{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}

module CLI where

import           Parse
import           Pretty
import           Typing
import qualified Context as Ctx

import           Control.Applicative
import           Control.Monad
import qualified Control.Monad.Reader         as CM
import qualified Control.Lens                 as CL
import           Control.Lens.Operators
import qualified Data.Vinyl                   as DV
import qualified Data.Vinyl.TH                as DV
import qualified Data.Map                     as Map
import qualified Data.Monoid                  as DM
import qualified Numeric.Natural              as NN
import qualified Options.Applicative          as OA
import qualified Data.Singletons.TH           as DS
import qualified System.Console.Haskeline     as SCH
import qualified System.IO                    as SI
import qualified Text.PrettyPrint             as TPP
import qualified Text.PrettyPrint.ANSI.Leijen as TPPAL
import qualified Text.Trifecta                as TT

import           Data.Vinyl
  ( (<-:)
  , (<+>)
  , (=:) )

import           Data.Vinyl.TH
  ( Semantics((:~>)) )

data CheckArgsUni
  = CAPaths
  deriving (Eq, Ord, Show)

data REPLArgsUni
  = RAUnit
  deriving (Eq, Ord, Show)

data OptionsUni
  = OVerbosity
  deriving (Eq, Ord, Show)

data InvocationUni
  = ICommand
  | IOptions
  deriving (Eq, Ord, Show)

DS.genSingletons
  [ ''CheckArgsUni
  , ''REPLArgsUni
  , ''OptionsUni
  , ''InvocationUni
  ]

DV.makeUniverse' ''CheckArgsUni "CheckArgsElm"
DV.semantics     ''CheckArgsElm
   [ 'CAPaths :~> [t| [SI.FilePath] |]
   ]
type  CheckArgsExt =
  '[  CAPaths
   ]

DV.makeUniverse' ''REPLArgsUni "REPLArgsElm"
DV.semantics     ''REPLArgsElm
   [ 'RAUnit :~> ''()
   ]
type  REPLArgsExt =
  '[  RAUnit
   ]

DV.makeUniverse' ''OptionsUni "OptionsElm"
DV.semantics     ''OptionsElm
   [ 'OVerbosity :~> ''NN.Natural
   ]
type  OptionsExt =
  '[  OVerbosity
   ]

data Command
  = CCheck (DV.PlainRec CheckArgsElm CheckArgsExt)
  | CREPL  (DV.PlainRec  REPLArgsElm  REPLArgsExt)
CL.makePrisms ''Command

DV.makeUniverse' ''InvocationUni "InvocationElm"
DV.semantics     ''InvocationElm
   [ 'ICommand :~> ''Command
   , 'IOptions :~> [t| DV.PlainRec OptionsElm OptionsExt |]
   ]
type  InvocationExt =
  '[  ICommand
   ,  IOptions
   ]

version = "0.1.0.0" -- FIXME: put this somewhere better

visibleHelper :: OA.Parser (a -> a)
visibleHelper = OA.abortOption OA.ShowHelpText . DM.mconcat $
        [ OA.long  "help"
        , OA.short 'h'
        , OA.help  "Show this help text"
        ]

parseCheckArgs :: OA.Parser (DV.PlainRec CheckArgsElm CheckArgsExt)
parseCheckArgs = fmap DV.cast . DV.rdist $
      SCAPaths <-: (many . OA.argument Just . DM.mconcat)
        [ OA.metavar "FILE"
        ]

parseREPLArgs :: OA.Parser (DV.PlainRec REPLArgsElm REPLArgsExt)
parseREPLArgs = fmap DV.cast . DV.rdist $
      SRAUnit =: ()

parseOptions :: OA.Parser (DV.PlainRec OptionsElm OptionsExt)
parseOptions = DV.rdist $
      SOVerbosity <-: (OA.option . DM.mconcat)
        [ OA.value   0
        , OA.short   'v'
        , OA.long    "verbose"
        , OA.metavar "LEVEL"
        , OA.help    "set verbosity to LEVEL"
        ]

parseCommand :: OA.Parser Command
parseCommand = OA.hsubparser . DM.mconcat $
        [ OA.command "check"
           . OA.info (CCheck <$> parseCheckArgs)
           . OA.progDesc
           $ "check theory files"
        , OA.command "repl"
           . OA.info (CREPL <$>  parseREPLArgs)
           . OA.progDesc
           $ "start the READ-EVAL-PRINT loop"
        ]

parseVersion :: OA.Parser (a -> a)
parseVersion = OA.infoOption version . DM.mconcat $
        [ OA.long "version"
        , OA.help "print version info"
        ]

parseInvocation :: OA.Parser (DV.PlainRec InvocationElm InvocationExt)
parseInvocation = DV.rdist $
      SICommand <-: parseCommand
  <+> SIOptions <-: parseOptions

infoInvocation :: OA.ParserInfo (DV.PlainRec InvocationElm InvocationExt)
infoInvocation = OA.info parser . DM.mconcat $
        [ OA.header   "TT-Reflection"
        , OA.fullDesc
        ]
  where
    parser = visibleHelper <*> parseVersion <*> parseInvocation

dispatchCheck :: DV.PlainRec CheckArgsElm CheckArgsExt -> IO ()
dispatchCheck
  = CL.perform
  $ DV.rLens SCAPaths
  . CL.act (mapM_ processPath)
  where
    processPath :: SI.FilePath -> IO ()
    processPath path = do
      putStrLn $ "Checking: " ++ path
      Just res <- TT.parseFromFile (many parseDecl) path
      case CM.runReaderT (runChecking (checkDecls res)) DM.mempty of
        Right artifacts ->
          putStrLn . TPP.renderStyle TPP.style . TPP.vcat $
            runFresh . pretty <$> artifacts
        Left err -> print err
      putStrLn ""

dispatchREPL :: DV.PlainRec REPLArgsElm REPLArgsExt -> IO ()
dispatchREPL
  = const
  . SCH.runInputT SCH.defaultSettings
  $ CM.runReaderT loop DM.mempty
  where
    loop :: CM.ReaderT Context (SCH.InputT IO) ()
    loop = do
      gamma <- CM.ask
      let barWidth = 80
      let dname = '_' ++ show (Map.size . Ctx.signature $ gamma)
      let next f = do CM.lift . SCH.outputStrLn $ replicate barWidth '=' ++ "\n"
                      CM.local f loop
      let parse = TT.parseString parseTm DM.mempty
      Just (parse -> rtm) <- CM.lift $ SCH.getInputLine "⊢ "
      Just (parse -> rty) <- CM.lift $ SCH.getInputLine "∈ "

      CM.lift . SCH.outputStrLn $ replicate barWidth '-'

      case (rtm, rty) of
        (TT.Success tm, TT.Success ty) -> do
          case CM.runReaderT (runChecking (check tm ty)) gamma of
            Right tder@(u, s) -> do
              let Realizer realizer = extractRealizer u
              let decl = (dname, s, u)
              CM.lift . SCH.outputStrLn . concat $
                [ "Typing: "
                , TPP.renderStyle TPP.style . runFresh . pretty $ decl
                ]
              next $ Ctx.appendDecl decl
            Left err -> do
              CM.lift $ SCH.outputStrLn err
              next id
        results -> do
          let errors = TPPAL.vsep $ results ^.. CL.both . TT._Failure
          CM.lift . SCH.outputStrLn . flip TPPAL.displayS "" $ TPPAL.renderPretty 0.4 200 errors
          next id

dispatchCommand :: Command -> IO ()
dispatchCommand
  = const mzero
  & CL.outside _CCheck .~ dispatchCheck
  & CL.outside _CREPL  .~ dispatchREPL

dispatchInvocation :: DV.PlainRec InvocationElm InvocationExt -> IO ()
dispatchInvocation
  = CL.perform
  $ DV.rLens SICommand
  . CL.act dispatchCommand

runCLI :: IO ()
runCLI = dispatchInvocation <=< OA.execParser $ infoInvocation
