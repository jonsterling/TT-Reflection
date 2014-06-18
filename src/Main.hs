{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Main where

import qualified Context              as Ctx
import           Syntax
import           Typing
import           Parse
import           Pretty

import           Control.Applicative
import           Control.Monad.Reader
import           Data.Monoid
import           Data.Either

import System.Console.Haskeline
import System.Environment

import Text.Trifecta
import qualified Text.PrettyPrint as PP

-- Examples
--
identityTyping = check identityTy identity
  where
    identity = Lam $ "s" \\ (Lam $ "x" \\ V "x")
    identityTy = B Pi (C U) $ "s" \\ B Pi (V "s") ("x" \\ V "s")

testReflection = check ty tm
  where
    idTy = Id (C Zero) (C One) (C U)
    ty = B Pi idTy $ "p" \\ C Zero
    tm = Lam $ "p" \\ Reflect (V "p") (C Dot)

main :: IO ()
main = do
  name:_ <- getArgs
  Just res <- parseFromFile (many parseDecl) name
  case runReaderT (runChecking (checkDecls res)) mempty of
    Right artifacts -> do
      putStrLn . PP.renderStyle PP.style . PP.vcat $
        map prettyNamedTyping artifacts
    Left err -> print err

repl :: IO ()
repl = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
      Just tmStr <- getInputLine "⊢ "
      Just tyStr <- getInputLine "∈ "

      let rtm = parseString parseTm mempty tmStr
      let rty = parseString parseTm mempty tyStr

      outputStrLn "--------------------------"

      case (rtm, rty) of
        (Success tm, Success ty) -> do
          let chk = check ty tm
          case runReaderT (runChecking chk) mempty of
            Right tder@(u :∈ s) -> do
              let Realizer realizer = extractRealizer u
              outputStrLn $ "Typing: " ++ PP.renderStyle PP.style (prettyTyping tder)
              outputStrLn $ "Realizer: " ++ PP.renderStyle PP.style (pretty 0 realizer)
            Left err -> outputStrLn err
        _ -> outputStrLn "Parse error"

      outputStrLn "==========================\n"
      loop

runClosed c = runReaderT (runChecking c) mempty

realize c = extractRealizer <$> runClosed c
