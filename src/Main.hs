{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Main where

import qualified Context                  as Ctx
import           Parse
import           Pretty
import           Syntax
import           Typing

import           Control.Applicative
import           Control.Monad.Reader
import           Data.Either
import           Data.Monoid

import           System.Console.Haskeline
import           System.Environment

import qualified Text.PrettyPrint         as PP
import           Text.Trifecta

main :: IO ()
main = do
  name:_ <- getArgs
  Just res <- parseFromFile (many parseDecl) name
  case runReaderT (runChecking (checkDecls res)) mempty of
    Right artifacts ->
      putStrLn . PP.renderStyle PP.style . PP.vcat $
        (runFresh . pretty) <$> artifacts
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
          let chk = check tm ty
          case runReaderT (runChecking chk) mempty of
            Right tder@(u, s) -> do
              let Realizer realizer = extractRealizer u
              outputStrLn $ "Typing: " ++ PP.renderStyle PP.style (runFresh (pretty ("_",s,u)))
            Left err -> outputStrLn err
        _ -> outputStrLn "Parse error"

      outputStrLn "==========================\n"
      loop

runClosed c = runReaderT (runChecking c) mempty

realize c = extractRealizer <$> runClosed c
