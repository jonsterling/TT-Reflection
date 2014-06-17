{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Main where

import           Compute
import qualified Context              as Ctx
import           Syntax
import           Typing
import           Parse

import           Control.Applicative
import           Control.Monad.Reader
import           Data.Monoid

import System.Console.Haskeline
import Text.Trifecta

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
main = runInputT defaultSettings loop
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
            Right tder -> do
              outputStrLn $ "Typing: " ++ show tder
              outputStrLn $ "Realizer: " ++ show (extractRealizer tder)
            Left err -> outputStrLn err
        _ -> outputStrLn "Parse error"

      outputStrLn "==========================\n"
      loop

runClosed c = runReaderT (runChecking c) mempty

realize c = extractRealizer <$> runClosed c
