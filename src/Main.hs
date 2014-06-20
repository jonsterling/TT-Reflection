module Main where

import           CLI

main :: IO ()
main = runCLI

-- runClosed c = runReaderT (runChecking c) mempty
-- realize   c = extractRealizer <$> runClosed c
