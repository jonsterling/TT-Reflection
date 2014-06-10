{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Term where

import           Compute
import qualified Context              as Ctx
import           Syntax
import           Typing

import           Control.Applicative
import           Control.Monad.Reader
import           Data.Monoid

-- Examples
--
identityTyping = check identityTy identity
  where
    identity = Lam $ "s" \\ (Lam $ "x" \\ V "x")
    identityTy = B Pi (C U) $ "s" \\ (B Pi (V "s") $ "x" \\ V "s")

testReflection = check ty tm
  where
    idTy = Id (C Zero) (C One) (C U)
    ty = B Pi idTy $ "p" \\ C Zero
    tm = Lam $ "p" \\ (Reflect (V "p") $ C Dot)

runClosed c = runReaderT (runChecking c) mempty


