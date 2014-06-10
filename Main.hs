{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveTraversable #-}

module Term where

import Syntax
import Compute
import qualified Context as Ctx
import Typing

import Control.Applicative
import Control.Monad.Reader
import Data.Monoid

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


