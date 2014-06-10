{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Typing ( infer
              , check
              , Checking(..)
              ) where

import           Compute
import qualified Context              as Ctx
import           Syntax               hiding (Tm)
import qualified Syntax               as Syn

import qualified Data.Map             as Map
import qualified Data.Set             as Set

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader
import           Data.Monoid

type Name = String
type Tm = Syn.Tm Name

type Context = Ctx.Context Name Syn.Tm
newtype Checking x =
  MkChecking
  { runChecking :: ReaderT Context (Either String) x
  } deriving (Monad, Applicative, Functor, MonadReader Context)

err :: String -> Checking x
err e = MkChecking $ ReaderT $ \_ -> Left e

infer :: Tm -> Checking Tm
infer e = infer' (whnf e)

check :: Tm -> Tm -> Checking Tm
check ty t = check' (whnf ty) (whnf t)

extendCtx :: Name -> Tm -> Checking a -> Checking a
extendCtx x xty =
  local $ \ctx ->
    ctx { Ctx.typings = Map.insert x xty (Ctx.typings ctx) }

addEquation :: (Tm,Tm) -> Checking a -> Checking a
addEquation (a,b) =
  local $ \ctx ->
    ctx { Ctx.equations = Set.insert (whnf a, whnf b) (Ctx.equations ctx) }

lookupTy :: Name -> Checking Tm
lookupTy x = do
  mty <- fmap (Map.lookup x) (asks Ctx.typings)
  case mty of
    Just ty -> return ty
    Nothing -> err $ "No such variable " ++ show x ++ "in context"

lookupEquation :: (Tm, Tm) -> Checking Bool
lookupEquation (a, b) =
  fmap (Set.member (whnf a, whnf b)) (asks Ctx.equations)

-- This is a very inefficient type checker! It computes the whnf of terms
-- over and over again. It would be a good idea to fix that.
--
infer' :: Tm -> Checking Tm
infer' (V x) = lookupTy x
infer' (Ann a s) = do
  s' <- check (C U) s
  a' <- check s' a
  return $ s'
infer' (C t) | elem t [U, Zero, One, Two] = return $ C U
infer' (C Dot) = return $ C One
infer' (C x) | elem x [Tt, Ff] = return $ C Two
infer' (B _ sg tau) = do
  _ <- check (C U) sg
  _ <- extendCtx "x" sg $ check (C U) (tau // V "x")
  return $ C U
infer' (Id a b s) = do
  s' <- check (C U) s
  _ <- check s' a
  _ <- check s' b
  return $ C U
infer' e = err $ "Cannot infer type of " ++ show e

check' :: Tm -> Tm -> Checking Tm
check' ty (V x) = do
  ty' <- lookupTy x
  equate ty ty'
  return $ V x
check' rho (Reflect p e) = do
  t <- infer p
  (a,b,s) <- ensureIdentity t
  Reflect p <$> (addEquation (a,b) $ check rho e)
check' (Id a b s) r@(C Refl) = do
  s' <- check (C U) s
  a' <- check s' a
  b' <- check s' b
  equate a' b'
  return $ r
check' (B Pi sg tau) (Lam e) = do
  e' <- extendCtx "x" sg $ check (tau // V "x") (e // V "x")
  return $ Lam ("x" \\ e')
check' ty t = do
  tty <- infer t
  equate ty tty
  return t

ensureIdentity :: Tm -> Checking (Tm, Tm, Tm)
ensureIdentity ty = do
  case whnf ty of
    Id a b s -> return (a, b, s)
    _ -> err $ "Expected identity type"

equate :: Tm -> Tm -> Checking ()
equate e1 e2 =
  unless (e1 == e2) $ do
    reflected <- lookupEquation (e1,e2)
    unless reflected $
      err $ "Not equal: " ++ show e1 ++ ", " ++ show e2

