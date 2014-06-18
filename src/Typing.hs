{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Typing ( infer
              , check
              , Checking(..)
              , Ty(..)
              , Realizer(..)
              , extractRealizer
              , checkDecls
              ) where

import qualified Context              as Ctx
import           Syntax               hiding (Tm, Ty, Decl)
import qualified Syntax               as Syn

import qualified Data.Map             as Map
import qualified Data.Set             as Set

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader
import           Data.Monoid
import           Data.Traversable

type Name = String
type Tm = Syn.Tm Name
type Ty = Syn.Ty Name
type Decl = Syn.Decl Name

type Context = Ctx.Context Name Syn.Tm Syn.Tm

newtype Checking x =
  MkChecking
  { runChecking :: ReaderT Context (Either String) x
  } deriving (Monad, Applicative, Functor, MonadReader Context, Alternative)

newtype Realizer = Realizer { unrealize :: Tm }

err :: String -> Checking x
err e = MkChecking $ ReaderT $ \_ -> Left e

infer :: Tm -> Checking Ty
infer e = infer' =<< whnf e

check :: Tm -> Ty -> Checking (Tm, Ty)
check t ty = do
  ty' <- whnf ty
  t' <- whnf t
  check' t' ty'

extendCtx :: Name -> Ty -> Checking a -> Checking a
extendCtx x xty =
  local $ \ctx ->
    ctx { Ctx.typings = Map.insert x xty (Ctx.typings ctx) }

extendSignature :: Name -> (Ty, Tm) -> Checking a -> Checking a
extendSignature x p =
  local $ \ctx ->
    ctx { Ctx.signature = Map.insert x p (Ctx.signature ctx) }

addEquation :: (Tm,Tm) -> Checking a -> Checking a
addEquation (a,b) c = do
  a' <- whnf a
  b' <- whnf b
  flip local c $ \ctx ->
    ctx { Ctx.equations = Set.insert (a', b') (Ctx.equations ctx) }

lookupTy :: Name -> Checking Ty
lookupTy x = do
  mty <- Map.lookup x <$> asks Ctx.typings
  case mty of
    Just ty -> return ty
    Nothing -> err $ "No such variable " ++ show x ++ "in context"

lookupDecl :: Name -> Checking (Ty, Tm)
lookupDecl x = do
  md <- Map.lookup x <$> asks Ctx.signature
  case md of
    Just d -> return d
    Nothing -> err $ "No such declaration " ++ show x ++ "in signature"

lookupEquation :: (Tm, Tm) -> Checking Bool
lookupEquation (a, b) = do
  a' <- whnf a
  b' <- whnf b
  Set.member (a, b) <$> asks Ctx.equations

-- This is a very inefficient type checker! It computes the whnf of terms
-- over and over again. It would be a good idea to fix that.
--
infer' :: Tm -> Checking Ty
infer' (V x) = lookupTy x <|> fst <$> (lookupDecl x)
infer' (Ann a s) = do
  (s', _) <- check s $ C U
  (a', _) <- check a s'
  return s'
infer' (C t) | t  `elem` [U, Zero, One, Two] = return $ C U
infer' (C Dot) = return $ C One
infer' (C x) | x `elem` [Tt, Ff] = return $ C Two
infer' (B _ sg tau) = do
  _ <- check sg $ C U
  _ <- extendCtx "x" sg $ check (tau // V "x") $ C U
  return $ C U
infer' (Id a b s) = do
  (s', _) <- check s $ C U
  _ <- check a s'
  _ <- check b s'
  return $ C U
infer' e = err $ "Cannot infer type of " ++ show e

check' :: Tm -> Ty -> Checking (Tm, Ty)
check' (V x) ty = do
  ty' <- lookupTy x <|> fst <$> (lookupDecl x)
  equate ty ty'
  return (V x, ty)
check' (Reflect p e) rho = do
  t <- infer p
  (a,b,s) <- ensureIdentity t
  (e', _) <- addEquation (a,b) $ check e rho
  return (Reflect p e', rho)
check' (C Refl) (Id a b s) = do
  (s', _) <- check s $ C U
  (a', _) <- check a s'
  (b', _) <- check b s'
  equate a' b'
  return (C Refl, Id a' b' s')
check' (Lam e) (B Pi sg tau) = do
  (e', _) <- extendCtx "x" sg $ check (e // V "x") $ tau // V "x"
  return (Lam ("x" \\ e'), B Pi sg tau)
check' t ty = do
  tty <- infer t
  equate ty tty
  return (t, tty)

checkDecls :: [Decl] -> Checking [Decl]
checkDecls [] = return []
checkDecls ((n, ty, tm) : ds) = do
  (a,s) <- check tm ty
  cs <- extendSignature n (ty, tm) $ checkDecls ds
  return $ (n,s,a) : cs

extractRealizer :: Tm -> Realizer
extractRealizer = Realizer . extract
  where
    extract (Ann a t) = extract a
    extract (Pair a b) = Pair (extract a) (extract b)
    extract (B b s t) = B b (extract s) $ "x" \\ extract (t // V "x")
    extract (Id a b s) = Id (extract a) (extract b) (extract s)
    extract (Reflect p e) = extract e
    extract (Split e p) = Split (abstract2 ("x","y") (extract (instantiate2 (V "x", V "y") e))) (extract p)
    extract (Lam e) = Lam ("x" \\ extract (e // V "x"))
    extract (Let (a,s) e) = Let (extract a, extract s) ("x" \\ extract (e // V "x"))
    extract (f :@ a) = extract f :@ extract a
    extract e = e

ensureIdentity :: Ty -> Checking (Tm, Tm, Ty)
ensureIdentity ty = do
  ty' <- whnf ty
  case ty' of
    Id a b s -> return (a, b, s)
    _ -> err "Expected identity type"

equate :: Tm -> Tm -> Checking ()
equate e1 e2 =
  unless (e1 == e2) $ do
    reflected <- lookupEquation (e1,e2)
    unless reflected $
      err $ "Not equal: " ++ show e1 ++ ", " ++ show e2

whnf :: Tm -> Checking Tm
whnf (Let (s, _) e) =
  whnf $ e // s
whnf (Reflect p e) =
  Reflect <$> (whnf p) <*> (whnf e)
whnf (f :@ a) = do
  f' <- whnf f
  case f' of
    Lam e -> whnf $ e // a
    _     -> return $ f' :@ a
whnf d@(Split e p) = do
  p' <- whnf p
  case p' of
    Pair a b -> whnf $ e /// (a,b)
    _ -> return d
whnf (V x) = do
  rho <- asks Ctx.signature
  return $
    case Map.lookup x rho of
      Just (_, tm) -> tm
      Nothing -> V x
whnf e = return e

