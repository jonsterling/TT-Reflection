{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UnicodeSyntax              #-}

module Typing ( infer
              , check
              , Checking(..)
              , Typing(..)
              , Realization(..)
              , extractRealizer
              , checkDecls
              ) where

import qualified Context              as Ctx
import           Syntax               hiding (Tm)
import qualified Syntax               as Syn

import qualified Data.Map             as Map
import qualified Data.Set             as Set

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader
import           Data.Monoid
import           Data.Traversable

import Debug.Trace

type Name = String
type Tm = Syn.Tm Name

type Context = Ctx.Context Name Syn.Tm
newtype Checking x =
  MkChecking
  { runChecking :: ReaderT Context (Either String) x
  } deriving (Monad, Applicative, Functor, MonadReader Context, Alternative)

data Typing = Tm :∈ Tm
data Realization = Tm :||- Tm

instance Show Typing where
  show (tm :∈ ty) = show tm ++ " ∈ " ++ show ty
instance Show Realization where
  show (tm :||- ty) = show tm ++ " ╟ " ++ show ty

err :: String -> Checking x
err e = MkChecking $ ReaderT $ \_ -> Left e

infer :: Tm -> Checking Tm
infer e = infer' =<< whnf e

check :: Tm -> Tm -> Checking Typing
check ty t = do
  ty' <- whnf ty
  t' <- whnf t
  check' ty' t'

extendCtx :: Name -> Tm -> Checking a -> Checking a
extendCtx x xty =
  local $ \ctx ->
    ctx { Ctx.typings = Map.insert x xty (Ctx.typings ctx) }

extendSignature :: Name -> (Tm, Tm) -> Checking a -> Checking a
extendSignature x p =
  local $ \ctx ->
    ctx { Ctx.signature = Map.insert x p (Ctx.signature ctx) }

addEquation :: (Tm,Tm) -> Checking a -> Checking a
addEquation (a,b) c = do
  a' <- whnf a
  b' <- whnf b
  local (\ctx -> ctx { Ctx.equations = Set.insert (a', b') (Ctx.equations ctx) }) c

lookupTy :: Name -> Checking Tm
lookupTy x = do
  mty <- fmap (Map.lookup x) (asks Ctx.typings)
  case mty of
    Just ty -> return ty
    Nothing -> err $ "No such variable " ++ show x ++ "in context"

lookupDecl :: Name -> Checking (Tm, Tm)
lookupDecl x = do
  mty <- fmap (Map.lookup x) (asks Ctx.signature)
  case mty of
    Just ty -> return ty
    Nothing -> err $ "No such declaration " ++ show x ++ "in signature"

lookupEquation :: (Tm, Tm) -> Checking Bool
lookupEquation (a, b) = do
  a' <- whnf a
  b' <- whnf b
  fmap (Set.member (a, b)) (asks Ctx.equations)

-- This is a very inefficient type checker! It computes the whnf of terms
-- over and over again. It would be a good idea to fix that.
--
infer' :: Tm -> Checking Tm
infer' (V x) = lookupTy x <|> fst <$> (lookupDecl x)
infer' (Ann a s) = do
  s' :∈ _ <- check (C U) s
  a' :∈ _ <- check s' a
  return s'
infer' (C t) | t  `elem` [U, Zero, One, Two] = return $ C U
infer' (C Dot) = return $ C One
infer' (C x) | x `elem` [Tt, Ff] = return $ C Two
infer' (B _ sg tau) = do
  _ <- check (C U) sg
  _ <- extendCtx "x" sg $ check (C U) (tau // V "x")
  return $ C U
infer' (Id a b s) = do
  s' :∈ _ <- check (C U) s
  _ <- check s' a
  _ <- check s' b
  return $ C U
infer' e = err $ "Cannot infer type of " ++ show e

check' :: Tm -> Tm -> Checking Typing
check' ty (V x) = do
  ty' <- lookupTy x <|> fst <$> (lookupDecl x)
  equate ty ty'
  return $ V x :∈  ty
check' rho (Reflect p e) = do
  t <- infer p
  (a,b,s) <- ensureIdentity t
  e' :∈ _ <- addEquation (a,b) $ check rho e
  return $ Reflect p e' :∈  rho
check' (Id a b s) (C Refl) = do
  s' :∈ _ <- check (C U) s
  a' :∈ _ <- check s' a
  b' :∈ _ <- check s' b
  equate a' b'
  return $ C Refl :∈ Id a' b' s'
check' (B Pi sg tau) (Lam e) = do
  e' :∈  _ <- extendCtx "x" sg $ check (tau // V "x") (e // V "x")
  return $ Lam ("x" \\ e') :∈ B Pi sg tau
check' ty t = do
  tty <- infer t
  equate ty tty
  return $ t :∈ tty

checkDecls :: [Decl Name] -> Checking [(Name, Typing)]
checkDecls [] = return []
checkDecls (Decl n ty tm : ds) = do
  c <- check ty tm
  cs <- extendSignature n (ty, tm) $ checkDecls ds
  return $ (n, c) : cs

extractRealizer :: Typing -> Realization
extractRealizer (u :∈ s) = extract u :||- s
  where
    extract (Ann a t) = extract a
    extract (Pair a b) = Pair (extract a) (extract b)
    extract (B b s t) = B b (extract s) ("x" \\ extract (t // V "x"))
    extract (Id a b s) = Id (extract a) (extract b) (extract s)
    extract (Reflect p e) = extract e
    extract (Split e p) = Split (abstract2 ("x","y") (extract (instantiate2 (V "x", V "y") e))) (extract p)
    extract (Lam e) = Lam ("x" \\ extract (e // V "x"))
    extract (Let (a,s) e) = Let (extract a, extract s) ("x" \\ extract (e // V "x"))
    extract (f :@ a) = extract f :@ extract a
    extract e = e

ensureIdentity :: Tm -> Checking (Tm, Tm, Tm)
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
whnf (Let (s, _) e) = whnf $ e // s
whnf (Reflect p e) = Reflect <$> (whnf p) <*> (whnf e)
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


