{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE UnicodeSyntax              #-}

module Typing ( infer
              , check
              , Checking(..)
              , Type(..)
              , Realizer(..)
              , extractRealizer
              , checkDecls
              ) where

import qualified Context              as Ctx
import           Syntax               hiding (Tm, Type)
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
type Type = Syn.Type Name

type Context = Ctx.Context Name Syn.Tm Syn.Type
newtype Checking x =
  MkChecking
  { runChecking :: ReaderT Context (Either String) x
  } deriving (Monad, Applicative, Functor, MonadReader Context, Alternative)

newtype Realizer = Realizer { unrealize :: Tm }

err :: String -> Checking x
err e = MkChecking $ ReaderT $ \_ -> Left e

infer :: Tm -> Checking Type
infer e = infer' =<< whnf e

check :: Type -> Tm -> Checking (Tm, Type)
check (Syn.Type ty) t = do
  ty' <- whnf ty
  t' <- whnf t
  check' (Syn.Type ty') t'

extendCtx :: Name -> Type -> Checking a -> Checking a
extendCtx x xty =
  local $ \ctx ->
    ctx { Ctx.typings = Map.insert x xty (Ctx.typings ctx) }

extendSignature :: Name -> (Type, Tm) -> Checking a -> Checking a
extendSignature x p =
  local $ \ctx ->
    ctx { Ctx.signature = Map.insert x p (Ctx.signature ctx) }

addEquation :: (Tm,Tm) -> Checking a -> Checking a
addEquation (a,b) c = do
  a' <- whnf a
  b' <- whnf b
  flip local c $ \ctx ->
    ctx { Ctx.equations = Set.insert (a', b') (Ctx.equations ctx) }

lookupTy :: Name -> Checking Type
lookupTy x = do
  mty <- Map.lookup x <$> asks Ctx.typings
  case mty of
    Just ty -> return ty
    Nothing -> err $ "No such variable " ++ show x ++ "in context"

lookupDecl :: Name -> Checking (Type, Tm)
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
infer' :: Tm -> Checking Type
infer' (V x) = lookupTy x <|> fst <$> (lookupDecl x)
infer' (Ann a s) = do
  (s', _) <- check (Syn.Type (C U)) (untype s)
  (a', _) <- check (Syn.Type s') a
  return (Syn.Type s')
infer' (C t) | t  `elem` [U, Zero, One, Two] = return . Syn.Type $ C U
infer' (C Dot) = return . Syn.Type $ C One
infer' (C x) | x `elem` [Tt, Ff] = return . Syn.Type $ C Two
infer' (B _ sg tau) = do
  _ <- check (Syn.Type (C U)) (untype sg)
  _ <- extendCtx "x" sg $ check (Syn.Type $ C U) $ untype $ tau // Syn.Type (V "x")
  return . Syn.Type $ C U
infer' (Id a b s) = do
  (s', _) <- check (Syn.Type (C U)) (untype s)
  _ <- check (Syn.Type s') a
  _ <- check (Syn.Type s') b
  return . Syn.Type $ C U
infer' e = err $ "Cannot infer type of " ++ show e

check' :: Type -> Tm -> Checking (Tm, Type)
check' ty (V x) = do
  ty' <- lookupTy x <|> fst <$> (lookupDecl x)
  equate (untype ty) (untype ty')
  return (V x, ty)
check' rho (Reflect p e) = do
  t <- infer p
  (a,b,s) <- ensureIdentity t
  (e', _) <- addEquation (a,b) $ check rho e
  return (Reflect p e', rho)
check' (Syn.Type (Id a b s)) (C Refl) = do
  (s', _) <- check (Syn.Type (C U)) (untype s)
  (a', _) <- check (Syn.Type s') a
  (b', _) <- check (Syn.Type s') b
  equate a' b'
  return (C Refl, Syn.Type $ Id a' b' (Syn.Type s'))
check' (Syn.Type (B Pi sg tau)) (Lam e) = do
  (e', _) <- extendCtx "x" sg $ check (tau // Syn.Type (V "x")) (e // V "x")
  return (Lam ("x" \\ e'), Syn.Type $ B Pi sg tau)
check' ty t = do
  tty <- infer t
  equate (untype ty) (untype tty)
  return (t, tty)

checkDecls :: [Decl Name] -> Checking [(Name, Tm, Type)]
checkDecls [] = return []
checkDecls (Decl n ty tm : ds) = do
  (a,s) <- check ty tm
  cs <- extendSignature n (ty, tm) $ checkDecls ds
  return $ (n,a,s) : cs

extractRealizer :: Tm -> Realizer
extractRealizer = Realizer . extract
  where
    extract (Ann a t) = extract a
    extract (Pair a b) = Pair (extract a) (extract b)
    extract (B b s t) = B b (extractTy s) $ "x" \\ extractTy (t // Syn.Type (V "x"))
    extract (Id a b s) = Id (extract a) (extract b) (extractTy s)
    extract (Reflect p e) = extract e
    extract (Split e p) = Split (abstract2 ("x","y") (extract (instantiate2 (V "x", V "y") e))) (extract p)
    extract (Lam e) = Lam ("x" \\ extract (e // V "x"))
    extract (Let (a,s) e) = Let (extract a, extract s) ("x" \\ extract (e // V "x"))
    extract (f :@ a) = extract f :@ extract a
    extract e = e

    extractTy = Syn.Type . extract . Syn.untype


ensureIdentity :: Type -> Checking (Tm, Tm, Type)
ensureIdentity (Syn.Type ty) = do
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

