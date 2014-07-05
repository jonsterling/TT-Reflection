{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Typing ( infer
              , check
              , Checking(..)
              , Ty(..)
              , Realizer(..)
              , Context
              , extractRealizer
              , checkDecls
              ) where

import qualified Context              as Ctx
import           Syntax               hiding (Decl, Tm, Ty)
import qualified Syntax               as Syn

import qualified Data.Map             as Map
import qualified Data.Set             as Set

import qualified Bound                as B

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader
import           Data.Monoid
import           Data.Traversable
import Debug.Trace

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
extendCtx x xty = local $ Ctx.appendTyping (x, xty)

extendSignature :: Name -> (Ty, Tm) -> Checking a -> Checking a
extendSignature x (a,s) = local $ Ctx.appendDecl (x, a, s)

addEquation :: (Tm,Tm) -> Checking a -> Checking a
addEquation (a,b) c = do
  a' <- whnf a >>= unref
  b' <- whnf b >>= unref
  flip local c $
    Ctx.appendEquation (a', b')

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
  Set.member (a', b') <$> asks Ctx.equations

-- This is a very inefficient type checker! It computes the whnf of terms
-- over and over again. It would be a good idea to fix that.
--
infer' :: Tm -> Checking Ty
infer' (V x) = lookupTy x <|> fst <$> lookupDecl x
infer' (C t) | t  `elem` [U, Zero, One, Two] = return $ C U
infer' (C Dot) = return $ C One
infer' (C x) | x `elem` [Tt, Ff] = return $ C Two
infer' (B _ sg tau) = do
  _ <- check sg $ C U
  _ <- extendCtx "x" sg $ check (tau // V "x") $ C U
  return $ C U
infer' (Id s a b) = do
  (s', _) <- check s $ C U
  _ <- check a s'
  _ <- check b s'
  return $ C U
infer' (BoolElim c m n b) = do
  (c', _) <- extendCtx "x" (C Two) $ check (c // V "x") $ C U
  _ <- check m (c // C Tt)
  _ <- check n (c // C Ff)
  (b', _) <- check b (C Two)
  return $ ("x" \\ c') // b'
infer' (Spread c e p) = do
  ty <- infer p
  (s, t) <- ensureSg ty
  (c', _) <- extendCtx "u" ty $ check (c // V "u") (C U)
  (e', _) <- extendCtx "v" s
             . extendCtx "w" (t // V "v")
             $ check (e /// (V "v", V "w")) (c // (Pair (V "v") (V "w")))
  return $ c // p
infer' (Proj True p) = do
  ty <- infer p
  (s, t) <- ensureSg ty
  return s
infer' (Proj False p) = do
  ty <- infer p
  (s, t) <- ensureSg ty
  whnf $ t // Proj True p
infer' (f :@ x) = do
  ty <- infer f
  (s, t)  <- ensurePi ty
  (x', _) <- check x s
  return $ t // x'
infer' (Funext f g h) = do
  ty <- infer f
  (s, t) <- ensurePi ty
  _ <- check g ty
  extendCtx "x" s $ do
    let x = V "x"
    (h', _) <- check (h // x) $ Id (t // x) (f :@ x) (g :@ x)
    return $ Id (B Pi s t) f g
infer' (PairEq m n p q) = do
  ty <- infer m
  (s, t) <- ensureSg ty
  (n', _) <- check n ty
  (p', _) <- check p $ Id s (Proj True m) (Proj True n)
  (q', _) <- addEquation (Proj True m, Proj True n) $ check q $ Id (t // Proj True m) (Proj False m) (Proj False n)
  return $ Id ty m n
infer' (BinderEq a@(B Pi s t) b@(B Pi s' t') p q) = do
  (a', _) <- check a (C U)
  (b', _) <- check b (C U)
  (p', _) <- check p (Id (C U) s s')
  (q', _) <- addEquation (s, s') $ check (q // V "x") $ Id (C U) (t // V "x") (t' // V "x")
  return $ Id (C U) a' b'
infer' e = err $ "Cannot infer type of " ++ show e

check' :: Tm -> Ty -> Checking (Tm, Ty)
check' (V x) ty = do
  ty' <- lookupTy x <|> fst <$> lookupDecl x
  equate (C U) ty ty'
  return (V x, ty)
check' (Reflect p e) rho = do
  t <- infer p
  (s, a, b) <- ensureIdentity t
  (rho', _) <- addEquation (a,b) $ check rho $ C U
  (e', _)   <- addEquation (a,b) $ check e rho'
  return (Reflect p e', rho)
check' (C Dot) (Id s a b) = do
  (s', _) <- check s $ C U
  (a', _) <- check a s'
  (b', _) <- check b s'
  equate s a' b'
  return (C Dot, Id s' a' b')
check' (Pair a b) (B Sg sg tau) = do
  (a', _) <- check a sg
  (b', _) <- check b $ tau // a'
  return (Pair a' b', B Sg sg tau)
check' (Lam e) (B Pi sg tau) = do
  (e', _) <- extendCtx "x" sg $ check (e // V "x") $ tau // V "x"
  return (Lam ("x" \\ e'), B Pi sg tau)
check' (PairEq m n p q) (Id a m' n') = do
  (s, t) <- ensureSg a
  _ <- check m a
  _ <- check n a
  equate a m m'
  equate a n n'
  (p', _) <- check p $ Id s (Proj True m) (Proj True n)
  (q', _) <- addEquation (Proj True m, Proj True n) $ check q $ Id (t // Proj True m) (Proj False m) (Proj False n)
  return $ (PairEq m n p q, Id a m n)
check' t ty = do
  tty <- infer t
  equate (C U) ty tty
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
    extract (Pair a b) = Pair (extract a) (extract b)
    extract (B b s t) = B b (extract s) $ "x" \\ extract (t // V "x")
    extract (Id s a b) = Id (extract s) (extract a) (extract b)
    extract (Reflect p e) = extract e
    extract (Spread c e p) = Spread ("x" \\ extract (c // V "x")) (("x","y") \\\ (extract (e /// (V "x", V "y")))) (extract p)
    extract (Proj b p) = Proj b (extract p)
    extract (BoolElim c m n b) = BoolElim ("x" \\ (extract (c // V "x"))) (extract m) (extract n) (extract b)
    extract (Lam e) = Lam ("x" \\ extract (e // V "x"))
    extract (Let a e) = extract (e // a)
    extract (f :@ a) = extract f :@ extract a
    extract (BinderEq a b p q) = C Dot
    extract (Funext f g h) = C Dot
    extract (PairEq m n p q) = C Dot
    extract e = e

ensureIdentity :: Ty -> Checking (Ty, Tm, Tm)
ensureIdentity ty = do
  ty' <- whnf ty
  case ty' of
    Id s a b -> return (s, a, b)
    _ -> err "Expected identity type"

ensurePi :: Ty -> Checking (Ty, B.Scope () Syn.Tm Name)
ensurePi (B Pi s t) = return (s, t)
ensurePi _ = err "Expected pi type"

ensureSg :: Ty -> Checking (Ty, B.Scope () Syn.Tm Name)
ensureSg (B Sg s t) = return (s, t)
ensureSg _ = err "Expected sigma type"

assert :: Bool -> String -> Checking ()
assert p = unless p . err


equate :: Ty -> Tm -> Tm -> Checking ()
equate a m n = do
  a' <- whnf a >>= unref
  structuralEq m n <|> trivialExtensionalEq a m n <|> reflectEquality m n

trivialExtensionalEq :: Ty -> Tm -> Tm -> Checking ()
trivialExtensionalEq a m n = () <$ (extensionalEq a m n >>= check (C Dot))

reflectEquality :: Tm -> Tm -> Checking ()
reflectEquality e1 e2 = do
  e1' <- whnf e1 >>= unref
  e2' <- whnf e2 >>= unref
  unless (e1' == e2') $ do
    reflected <- lookupEquation (e1', e2') <|> lookupEquation (e2', e1')
    eqs <- asks Ctx.equations
    unless reflected $
      err $ "Not equal: " ++ show e1 ++ "            and             " ++ show e2

extensionalEq :: Ty -> Tm -> Tm -> Checking Ty
extensionalEq a m n = do
  (m', _) <- check m a
  (n', _) <- check n a
  a' <- whnf a >>= unref
  extensionalEq' a' m' n'

structuralEq :: Tm -> Tm -> Checking ()
structuralEq m n = do
  m' <- whnf m >>= unref
  n' <- whnf n >>= unref
  structuralEq' m' n'

structuralEq' :: Tm -> Tm -> Checking ()
structuralEq' (C c) (C c') =
  assert (c == c') "Constants are not equal"
structuralEq' (V x) (V x') =
  assert (x == x') "Variables are not equal"
structuralEq' (f :@ x) (g :@ y) = do
  structuralEq f g
  structuralEq x y
structuralEq' e e' =
  assert (e == e') "Terms not structurally equal"

extensionalEq' :: Ty -> Tm -> Tm -> Checking Ty
extensionalEq' (C One) m n =
  return $ C One
extensionalEq' (B Sg s t) m n = do
  fst <- extensionalEq s (Proj True m) (Proj True n)
  snd <- extensionalEq (t // Proj True m) (Proj False m) (Proj False n)
  return $ B Sg fst ("x" \\ snd)
extensionalEq' (B Pi s t) f g = do
  h <- extendCtx "x" s $ extensionalEq (t // V "x") (f :@ V "x") (g :@ V "x")
  return $ B Pi s ("x" \\ h)
extensionalEq' (Id a m n) p q =
  return $ C One
extensionalEq' a m n =
  err $ "extensionalEq' applied to non-type " ++ show a


unref :: Tm -> Checking Tm
unref (V x) = do
  sig <- asks Ctx.signature
  case Map.lookup x sig of
    Just (_, tm) -> unref tm
    Nothing -> return $ V x
unref e = return e

whnf :: Tm -> Checking Tm
whnf (Let s e) =
  whnf $ e // s
whnf (f :@ a) = do
  f' <- whnf f >>= unref
  a' <- whnf a
  case f' of
    Lam e -> whnf $ e // a'
    _ -> return $ f' :@ a'
whnf (Spread c e p) = do
  p' <- whnf p >>= unref
  case p' of
    Pair a b -> whnf $ e /// (a,b)
    _ -> return $ Spread c e p'
whnf (Proj True p) = do
  p' <- whnf p >>= unref
  case p' of
    Pair a b -> whnf a
    _ -> return $ Proj True p'
whnf (Proj False p) = do
  p' <- whnf p >>= unref
  case p' of
    Pair a b -> whnf b
    _ -> return $ Proj False p'
whnf (BoolElim c m n b) = do
  c' <- (\\) "x" <$> whnf (c // V "x")
  b' <- whnf b
  m' <- whnf m
  n' <- whnf n
  case b' of
    C Tt -> return m'
    C Ff -> return n'
    _ -> return $ BoolElim c' m' n' b'
whnf e = return e

