{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ViewPatterns               #-}

module Syntax where

import qualified Bound                as B
import qualified Bound.Var            as B
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader
import           Data.Foldable        hiding (elem)
import qualified Data.Map             as Map
import           Data.Monoid
import qualified Data.Set             as Set
import           Data.Traversable
import           Prelude.Extras

data Binder
  = Pi
  | Sg
  deriving (Eq, Ord, Show, Read)

data Constant
  = Zero
  | One
  | Two
  | Dot
  | Tt
  | Ff
  | U
  | Refl
  deriving (Eq, Ord, Show, Read)

data Tm a
  = V a
  | Ann (Tm a) (Tm a)
  | C Constant
  | Pair (Tm a) (Tm a)
  | B Binder (Tm a) (B.Scope () Tm a)
  | Id (Tm a) (Tm a) (Tm a)
  | Reflect (Tm a) (Tm a)
  | Split (B.Scope Bool Tm a) (Tm a)
  | Lam (B.Scope () Tm a)
  | Let (Tm a, Tm a) (B.Scope () Tm a)
  | Tm a :@ Tm a
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

type Type a = Tm a
data Decl a = Decl a (Type a) (Tm a)

instance Eq1 Tm
instance Ord1 Tm
instance Show1 Tm
instance Read1 Tm
instance Applicative Tm where pure = V; (<*>) = ap

instance Monad Tm where
  return = V
  V a >>= f = f a
  C a >>= f = C a
  Ann u t >>= f = Ann (u >>= f) (t >>= f)
  Pair a b >>= f = Pair (a >>= f) (b >>= f)
  B bnd s t >>= f = B bnd (s >>= f) (t B.>>>= f)
  Id a b s >>= f = Id (a >>= f) (b >>= f) (s >>= f)
  Reflect p e >>= f = Reflect (p >>= f) (e >>= f)
  Let (s, sty) e >>= f = Let (s >>= f, sty >>= f) (e B.>>>= f)
  Lam e >>= f = Lam (e B.>>>= f)
  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Split e p >>= f = Split (e B.>>>= f) (p >>= f)

abstract2 :: (Monad f, Eq a) => (a,a) -> f a -> B.Scope Bool f a
abstract2 (x,y) =
  B.abstract $ \z ->
    if x == z
      then Just True
    else if y == z
      then Just False
    else Nothing

instantiate2 :: Monad f => (f a, f a) -> B.Scope Bool f a -> f a
instantiate2 (a,b) =
  B.instantiate $ \z ->
    if z
      then a
      else b

u // x = B.instantiate1 x u
x \\ u = B.abstract1 x u

u /// (x,y) = instantiate2 (x,y) u
(x,y) \\\ u = abstract2 (x,y) u

