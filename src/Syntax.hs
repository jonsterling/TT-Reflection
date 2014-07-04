{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
  deriving (Eq, Ord, Show, Read)

data Tm a
  = V a
  | Ann (Tm a) (Tm a)
  | C Constant
  | Pair (Tm a) (Tm a)
  | B Binder (Tm a) (B.Scope () Tm a)
  | Id (Tm a) (Tm a) (Tm a)
  | Reflect (Tm a) (Tm a)
  | Spread (B.Scope () Tm a) (B.Scope Bool Tm a) (Tm a)
  | Proj Bool (Tm a)
  | BoolElim (B.Scope () Tm a) (Tm a) (Tm a) (Tm a)
  | Lam (B.Scope () Tm a)
  | Let (Tm a) (B.Scope () Tm a)
  | Tm a :@ Tm a
  | BinderEq (Tm a) (Tm a) (Tm a) (B.Scope () Tm a)
  | Funext (Tm a) (Tm a) (B.Scope () Tm a)
  | UIP (Tm a) (Tm a)
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

type Ty a = Tm a
type Decl a = (a, Ty a, Tm a)

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
  Id s a b >>= f = Id (s >>= f) (a >>= f) (b >>= f)
  Reflect p e >>= f = Reflect (p >>= f) (e >>= f)
  Let s e >>= f = Let (s >>= f) (e B.>>>= f)
  Lam e >>= f = Lam (e B.>>>= f)
  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Spread c e p >>= f = Spread (c B.>>>= f) (e B.>>>= f) (p >>= f)
  Proj b p >>= f = Proj b (p >>= f)
  BoolElim c m n b >>= f = BoolElim (c B.>>>= f) (m >>= f) (n >>= f) (b >>= f)
  BinderEq a b p q >>= f = BinderEq (a >>= f) (b >>= f) (p >>= f) (q B.>>>= f)
  Funext m n h >>= f = Funext (m >>= f) (n >>= f) (h B.>>>= f)
  UIP p q >>= f = UIP (p >>= f) (q >>= f)

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

u /// vs = instantiate2 vs u
vs \\\ u = abstract2 vs u

