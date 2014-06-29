{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}

module Context where

import qualified Data.Map    as Map
import qualified Data.Set    as Set

import           Data.Monoid

data Context n tm ty =
  (Ord n, Ord (tm n), Ord (ty n)) =>
  Context
  { typings   :: Map.Map n (ty n)
  , signature :: Map.Map n (ty n, tm n)
  , equations :: Set.Set (tm n, tm n)
  }

appendTyping :: Ord n => (n, ty n) -> Context n tm ty -> Context n tm ty
appendTyping (n, t) ctx = ctx { typings = Map.insert n t (typings ctx) }

appendDecl :: Ord n => (n, ty n, tm n) -> Context n tm ty -> Context n tm ty
appendDecl (n, ty, tm) ctx = ctx { signature = Map.insert n (ty, tm) (signature ctx) }

appendEquation :: Ord (tm n) => (tm n, tm n) -> Context n tm ty -> Context n tm ty
appendEquation (a, b) ctx = ctx { equations = Set.insert (a,b) (equations ctx) }

instance (Ord n, Ord (tm n), Ord (ty n)) => Monoid (Context n tm ty) where
  mempty = Context mempty mempty mempty
  mappend (Context gm sg ep) (Context gm' sg' ep') = Context (gm <> gm') (sg <> sg') (ep <> ep')

