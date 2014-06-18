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

instance (Ord n, Ord (tm n), Ord (ty n)) => Monoid (Context n tm ty) where
  mempty = Context mempty mempty mempty
  mappend (Context gm sg ep) (Context gm' sg' ep') = Context (gm <> gm') (sg <> sg') (ep <> ep')

