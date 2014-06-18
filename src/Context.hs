{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}

module Context where

import qualified Data.Map    as Map
import qualified Data.Set    as Set

import           Data.Monoid

data Context n f =
  (Ord n, Ord (f n)) =>
  Context
  { typings   :: Map.Map n (f n)
  , signature :: Map.Map n (f n, f n)
  , equations :: Set.Set (f n, f n)
  }

instance (Ord n, Ord (f n)) => Monoid (Context n f) where
  mempty = Context mempty mempty mempty
  mappend (Context gm sg ep) (Context gm' sg' ep') = Context (gm <> gm') (sg <> sg') (ep <> ep')

