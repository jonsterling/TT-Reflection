module Compute where

import           Syntax

whnf :: Tm a -> Tm a
whnf (Let (s, _) e) = whnf $ e // s
whnf (Reflect p e) = Reflect (whnf p) (whnf e)
whnf (f :@ a) = case whnf f of
  Lam e -> whnf $ e // a
  f'    -> f' :@ a
whnf d@(Split e p) = case whnf p of
  Pair a b -> whnf $ e /// (a,b)
  p' -> d
whnf e = e

