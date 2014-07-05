{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Pretty ( Pretty(..)
              , Fresh
              , runFresh
              ) where

import qualified Bound                as B
import           Syntax
import           Text.PrettyPrint
import           Typing               hiding (Tm, Type)

import           Control.Applicative
import           Control.Monad.Reader
import qualified Data.Char            as C
import qualified Data.Digits          as D

newtype Fresh a = Fresh { runFreshWith :: Int -> a }
  deriving (Applicative, Functor, Monad, MonadReader Int)

runFresh :: Fresh a -> a
runFresh = flip runFreshWith (-1)

scope :: Fresh a -> Fresh a
scope = local succ

var :: Fresh String
var = asks $ map (C.chr . (+ 97)) . digits
  where
    digits 0 = [0]
    digits i = D.digits 26 i

class Pretty a where
  pretty :: a -> Fresh Doc

instance Pretty Binder where
  pretty Pi = pure $ text "Π"
  pretty Sg = pure $ text "Σ"

instance Pretty Constant where
  pretty Zero = pure $ text "𝟘"
  pretty One  = pure $ text "𝟙"
  pretty Two  = pure $ text "𝟚"
  pretty U    = pure $ text "𝕌"
  pretty Tt   = pure $ text "tt"
  pretty Ff   = pure $ text "ff"
  pretty Dot  = pure $ text "♦"

instance Pretty (Tm String) where
  pretty (V a) = pretty a
  pretty (C c) = pretty c
  pretty (B b s e) = do
    b' <- pretty b
    s' <- pretty s
    scope $ do
      x  <- var
      e' <- pretty (e // V x)
      pure $ b' <> brackets (text x <> colon <> s') <+> e'
  pretty (Pair m n) = scope $ do
    m' <- pretty m
    n' <- pretty n
    pure $ text "⟨" <> m' <> comma <+> n' <> text "⟩"
  pretty (Lam e) = scope $ do
    x  <- var
    e' <- pretty $ e // V x
    pure $ text "λ" <> brackets (text x) <+> e'
  pretty (Let s e) = do
    s' <- pretty s
    scope $ do
      x <- var
      e' <- pretty (e // V x)
      pure $ text "let" <+> text x <+> text "=" <+> s' <+> text "in" <+> e'
  pretty (Reflect a b) = do
    a' <- pretty a
    b' <- pretty b
    pure $ text "reflect" <+> a' <+> text "in" <+> b'
  pretty (Id s a b) = do
    s' <- pretty s
    a' <- pretty a
    b' <- pretty b
    pure $ text "Id" <> parens (s' <> semi <+> a' <> semi <+> b')
  pretty (BinderEq a b p q) = do
    a' <- pretty a
    b' <- pretty b
    p' <- pretty p
    scope $ do
      x  <- var
      q' <- pretty $ q // V x
      pure $ text "binderEq" <> parens (a' <> semi <+> b' <> semi <+> p' <> semi <+> brackets (text x) <+> q')
  pretty (Funext f g h) = do
    f' <- pretty f
    g' <- pretty g
    scope $ do
      x <- var
      h' <- pretty $ h // V x
      pure $ text "funext" <> parens (f' <> semi <+> g' <> semi <+> brackets (text x) <+> h')
  pretty (UIP p q) = scope $ do
    p' <- pretty p
    q' <- pretty q
    pure $ text "uip" <> parens (p' <> semi <+> q')
  pretty (BoolElim c m n b) = do
    xc <- scope $ do
      x  <- var
      c' <- pretty $ c // V x
      pure $ brackets (text x) <+> c'
    m' <- pretty m
    n' <- pretty n
    b' <- pretty b
    pure $ text "boolElim" <> parens (xc <> semi <+> m' <> semi <+> n' <> semi <+> b')
  pretty (f :@ a) = (<+>) <$> pretty f <*> pretty a
  pretty (Spread c e p) = do
    c' <- scope $ do
      u <- var
      uc <- pretty (c // V u)
      pure $ brackets (text u) <+> uc
    e' <- scope $ do
      v <- var
      scope $ do
        w <- var
        vwe <- pretty (e /// (V v, V w))
        pure $ brackets (text v <> comma <> text w) <+> vwe
    p' <- pretty p
    pure $ text "spread" <> parens (c' <> semi <+> e' <> semi <+> p')
  pretty (Proj i p) = do
    let i' = text $ if i then "₁" else "₂"
    p' <- pretty p
    pure $ text "π" <> i' <> parens p'
  pretty (PairEq m n p q) = do
    m' <- pretty m
    n' <- pretty n
    p' <- pretty p
    q' <- pretty q
    pure $ text "pairEq" <> parens (m' <> semi <+> n' <> semi <+> p' <> semi <+> q')

instance Pretty String where
  pretty = return . text

instance Pretty (Decl String) where
  pretty (n, s, u) =  do
    let Realizer r = extractRealizer u
    n' <- pretty n
    s' <- pretty s
    u' <- pretty u
    r' <- pretty r
    pure $
     text "⊢" <+> n' $$
       nest 2
         (vcat [ text "⇓" <+> r'
               , text "╟" <+> u'
               , text "∈" <+> s'
               ]
         )
