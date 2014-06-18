{-# LANGUAGE FlexibleInstances #-}

module Pretty where

import qualified Bound            as B
import           Syntax
import           Text.PrettyPrint
import           Typing           hiding (Type)

class Pretty a where
  pretty :: Int -> a -> Doc

instance Pretty Binder where
  pretty i Pi = text "Π"
  pretty i Sg = text "Σ"

instance Pretty Constant where
  pretty i Zero = text "𝟘"
  pretty i One = text "𝟙"
  pretty i Two = text "𝟚"
  pretty i U = text "𝕌"
  pretty i Tt = text "tt"
  pretty i Ff = text "ff"
  pretty i Dot = text "♦"
  pretty i Refl = text "refl"

instance Pretty a => Pretty (B.Var () a) where
  pretty i (B.B x) = text $ "@" ++ show i
  pretty i (B.F x) = pretty i x

instance (Show a, Pretty a) => Pretty (Tm a) where
  pretty i (V a) = pretty i a
  pretty i (C c) = pretty i c
  pretty i (Ann a s) = parens $ pretty i a <+> colon <+> pretty i s
  pretty i (Pair a b) = text "〈" <+> pretty i a <+> comma <+> pretty i b <+> text "〉"
  pretty i (B b s (B.Scope e)) = pretty i b <> brackets (pretty i s) <+> pretty (i + 1) e
  pretty i (Lam (B.Scope e)) = text "λ" <+> pretty (i + 1) e
  pretty i (Reflect a b) = text "reflect" <+> pretty i a <+> text "in" <+> pretty i b
  pretty i (Id a b s) = text "Id" <+> pretty i s <+> pretty i a <+> pretty i b
  pretty i (f :@ a) = pretty i f <+> pretty i a
  pretty i e = error $ "Welp: " ++ show e

instance Pretty String where
  pretty _ = text

prettyDecl :: Decl String -> Doc
prettyDecl (n, s, u) =
  let Realizer r = extractRealizer u in
  text "⊢" <+> text n $$
    nest 2
      (vcat [ text "⇓" <+> pretty 0 r
            , text "╟" <+> pretty 0 u
            , text "∈" <+> pretty 0 s
            ]
      )

