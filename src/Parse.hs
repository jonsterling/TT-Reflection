{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Parse where

import Control.Arrow
import Control.Monad
import Control.Applicative
import qualified Data.HashSet as HS
import Data.Monoid

import Text.Trifecta
import Text.Parser.Token.Highlight

import qualified Bound as B

import Syntax

emptyOps :: (Monad m, TokenParsing m) => IdentifierStyle m
emptyOps = IdentifierStyle
  { _styleName      = "operator"
  , _styleStart     = alphaNum <|> oneOf "_-"
  , _styleLetter    = alphaNum <|> oneOf "_-"
  , _styleHighlight = Identifier
  , _styleReserved  = mempty
  , _styleReservedHighlight = ReservedIdentifier
  }

identifier :: (Monad m, TokenParsing m) => m String
identifier = ident emptyOps

reserved :: (Monad m, TokenParsing m) => String -> m ()
reserved = reserve emptyOps

parseConstant :: (Monad m, TokenParsing m) => m Constant
parseConstant = Zero <$ (reserved "`0" <|> reserved "𝟘")
            <|> One  <$ (reserved "`1" <|> reserved "𝟙")
            <|> Two  <$ (reserved "`2" <|> reserved "𝟚")
            <|> Dot  <$ (reserved "<>" <|> reserved "♦")
            <|> U    <$ (reserved "U"  <|> reserved "𝕌")
            <|> Tt   <$ reserved "tt"
            <|> Ff   <$ reserved "ff"
            <|> Refl <$ reserved "refl"

parseBinder :: (Monad m, TokenParsing m) => m Binder
parseBinder = Pi <$ (reserved "pi" <|> reserved "Π")
          <|> Sg <$ (reserved "sg" <|> reserved "Σ")

optionalParens :: TokenParsing m => m a -> m a
optionalParens p = try p <|> parens p

parseAnnBoundExpr :: (Monad m, TokenParsing m) => m (Tm String, B.Scope () Tm String)
parseAnnBoundExpr = do
  (u,t) <- brackets $ parseAnnot
  e <- parseTm
  return $ (t, u \\ e)

parseBoundExpr :: (Monad m, TokenParsing m) => m (B.Scope () Tm String)
parseBoundExpr = do
  u <- brackets $ identifier
  e <- parseTm
  return $ u \\ e

parseAnnot :: (Monad m, TokenParsing m) => m (String, Tm String)
parseAnnot = (,) <$> identifier <* colon <*> parseTm

parseLambda :: (Monad m, TokenParsing m) => m ()
parseLambda = reserved "lam"
          <|> reserved "λ"

parseLambdaExpr :: (Monad m, TokenParsing m) => m (Tm String)
parseLambdaExpr = Lam
              <$> (parseLambda *> whiteSpace *> parseBoundExpr)

parseBinderExpr :: (Monad m, TokenParsing m) => m (Tm String)
parseBinderExpr = uncurry . B
              <$> parseBinder
              <*> (whiteSpace *> parseAnnBoundExpr)

parseReflection :: (Monad m, TokenParsing m) => m (Tm String)
parseReflection = Reflect
              <$> (reserved "reflect" *> parseTm)
              <*> (reserved "in" *> parseTm)

parseIdentityType :: (Monad m, TokenParsing m) => m (Tm String)
parseIdentityType = do
  reserved "Id"
  s <- parseTm
  a <- parseTm
  b <- parseTm
  return $ Id a b s

parseTm :: (Monad m, TokenParsing m) => m (Tm String)
parseTm = optionalParens parseTm'
  where
    parseTm' = (C <$> parseConstant <?> "constant")
           <|> (parseLambdaExpr <?> "lambda expr")
           <|> (parseBinderExpr <?> "binder expr")
           <|> (parseReflection <?> "reflection scope")
           <|> (parseIdentityType <?> "identity type")
           <|> (parens $ Ann <$> (parseTm <* colon) <*> parseTm <?> "annotation")
           <|> (V <$> identifier <?> "variable")
