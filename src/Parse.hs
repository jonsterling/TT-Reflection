
module Parse where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import qualified Data.HashSet                as HS
import           Data.Monoid

import           Text.Parser.Token.Highlight
import           Text.Trifecta               hiding ((:@))

import qualified Bound                       as B

import           Syntax

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

semicolon :: CharParsing m => m Char
semicolon = char ';'

parseConstant :: (Monad m, TokenParsing m) => m Constant
parseConstant = Zero <$ (reserved "`0" <|> reserved "𝟘")
            <|> One  <$ (reserved "`1" <|> reserved "𝟙")
            <|> Two  <$ (reserved "`2" <|> reserved "𝟚")
            <|> Dot  <$ (reserved "<>" <|> reserved "♦")
            <|> U    <$ (reserved "U"  <|> reserved "𝕌")
            <|> Tt   <$ reserved "tt"
            <|> Ff   <$ reserved "ff"

parseBinder :: (Monad m, TokenParsing m) => m Binder
parseBinder = Pi <$ (reserved "pi" <|> reserved "Π")
          <|> Sg <$ (reserved "sg" <|> reserved "Σ")

optionalParens :: TokenParsing m => m a -> m a
optionalParens p = try p <|> parens p

parseAnnBoundExpr :: (Monad m, TokenParsing m) => m (Tm String, B.Scope () Tm String)
parseAnnBoundExpr = do
  (u,t) <- brackets parseAnnot
  e <- parseTm
  return (t, u \\ e)

parseBoundExpr :: (Monad m, TokenParsing m) => m (B.Scope () Tm String)
parseBoundExpr = do
  u <- brackets identifier
  e <- parseTm
  return $ u \\ e

parseBoundExpr2 :: (Monad m, TokenParsing m) => m (B.Scope Bool Tm String)
parseBoundExpr2 = do
  (u,v) <- brackets $ (,) <$> identifier <*> identifier
  e <- parseTm
  return $ (u,v) \\\ e

parseAnnot :: (Monad m, TokenParsing m) => m (String, Tm String)
parseAnnot = (,) <$> identifier <* colon <*> parseTm

parseLambda :: (Monad m, TokenParsing m) => m ()
parseLambda = reserved "lam"
          <|> reserved "λ"

parseLambdaExpr :: (Monad m, TokenParsing m) => m (Tm String)
parseLambdaExpr = Lam
              <$> (parseLambda *> whiteSpace *> parseBoundExpr)

parseLet :: (Monad m, TokenParsing m) => m (Tm String)
parseLet = do
  reserved "let"
  x <- identifier
  reserved "="
  s <- parseTm
  reserved "in"
  e <- parseTm
  return $ Let s (x \\ e)

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
  parens $ do
    s <- parseTm
    whiteSpace; semicolon; whiteSpace
    m <- parseTm
    whiteSpace; semicolon; whiteSpace
    n <- parseTm
    return $ Id s m n

parseBoolElim :: (Monad m, TokenParsing m) => m (Tm String)
parseBoolElim = do
  reserved "boolElim"
  parens $ do
    c <- parseBoundExpr
    whiteSpace; semicolon; whiteSpace
    m <- parseTm
    whiteSpace; semicolon; whiteSpace
    n <- parseTm
    whiteSpace; semicolon; whiteSpace
    b <- parseTm
    return $ BoolElim c m n b

parseApp :: (Monad m, TokenParsing m) => m (Tm String)
parseApp = (:@) <$> parseTm <*> parseTm

parsePair :: (Monad m, TokenParsing m) => m (Tm String)
parsePair = do
  reserved "⟨" <|> reserved "<"
  m <- parseTm
  whiteSpace; comma; whiteSpace
  n <- parseTm
  reserved "⟩" <|> reserved ">"
  return $ Pair m n

parseSpread :: (Monad m, TokenParsing m) => m (Tm String)
parseSpread = do
  reserved "spread"
  parens $ do
    c <- parseBoundExpr
    whiteSpace; semicolon; whiteSpace
    e <- parseBoundExpr2
    whiteSpace; semicolon; whiteSpace
    p <- parseTm
    return $ Spread c e p

parseProj1 :: (Monad m, TokenParsing m) => m (Tm String)
parseProj1 = (reserved "π₁" <|> reserved "pi1") *> (Proj True <$> parens parseTm)

parseProj2 :: (Monad m, TokenParsing m) => m (Tm String)
parseProj2 = (reserved "π₂" <|> reserved "pi2") *> (Proj False <$> parens parseTm)

parseExtEq :: (Monad m, TokenParsing m) => m (Tm String)
parseExtEq = do
  reserved "extEq"
  p <- parens parseTm
  return $ ExtEq p

parseTm :: (Monad m, TokenParsing m) => m (Tm String)
parseTm = optionalParens parseTm'
  where
    parseTm' = (C <$> parseConstant <?> "constant")
           <|> (parseLambdaExpr <?> "lambda expr")
           <|> (parseBinderExpr <?> "binder expr")
           <|> (parseReflection <?> "reflection scope")
           <|> (parseIdentityType <?> "identity type")
           <|> (parseExtEq <?> "extEq expr")
           <|> (parseBoolElim <?> "bool elimination")
           <|> (parseSpread <?> "spread expr")
           <|> (parseProj1 <?> "pi1 expr")
           <|> (parseProj2 <?> "pi2 expr")
           <|> (parsePair <?> "pair expr")
           <|> (parseLet <?> "let expr")
           <|> (try (parens parseApp) <?> "application")
           <|> (V <$> identifier <?> "variable")

parseDecl :: (Monad m, TokenParsing m) => m (Decl String)
parseDecl = (,,)
        <$> (turnstile *> identifier)
        <*> (memberOf *> parseTm)
        <*> (evals *> parseTm)
  where
    turnstile = reserved "|-" <|> reserved "⊢"
    memberOf = reserved "in" <|> reserved "∈"
    evals = reserved "~>" <|> reserved "⇓"

