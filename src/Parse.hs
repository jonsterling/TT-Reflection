
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
  parens $ do
    s <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    m <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    n <- parseTm
    return $ Id s m n

parseBinderEq :: (Monad m, TokenParsing m) => m (Tm String)
parseBinderEq = do
  reserved "binderEq"
  parens $ BinderEq
    <$> parseTm <* whiteSpace
    <*> (semicolon *> whiteSpace *> parseBoundExpr)

parseFunext :: (Monad m, TokenParsing m) => m (Tm String)
parseFunext = do
  reserved "funext"
  parens $ do
    f <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    g <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    h <- parseBoundExpr
    return $ Funext f g h

parseUIP :: (Monad m, TokenParsing m) => m (Tm String)
parseUIP = do
  reserved "uip"
  parens $ do
    p <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    q <- parseTm
    return $ UIP p q

parseBoolElim :: (Monad m, TokenParsing m) => m (Tm String)
parseBoolElim = do
  reserved "boolElim"
  parens $ do
    c <- parseBoundExpr
    whiteSpace *> semicolon *> whiteSpace
    m <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    n <- parseTm
    whiteSpace *> semicolon *> whiteSpace
    b <- parseTm
    return $ BoolElim c m n b

parseApp :: (Monad m, TokenParsing m) => m (Tm String)
parseApp = (:@) <$> parseTm <*> parseTm

parseTm :: (Monad m, TokenParsing m) => m (Tm String)
parseTm = optionalParens parseTm'
  where
    parseTm' = (C <$> parseConstant <?> "constant")
           <|> (parseLambdaExpr <?> "lambda expr")
           <|> (parseBinderExpr <?> "binder expr")
           <|> (parseReflection <?> "reflection scope")
           <|> (parseIdentityType <?> "identity type")
           <|> (parseBinderEq <?> "binder equality expr")
           <|> (parseFunext <?> "function extensionality expr")
           <|> (parseBoolElim <?> "bool elimination")
           <|> (parseUIP <?> "UIP expr")
           <|> (try (parens $ Ann <$> (parseTm <* colon) <*> parseTm) <?> "annotation")
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

