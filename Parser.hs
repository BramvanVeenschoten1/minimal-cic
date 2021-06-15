module Parser where

import Lexer hiding (keywords, puncts)
import Core

import Control.Applicative ( Alternative(some,many) )
import Data.List ()
import Data.Function ()
import Data.Array.Unboxed ( listArray )
import Data.Maybe ( isJust )
import Control.Monad.RWS

type Param = (Loc, String, Term)
type Ctor = (Loc, String, Term)
type Module = [Decl]

data Decl
  = Data String Term [(String,Term)]
  | Func String Term
  | Axiom String Term
  | Print Term

mkPi _ _  = Pi
mkType _  = Type
mkLam _ _ = Lam
mkApply _ = App

puncts :: [String]
puncts = ["|", "->", "=", "(" , ")", "\\", ":", ","]

keywords :: [String]
keywords = [
  "data",
  "let",
  "axiom",
  "print",
  "Pi", 
  "Type"]

annotParam :: Parser [Param]
annotParam = do
  bs <- some (withLoc (expectSymbol "name in parameter list"))
  expect ":" "':' after name in binding"
  ty <- parseTerm
  pure (fmap (\(nloc,name) -> (nloc,name,ty)) bs)

param :: Parser [Param]
param = do
  t <- peekToken
  case t of
    Pct "(" -> token *> annotParam <* expect ")" "closing ')' after parameter"
    _ -> annotParam

params :: Parser [Param]
params = do
  t <- peekToken
  case t of
    Symbol _ -> someParams
    Pct "("  -> someParams
    _ -> pure []
  
someParams :: Parser [Param]
someParams = (++) <$> param <*> params

-- parse a lambda or dependent product,
-- having already consumed the '\\' or 'Pi' token
parseBinder :: Cursor -> (Loc -> Loc -> String -> Term -> Term -> Term) -> Parser Term
parseBinder begin mk = do
  ps <- someParams
  expect "," "',' after parameters in binder"
  body <- parseTerm
  loc <- endLoc begin
  let f (nloc,v,ta) = mk loc nloc v ta
  pure (foldr f body ps)

parsePrimary :: Parser Term
parsePrimary = do
  begin   <- beginLoc
  (loc,t) <- withLoc token
  case t of
    Pct "(" -> parseTerm <* expect ")" "closing ')' after parseTermession"
    Pct "\\" -> parseBinder begin mkLam
    Pct "Type" -> pure (mkType loc)
    Pct "Pi" -> parseBinder begin mkPi
    Symbol x -> pure (Def x)
    x -> expected loc "some parseTermession" (show loc)

parseApp :: Parser Term
parseApp = do
  begin <- beginLoc 
  head <- parsePrimary
  let
    parseArgs :: Parser [(Loc,Term)]
    parseArgs = do
      t <- peekToken
      case t of
        Symbol _    -> expArg
        Pct "Type"  -> expArg
        Pct "\\"    -> expArg
        Pct "Pi"    -> expArg
        Pct "("     -> expArg
        _           -> pure []
    
    expArg = do
      arg <- parsePrimary
      loc <- endLoc begin
      args <- parseArgs
      pure ((loc,arg):args)

  args <- parseArgs
  pure (foldl (\fun (loc,arg) -> mkApply loc fun arg) head args)
  where

parseArrow :: Parser Term
parseArrow = do
  begin <- beginLoc
  lhs   <- parseApp
  t     <- peekToken
  case t of
    Pct "->" -> f begin lhs
    _ -> pure lhs
    where
      f begin lhs = do
        token
        rhs <- parseArrow
        loc <- endLoc begin
        pure (mkPi loc loc "" lhs rhs)

parseTerm :: Parser Term
parseTerm = parseArrow

parseConstructors :: Parser [Ctor]
parseConstructors = do
  t <- peekToken
  case t of
    Pct "|" -> do
      token
      (nloc,name) <- withLoc $ expectSymbol "name in constructor definition"
      expect ":" "':' after name in constructor definition"
      ty <- parseTerm
      ctors <- parseConstructors
      pure ((nloc,name,ty):ctors)
    _ -> pure []

-- parse a data declaration/definition,
-- having already consumed the 'data' keyword
parseData :: Parser Decl
parseData = do
  (loc,name) <- withLoc (expectSymbol "name after 'data' in data declaration")
  expect ":" "':' after name in data declaration"
  arity <- parseTerm
  ctors <- parseConstructors
  pure (Data name (solveVars arity) (fmap (\(x,y,z) -> (y,solveVars z)) ctors))
  
-- parse a function clause/declaration, having already consumed the 'let' keyword
parseFunction :: Parser Decl
parseFunction = do
  name <- expectSymbol "name after 'let' in function definition"
  expect "=" "'=' after name in function definition"
  body <- parseTerm
  pure (Func name (solveVars body))

parseAxiom = do
  name <- expectSymbol "name after 'axiom' in axiom declaration"
  expect ":" "':' after name in axiom declaration"
  ty <- parseTerm
  pure (Axiom name (solveVars ty))

parsePrint = fmap (Print . solveVars) parseTerm

-- parse declarations
parseDecls :: Parser [Decl]
parseDecls = do
  (loc,t) <- withLoc token
  case t of
    Pct ""     -> pure []
    Pct "data" -> (:) <$> parseData <*> parseDecls
    Pct "let"  -> (:) <$> parseFunction <*> parseDecls
    Pct "axiom" -> (:) <$> parseAxiom <*> parseDecls
    Pct "print" -> (:) <$> parsePrint <*> parseDecls
    x -> err (show loc ++ "expected some declaration")

parse :: Filename -> String -> Either ParseError Module
parse name input = do
  fst <$> evalRWST
            parseDecls
            (ParserEnv keywords puncts name (listArray (0, length input - 1) input))
            (Cursor 0 0 0)
