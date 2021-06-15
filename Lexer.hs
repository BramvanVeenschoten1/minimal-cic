module Lexer where

import Control.Applicative (Alternative (..))
import Control.Monad (guard, replicateM)
import Control.Monad.RWS
import Data.Array.Unboxed (IArray (bounds), UArray, (!))
import Data.Char
import Data.Either ()
import Data.Foldable (asum)

data Cursor = Cursor
  { cursorIndex :: Int,
    line :: Int,
    col :: Int
  }

data Token
  = Symbol String
  | Number Int
  | Pct String
  | Str [Int]
  deriving (Eq)

type Position = (Int, Int)

type Range = (Position, Position)

data Loc = Loc
  { uri :: String,
    range :: Range
  }

emptyLoc :: Loc
emptyLoc = Loc "" ((0,0),(0,0))

type ParseError = String

type Filename = String

type Charray = UArray Int Char

type Indent = Int

data ParserEnv = ParserEnv
  { keywords :: [String],
    puncts :: [String],
    filename :: Filename,
    source :: Charray
  }

type Parser a = RWST ParserEnv String Cursor (Either ParseError) a

len :: Charray -> Int
len = (+ 1) . snd . bounds

instance Show Loc where
  show (Loc src ((startLine, startCol), (endLine, endCol))) =
    src ++ ": "
      ++ show startLine
      ++ ":"
      ++ show startCol
      ++ " - "
      ++ show endLine
      ++ ":"
      ++ show endCol

err :: String -> Parser a
err = lift . Left

expected :: Loc -> String -> String -> Parser a
expected span msg e =
  err $
    show span ++ "\nexpected " ++ msg ++ ", but got: \'" ++ e ++ "\'"

errAt :: Loc -> String -> Parser a
errAt span msg = err (show span ++ msg)

isEof :: Parser Bool
isEof = do
  index <- gets cursorIndex
  leng <- asks (len . source)
  pure (index >= leng)

eof :: Parser Token
eof = do
  b <- isEof
  if b then pure (Pct "") else err ""

char :: Parser Char
char = do
  c <- get
  name <- asks filename
  arr <- asks source
  end <- asks (len . source)
  if cursorIndex c >= end
    then err (name ++ ": Unexpected end of input")
    else pure ()
  let x = arr ! cursorIndex c
      c' =
        if x == '\n'
          then
            Cursor
              { cursorIndex = cursorIndex c + 1,
                col = 0,
                line = line c + 1
              }
          else
            Cursor
              { cursorIndex = cursorIndex c + 1,
                col = col c + 1,
                line = line c
              }
  put c'
  pure x

peek :: Parser a -> Parser a
peek p = do
  save <- get
  res <- p
  put save
  pure res

parseIf :: (Char -> Bool) -> Parser Char
parseIf f = do
  x <- char
  guard (f x)
  pure x

beginLoc :: Parser Cursor
beginLoc = ws *> get

endLoc :: Cursor -> Parser Loc
endLoc x = do
  y <- get
  src <- asks filename
  arr <- asks source
  pure $
    Loc src ((line x, col x),(line y, col y))

withLoc :: Parser a -> Parser (Loc, a)
withLoc p = do
  ws
  begin <- get
  item <- p
  loc <- endLoc begin
  pure (loc, item)

string :: String -> Parser String
string = mapM (parseIf . (==))

ws :: Parser ()
ws = blockComment *> ws <|> lineComment *> ws <|> parseIf isSpace *> ws <|> pure ()
  where
    blockComment = string "{-" *> blockRest
    blockRest = string "-}" <|> blockComment *> blockRest <|> char *> blockRest
    lineComment = string "--" *> lineRest
    lineRest = parseIf (== '\n') <|> char *> lineRest

ident :: Parser [Char]
ident =
  (:) <$> parseIf (\x -> x == '_' || isAlpha x)
    <*> many (parseIf (\x -> x == '_' || isAlphaNum x))

number :: Parser Token
number = Number . read <$> some (parseIf isDigit)

symbol :: Parser Token
symbol = do
  kw <- asks keywords
  i  <- ident
  if i `elem` kw then pure (Pct i) else pure (Symbol i)

punct :: Parser Token
punct = do
  ps <- asks puncts
  Pct <$> asum (string <$> ps)
  fmap Pct (fmap string ps)
  asks puncts >>= (fmap Pct . fmap string)

token :: Parser Token
token = ws *> (eof <|> f)
  where
    f = number <|> symbol <|> punct <|> badChar

    badChar = withLoc char >>= flip errAt "unexpected character\n" . fst

peekToken :: Parser Token
peekToken = peek token

expectSymbol :: String -> Parser String
expectSymbol msg = withLoc token >>= f
  where
    f (_, Symbol s) = pure s
    f (loc, e) = expected loc msg (show loc)

expect :: String -> String -> Parser String
expect x msg = withLoc token >>= f
  where
    f (_, Pct y)
      | x == y = pure y
    f (loc, e) = expected loc msg (show loc)
