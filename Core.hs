module Core where

import Control.Monad
import Data.Map as M
import Data.List as L
import Control.Monad.State.Lazy as S 
import Control.Applicative
import Data.Char

{-
TODO:
- parsing
- printing
- rewrite rules
-}

data Term
  = Type
  | Kind
  | Var Int
  | Lam String Term Term
  | Pi  String Term Term
  | App Term Term
  | Def String

type Hyp = (String,Term)
type Context = [Hyp]
type Defs = Map String Term
type Rule = [Term] -> Term
type Rules = Map String Rule
type Signature = (Defs,Rules)

mkApp :: Term -> [Term] -> Term
mkApp = L.foldl App

unrollApp :: Term -> (Term, [Term])
unrollApp (App fun arg) =
  let (fun',args) = unrollApp fun in (fun',arg:args)
unrollApp t = (t,[])

fold :: (Hyp -> k -> k) -> k -> (k -> Term -> a -> a) -> Term -> a -> a
fold push ctx f t = case t of
  App fun arg -> f ctx fun . f ctx arg
  Lam n src dst -> f ctx src . f (push (n,src) ctx) dst
  Pi  n src dst -> f ctx src . f (push (n,src) ctx) dst
  t -> id

map :: (Hyp -> k -> k) -> k -> (k -> Term -> Term) -> Term -> Term
map push ctx f t = case t of
  App fun arg -> App (f ctx fun) (f ctx arg)
  Lam n src dst -> Lam n (f ctx src) (f (push (n,src) ctx) dst)
  Pi  n src dst -> Pi  n (f ctx src) (f (push (n,src) ctx) dst)
  t -> t

-- parsing

type Parser = StateT String Maybe

char :: Parser Char
char = do
  c <- get
  case c of
    (x : xs) -> put xs >> pure x
    _ -> S.lift Nothing

parseIf :: (Char -> Bool) -> Parser Char
parseIf f = do
  x <- char
  guard (f x)
  pure x

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

symbol :: Parser String
symbol = do
  i <- ident
  if i == "def" || i == "data"
  then S.lift Nothing
  else pure i

expect :: Char -> Parser ()
expect = void . parseIf . (==)

expr :: Parser Term
expr =
  (Type <$ expect '*') <|>
  (Def <$> symbol) <|>
  (Lam
    <$> (expect '[' *> symbol)
    <*> (expect ':' *> expr)
    <*> (expect ']' *> expr)) <|>
  (Pi
    <$> (expect '{' *> symbol)
    <*> (expect ':' *> expr)
    <*> (expect '}' *> expr)) <|>
  (App
    <$> (expect '(' *> expr)
    <*> (expect ')' *> expr))

decl :: Parser (Either (String,Term)(String,Term,[(String,Term)]))
decl = do
  kw <- ident
  case kw of
    "def" -> do
      name <- symbol
      expect '='
      body <- expr
      pure (Left (name,body))
    "data" -> do
      name <- symbol
      expect ':'
      arity <- expr
      let ctor = (,) <$> (expect '|' *> symbol) <*> (expect ':' *> expr)
      ctors <- many ctor
      pure (Right (name,arity,ctors))

solveVars :: Term -> Term
solveVars t = f [] t where
  f ctx (Def n) = g 0 ctx n
  f ctx t = Core.map (:) ctx f t

  g n [] name = Def name
  g n ((name',ty):ctx) name
    | name == name' = Var n
    | otherwise = g (n + 1) ctx name

-- prettyprint

showTerm :: Context -> Term -> String
showTerm ctx Type = "*"
showTerm ctx Kind = "?"
showTerm ctx (Var n) = fst (ctx !! n)
showTerm ctx (Lam n src dst) = "[" ++ n ++ ":" ++ showTerm ctx src ++ "]" ++ showTerm ((n,src):ctx) dst
showTerm ctx (Pi n src dst) = "{" ++ n ++ ":" ++ showTerm ctx src ++ "}" ++ showTerm ((n,src):ctx) dst 
showTerm ctx (App fun arg) = "(" ++ showTerm ctx fun ++ ")" ++ showTerm ctx arg
showTerm ctx (Def name) = name

showDefs :: Defs -> String
showDefs = unlines . fmap (\(name,ty) -> name ++ " : " ++ showTerm [] ty) . toList

-- checker

lift :: Int -> Term -> Term
lift n = f 0 where
  f k (Var m)
    | m >= k = Var (m + n)
  f k t = Core.map (const (+1)) k f t

psubst :: [Term] -> Term -> Term
psubst args = f 0 where
  nargs = length args

  f k (t @ (Var n))
    | n >= k + nargs = Var (n - nargs)
    | n < k = t
    | otherwise = Core.lift k (args !! (n - k))
  f k (App fun arg) = g (f k fun) (f k arg)
  f k t = Core.map (const (+1)) k f t

  g (Lam _ _ dst) arg = psubst [arg] dst
  g fun arg = App fun arg

whnf :: Signature -> Term -> Term
whnf (_,rules) t = f t [] where
  f (App fun arg) s = f fun (f arg [] : s)
  f (Lam _ _ t) (arg : s) = f (psubst [arg] t) s
  f (Def n) s = case M.lookup n rules of
    Nothing -> mkapp (Def n) s
    Just rule -> rule s
  f t s = mkApp t s

convertible :: Signature -> Term -> Term -> Bool
convertible sig t0 t1 = cmp (whnf sig t0) (whnf sig t1) where
  cmp Type Type = True
  cmp Kind Kind = True
  cmp (Var n0) (Var n1) = n0 == n1
  cmp (App f0 a0) (App f1 a1) =
    cmp f0 f1 && cmp a0 a1
  cmp (Lam _ _ dst0) (Lam _ _ dst1) =
    convertible sig dst0 dst1
  cmp (Pi _ src0 dst0) (Pi _ src1 dst1) =
    convertible sig src0 src1 &&
    convertible sig dst0 dst1
  cmp (Def n0) (Def n1) = n0 == n1
  cmp _ _ = False

type Error = ()

ensureSort :: Term -> Either Error ()
ensureSort Type = pure ()
ensureSort Kind = pure ()
ensureSort _    = Left ()

ensureFun :: Signature -> Term -> Either Error (Term,Term)
ensureFun sig t = case whnf sig t of
  Pi _ src dst -> pure (src,dst)
  _ -> Left ()

infer :: Signature -> Context -> Term -> Either Error Term
infer sig ctx t = case t of
  Type -> pure Kind
  Kind -> Left ()
  Var n -> pure (Core.lift (n + 1) (snd (ctx !! n)))
  App f x -> do
    tf <- infer sig ctx f
    (src,dst) <- ensureFun sig tf
    tx <- infer sig ctx x
    unless (convertible sig src tx) (Left ())
    pure (psubst [x] dst)
  Lam n src dst -> do
    ksrc <- infer sig ctx src
    ensureSort ksrc
    tdst <- infer sig ((n,src):ctx) dst
    pure (Pi n src tdst)
  Pi n src dst -> do
    ksrc <- infer sig ctx src
    ensureSort ksrc
    kdst <- infer sig ((n,src):ctx) dst
    ensureSort kdst
    pure kdst
  Def n -> pure (fst sig ! n)

insertName :: String -> Term -> StateT Signature (Either Error) ()
insertName name ty = do
  (defs,rules) <- get
  case M.lookup name defs of
    Nothing -> do
      traceM (name ++ " : " ++ showTerm [] ty)
      put (M.insert name ty defs, rules)
    Just name' -> Left ()

insertRule :: String -> ([Term] -> Term) -> StateT Signature (Either Error) ()
insertRule name rule = modify (\(defs,rules) -> (defs, M.insert name rule rules))

checkCtor :: String -> Term -> Either Error [Bool]
checkCtor ind = checkArgs where
  checkArgs (Pi _ src dst) = (:) <$> checkPositive src <*> checkArgs dst
  checkArgs t = case unrollApp t of
    (Def n, args) -> 
      if n == ind && not (any occurs args)
      then pure []
      else Left ()
    _ -> Left ()

  checkPositive (Pi _ src dst)
    | occurs src = Left ()
    | otherwise = checkPositive dst
  checkPositive t =
    let (fun,args) = unrollApp t in
    if any occurs args
    then Left ()
    else case fun of
      Def n -> pure (n == ind)
      _ -> pure False

  occurs t = f () t False

  f () (Def n) acc
    | n == ind = True
    | otherwise = acc
  f () t acc = Core.fold (const id) () f t acc

motiveType :: Int -> Term -> Term -> Term
motiveType ino iref (Pi n src dst) = Pi n src (motiveType ino iref dst)
motiveType ino iref t = Pi "_" (mkApp iref (fmap Var (reverse [0 .. ino - 1]))) Type

getIndices :: Term -> [Term] -> [Term]
getIndices fun args = snd (unrollApp (psubst args (unroll fun))) where
  unroll (Pi _ _ dst) = unroll dst
  unroll t = t

branchType :: [Bool] -> Int -> Term -> Term -> Term
branchType recs mot ctor ctorty = walkArgs mot [] ctorty where
  walkArgs mot ctx (Pi n src dst) = Pi n src (walkArgs (mot + 1) ((n,src):ctx) dst)
  walkArgs mot ctx t = computeIH mot (length ctx - 1) ctx recs t

  computeIH mot argd ctx [] t = computeResult mot ctx t
  computeIH mot argd ctx (False:recs) t = computeIH mot (argd - 1) ctx recs t
  computeIH mot argd ctx (True:recs) t = let
    ty = Core.lift (argd + 1) (snd (ctx !! argd))
    ih = abstractArgs mot argd 0 ty ty
    name = "ih" ++ show (length recs - argd - 1)
    in Pi name ih (computeIH (mot + 1) argd ((name,ih):ctx) recs t)

  abstractArgs mot v argc ty (Pi n src dst) = Pi n src (abstractArgs (mot + 1) (v + 1) (argc + 1) ty dst)
  abstractArgs mot v argc ty t = let
    args = fmap Var (reverse [0 .. argc - 1])
    indices = getIndices (Core.lift argc ty) args -- questionable
    in mkApp (Var mot) (indices ++ [mkApp (Var v) args])

  computeResult mot ctx t = let
    ih_count = length (L.filter id recs)
    args = fmap Var (reverse [ih_count .. length ctx - ih_count - 1])
    indices = getIndices ctorty args
    in mkApp (Var mot) (indices ++ [mkApp ctor args])

computeElimRule :: Int -> Int -> Term -> [Term] -> [(String,Int)] -> [Term] -> Term
computeElimRule ctorno indexno self branchTypes tags stack
  -- motive=1, branches=ctorno, indices=indexno, eliminee=1
  | ctorno + indexno + 2 <= length stack =
    let
      (motive : stack2) = stack
      (branches, stack3) = L.splitAt ctorno stack2
      (indices, stack4) = L.splitAt indexno stack3
      (eliminee : stack5) = stack4
      (head, args) = unrollApp (whnf eliminee)
    in case head of
      Def name ->
        case L.lookup name tags of
          Just tag ->
            let
              tag' = ctorno - tag - 1
              branch = branches !! tag'

              -- the branch here must be applied to the args and the recursive calls
              -- the recursive calls are tricky because we must know which args are recursive
              -- and what their types are, then we must type-correctly lambda-abstract over them,
              -- and apply the recursor
              -- how to get types of subdata:
              -- from constructor or branch type
              -- apply elimTy to motive
              -- select branch
              -- walk through args
              -- inhabit recursion types

            in undefined
          _ -> mkApp self stack
      _ -> mkApp self stack
  | otherwise = mkApp self stack 

checkInductive :: String -> Term -> [(String,Term)] -> StateT Signature (Either Error) ()
checkInductive name arity ctors = do
  sig <- get
  k <- S.lift (infer sig [] arity)
  unless (convertible sig k Kind) (S.lift (Left ()))
  insertName name arity
  let unrollPi (Pi _ _ dst) = 1 + unrollPi dst
      unrollPi _ = 0
      ino = unrollPi arity
      iref = Def name
      (ctornames,ctortys) = unzip ctors
  S.lift (mapM_ (infer sig []) ctortys)
  recs <- S.lift (mapM (checkCtor name) ctortys)
  zipWithM insertName ctornames ctortys
  let ctorno = length ctors
      crefs = fmap Def ctornames
      motiveTy = motiveType ino iref arity
      branchTypes = zipWith4 branchType recs [0..] crefs ctortys
      walkIndices (Pi n src dst) = Pi n src (walkIndices dst)
      walkIndices t = Pi "x" (mkApp iref (fmap Var (reverse [0 .. ino - 1]))) (mkApp (Var ctorno) (fmap Var (reverse [0 .. ino])))
      returnType = walkIndices arity
      branchNames = fmap (\n -> "p" ++ show n) [0..]
      branches = L.foldl (\acc (n,src) -> Pi n src acc) returnType (zip branchNames branchTypes)
      elimTy = Pi "P" motiveTy branches
      elimName = name ++ "_rec"
      elimRule = computeElimRule ctorno ino (Def elimName) (zipWith3 (\recs -> branchType recs 0) crefs ctortys) (zip ctornames [0..])
  insertName elimName elimTy
  insertRule elimName elimRule
