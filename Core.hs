module Core where

import Data.Map as M
import Data.List as L
import Control.Applicative
import Control.Monad
import Control.Monad.State.Lazy as S

data Term
  = Type
  | Kind
  | Var Int
  | Lam String Term Term
  | Pi  String Term Term
  | App Term Term
  | Def String

data Error
  = ExpectedSort Context Term
  | ExpectedFunction Context Term
  | ExpectedType Context Term Term Term
  | NameNotDefined String
  | NameAlreadyDefined String
  | IllFormedTypeConstructor String
  | IllFormedDataConstructor String
  | OccurrenceInIndex String
  | NegativeOccurrence String

type Hyp = (String,Term)
type Context = [Hyp]
type Rule = (Term -> [Term] -> Term) -> [Term] -> Term
type Signature = (Map String Term, Map String Rule)

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

-- a little hack, replace every def by a deBruijn index if in scope
-- the parser does not keep a context
solveVars :: Term -> Term
solveVars t = f [] t where
  f ctx (Def n) = g 0 ctx n
  f ctx t = Core.map (:) ctx f t

  g n [] name = Def name
  g n ((name',ty):ctx) name
    | name == name' = Var n
    | otherwise = g (n + 1) ctx name

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
whnf sig t = f t [] where
  f (App fun arg) s = f fun (f arg [] : s)
  f (Lam _ _ t) (arg : s) = f (psubst [arg] t) s
  f (Def n) s = case M.lookup n (snd sig) of
    Nothing -> mkApp (Def n) s
    Just rule -> rule f s
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

ensureSort :: Context -> Term -> Either Error ()
ensureSort _ Type = pure ()
ensureSort _ Kind = pure ()
ensureSort ctx x  = Left (ExpectedSort ctx x)

ensureFun :: Signature -> Context -> Term -> Either Error (Term,Term)
ensureFun sig ctx t = case whnf sig t of
  Pi _ src dst -> pure (src,dst)
  x -> Left (ExpectedFunction ctx x)

infer :: Signature -> Context -> Term -> Either Error Term
infer sig ctx t = case t of
  Type -> pure Kind
  Kind -> error "infer Kind"
  Var n -> pure (Core.lift (n + 1) (snd (ctx !! n)))
  App f x -> do
    tf <- infer sig ctx f
    (src,dst) <- ensureFun sig ctx tf
    tx <- infer sig ctx x
    unless (convertible sig src tx) (Left (ExpectedType ctx src x tx))
    pure (psubst [x] dst)
  Lam n src dst -> do
    ksrc <- infer sig ctx src
    ensureSort ctx ksrc
    tdst <- infer sig ((n,src):ctx) dst
    pure (Pi n src tdst)
  Pi n src dst -> do
    ksrc <- infer sig ctx src
    ensureSort ctx ksrc
    kdst <- infer sig ((n,src):ctx) dst
    ensureSort ctx kdst
    pure kdst
  Def n -> case M.lookup n (fst sig) of
    Just ty -> pure ty
    Nothing -> Left (NameNotDefined n)

insertName :: String -> Term -> StateT Signature (Either Error) ()
insertName name ty = do
  (defs,rules) <- get
  case M.lookup name defs of
    Nothing -> do
      put (M.insert name ty defs, rules)
    Just name' -> S.lift (Left (NameAlreadyDefined name))

insertRule :: String -> Rule -> StateT Signature (Either Error) ()
insertRule name rule = modify (\(defs,rules) -> (defs, M.insert name rule rules))

checkCtor :: String -> Term -> Either Error [Bool]
checkCtor ind = checkArgs where
  checkArgs (Pi _ src dst) = (:) <$> checkPositive src <*> checkArgs dst
  checkArgs t = case unrollApp t of
    (Def n, args) -> 
      if n == ind && not (any occurs args)
      then pure []
      else Left (OccurrenceInIndex ind)
    _ -> Left (IllFormedDataConstructor ind)

  checkPositive (Pi _ src dst)
    | occurs src = Left (NegativeOccurrence ind)
    | otherwise = checkPositive dst
  checkPositive t =
    let (fun,args) = unrollApp t in
    if any occurs args
    then Left (OccurrenceInIndex ind)
    else case fun of
      Def n -> pure (n == ind)
      _ -> pure False

  occurs t = f () t False

  f () (Def n) acc
    | n == ind = True
    | otherwise = acc
  f () t acc = Core.fold (const id) () f t acc

motiveType :: Int -> Int -> Term -> Term -> Term
motiveType ino iname iref (Pi n src dst) = Pi ("i" ++ show iname) src (motiveType ino (iname + 1) iref dst)
motiveType ino iname iref t = Pi "_" (mkApp iref (fmap Var (reverse [0 .. ino - 1]))) Type

getIndices :: Term -> [Term] -> [Term]
getIndices fun args = snd (unrollApp (psubst args (unroll fun))) where
  unroll (Pi _ _ dst) = unroll dst
  unroll t = t

countDomains :: Term -> Int
countDomains (Pi _ _ dst) = 1 + countDomains dst
countDomains _ = 0

computeBranchType :: [Bool] -> Int -> Term -> Term -> Term
computeBranchType recs mot ctor ctorty = walkArgs mot 0 [] ctorty where
  ctor_tag   = mot
  ctor_arity = countDomains ctorty

  walkArgs mot argc ctx (Pi n src dst) = let name = "x" ++ show (mot - ctor_tag) in
    Pi name src (walkArgs (mot + 1) (argc + 1) ((name,src):ctx) dst)
  walkArgs mot argc ctx t = computeIH mot (ctor_arity - 1) ctx recs t

  computeIH mot argd ctx [] t = computeResult mot ctx t
  computeIH mot argd ctx (False:recs) t = computeIH mot (argd - 1) ctx recs t
  computeIH mot argd ctx (True:recs) t = let
    ty = Core.lift (argd + 1) (snd (ctx !! argd))
    ih = abstractArgs mot argd 0 ty ty
    name = "ih" ++ show (length ctx - argd - 1)
    in Pi name ih (computeIH (mot + 1) argd ((name,ih):ctx) recs t)

  abstractArgs mot v argc ty (Pi n src dst) = Pi ("a" ++ show v) src (abstractArgs (mot + 1) (v + 1) (argc + 1) ty dst)
  abstractArgs mot v argc ty t = let
    args = fmap Var ([0 .. argc - 1])
    indices = getIndices (Core.lift argc ty) args
    in mkApp (Var mot) (reverse indices ++ [mkApp (Var v) args])

  computeResult mot ctx t = let
    ih_count = length (L.filter id recs)
    args = fmap Var [ih_count .. ih_count + ctor_arity - 1]
    indices = getIndices ctorty args
    in mkApp (Var mot) (reverse indices ++ [mkApp ctor (reverse args)])

-- discard first n domains of a nested pi type
unrollPi :: Int -> Term -> Term
unrollPi 0 t = t
unrollPi n (Pi _ _ dst) = unrollPi (n - 1) dst
unrollPi _ _ = error "unrolling pi too far"

-- select a branch type from an eliminator type
getNthBranch :: Int -> Int -> Term -> Term
getNthBranch 0 m (Pi _ src _) = Core.lift m src
getNthBranch n m (Pi _ _ dst) = getNthBranch (n - 1) (m + 1) dst

-- unroll pi type, lifting domains
unrollRecTypes :: Int -> Term -> [Term]
unrollRecTypes n (Pi _ src dst) = Core.lift n src : unrollRecTypes (n + 1) dst
unrollRecTypes _ _ = []

-- replace a recursive call type with a term inhabiting it
-- the type is a nested product type with an application in the codomain.
-- this application should have a variable as head
-- the pi types are replaced by lambda's, the variable by the recursive call term
replaceRecs :: String -> Int -> Term -> Term -> Term
replaceRecs ref n recCall (Pi name src dst) = Lam name src (replaceRecs ref (n + 1) recCall dst)
replaceRecs ref n recCall t = case unrollApp t of
  (Var m, args) -> mkApp (Core.lift m recCall) args
  _ -> error "expected a variable in application head in recursive call"

-- compute elimination rule for an inductive data types given
-- the number of constructors, number of indices, the reference to the name, the eliminator type
-- and a list associating constructor names with tags
computeElimRule :: Int -> Int -> Term -> Term -> [(String,Int)] -> Rule
computeElimRule ctorno indexno self @ (Def name) selfType tags whnf stack
  -- motive=1, branches=ctorno, indices=indexno, eliminee=1
  | ctorno + indexno + 2 <= length stack =
    let
      (motive : stack2) = stack
      (branches, stack3) = L.splitAt ctorno stack2
      (indices, stack4) = L.splitAt indexno stack3
      (eliminee : stack5) = stack4
      (head, args) = unrollApp eliminee
      recApp = mkApp self (motive : branches)
      argc = length args
      Pi _ _ selfType' = selfType
    in case head of
      Def name ->
        case L.lookup name tags of
          Just tag ->
            let
              tag' = tag
              branch = branches !! tag'
              computeBranchType = getNthBranch tag' 0 selfType'
              computeBranchTypeWithArgs = psubst args (unrollPi argc computeBranchType)
              recTypes = unrollRecTypes 0 computeBranchTypeWithArgs
              recCalls = fmap (replaceRecs name 0 recApp) recTypes
              branchArgs = reverse args ++ recCalls ++ stack5
            in whnf branch branchArgs
          _ -> mkApp self stack
      _ -> mkApp self stack
  | otherwise = mkApp self stack 

checkInductive :: String -> Term -> [(String,Term)] -> StateT Signature (Either Error) ()
checkInductive name arity ctors = do
  sig <- get
  k <- S.lift (infer sig [] arity)
  unless (convertible sig k Kind) (S.lift (Left (IllFormedTypeConstructor name)))
  insertName name arity
  let ino = countDomains arity
      iref = Def name
      (ctornames,ctortys) = unzip ctors
  sig <- get
  S.lift (mapM_ (infer sig []) ctortys)
  recs <- S.lift (mapM (checkCtor name) ctortys)
  zipWithM insertName ctornames ctortys
  let ctorno = length ctors
      crefs = fmap Def ctornames
      motiveTy = motiveType ino 0 iref arity
      branchTypes = zipWith4 computeBranchType recs [0..] crefs ctortys
      computeReturnType iname (Pi n src dst) = Pi ("i" ++ show iname) src (computeReturnType (iname + 1) dst)
      computeReturnType iname t =
        let indices = fmap Var (reverse [0 .. ino - 1])
        in Pi "x" (mkApp iref indices) (mkApp (Var (ino + ctorno + 1)) (Var ino : indices))
      returnType = computeReturnType 0 arity
      branchNames = fmap (\n -> "b" ++ show n) [0..]
      branches = L.foldr (\(n,src) acc -> Pi n src acc) returnType (zip branchNames branchTypes)
      elimTy = Pi "p" motiveTy branches
      elimName = name ++ "_rec"
      elimRule = computeElimRule ctorno ino (Def elimName) elimTy (zip ctornames [0..])
  insertName elimName elimTy
  insertRule elimName elimRule

checkDefinition :: String -> Term -> StateT Signature (Either Error) ()
checkDefinition name body = do
  sig <- get
  ty <- S.lift (infer sig [] body)
  insertName name ty
  insertRule name (\whnf stack -> whnf body stack)
