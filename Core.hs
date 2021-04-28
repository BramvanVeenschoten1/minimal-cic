module Core where

import Control.Monad
import Data.Map as M
import Data.List as L

data Term
  = Type
  | Kind
  | Var Int
  | Lam String Term Term
  | Pi  String Term Term
  | App Term Term
  | Def String Int
  | Ind String Int
  | Con String Int Int
  | Rec String Int

data Datatype = Datatype {
  indexno :: Int,
  arity :: Term,
  ctornames :: [String],
  ctors :: [Term],
  elimTy :: Term,
  elimRules :: [Term]}

type Defs = Map Int (Term,Term)
type Inds = Map Int Datatype
type Hyp = (String,Term)
type Context = [Hyp]
type Signature = (Defs,Inds)

mkApp :: Term -> [Term] -> Term
mkApp = L.foldl App

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
    | otherwise = lift k (args !! (n - k))
  f k (App fun arg) = g (f k fun) (f k arg)
  f k t = Core.map (const (+1)) k f t

  g (Lam _ _ dst) arg = psubst [arg] dst
  g fun arg = App fun arg

subst :: Term -> Term -> Term
subst arg = f 0 where
  f k t @ (Var n)
    | n > k = Var (n - 1)
    | n < k = t
    | otherwise = lift k arg
  f k (App fun arg) = g (f k fun) (f k arg)
  f k t = Core.map (const (+1)) k f t

  g (Lam _ _ dst) arg = subst arg dst
  g fun arg = App fun arg

whnf :: Signature -> Term -> Term
whnf (defs,inds) t = f t [] where
  f (App fun arg) s = f fun (f arg [] : s)
  f (Lam _ _ t) (arg : s) = f (subst arg t) s
  f (Def _ i) s = f (snd (defs ! i)) s
  f (Rec n i) s = error ("recursor not implemented: " ++ n)
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
  cmp (Ind _ i0) (Ind _ i1) = i0 == i1
  cmp (Con _ _ i0) (Con _ _ i1) = i0 == i1
  cmp (Rec _ i0) (Rec _ i1) = i0 == i1
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
  Var n -> pure (lift (n + 1) (snd (ctx !! n)))
  App f x -> do
    tf <- infer sig ctx f
    (src,dst) <- ensureFun sig tf
    tx <- infer sig ctx x
    unless (convertible sig src tx) (Left ())
    pure (subst x dst)
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
  Def _ i -> pure (fst (fst sig ! i))
  Ind _ i -> pure (arity (snd sig ! i))
  Rec _ i -> pure (elimTy (snd sig ! i))
  Con _ i j -> pure (ctors (snd sig ! i) !! j)

unrollPi (Pi _ _ dst) = 1 + unrollPi dst
unrollPi _ = 0

occurs :: Int -> Term -> Bool
occurs k t = f k t False where
  f k (Var n) acc
    | n == k = True
    | otherwise = acc
  f k t acc = Core.fold (const (+1)) k f t acc

-- return True if occurs strictly positively, False if not occurs, error if occurs non-strictly positively
checkPositive :: Int -> Term -> Either Error Bool
checkPositive k (Pi _ src dst)
  | occurs k src = Left ()
  | otherwise = checkPositive (k + 1) dst
checkPositive k t =
  let (fun,args) = unrollApp t in
  if any (occurs k) args
  then Left ()
  else case fun of
    Var m -> pure (m == k)
    _ -> False

-- check strict positivity of constructor and return indices of recursive subdata
checkCtor :: Int -> Term -> Either Error [Bool]
checkCtor k (Pi _ src dst) = (:) <$> checkPositive k src <*> checkCtor (k + 1) dst
checkCtor k t = case unrollApp t of
  (Var m, args) -> 
    if m == k && not (any (occurs k) args)
    then pure []
    else Left ()
  _ -> Left ()

motiveTy :: Int -> Term -> Term
motiveTy ino iref = f [] where
  f ctx (Pi n src dst) = Pi n src (f ((n,src):ctx) dst)
  f ctx t = Pi "_" (mkApp iref (reverse [0 .. ino - 1])) Type

{-
  compute branch type:
  - traverse constructor type
  - for each subdatum, if recursive compute rectype
  - pi-abstract over rectypes
  - compute indices of applied ctor
  - return motive applied to indices and applied ctor

  It might be useful to compute the indices of recursive subdata in the positivity check
  If a subdatum has a recurrence, it is in the head of an app of the codomain of a nested pi.
  the type of the recursive call will abstract over the same function arguments and return the
  motive, applied to local indices and the subdatum applied to these arguments

  separating checking and construction saves work if a check fails;
  the check is already functional in the abstract constructor types

  so : typecheck >> poscheck >> instantiate >> compute branchty >> compute rule?
-}
branchTy :: Int -> Term -> Term
branchTy motive t = f motive t [] where
  f k (Pi _ src dst) recs

checkInductive :: Signature -> String -> Term -> [(String,Term)] -> Int -> Either Error Datatype
checkInductive sig name arity ctors block = do
  k <- infer sig [] arity
  unless (convertible sig k Kind) (Left ())
  let ino = unrollPi arity
      iref = Ind name block
      (ctornames,ctortys) = unzip ctors
  mapM_ (infer sig [(name,arity)]) ctortys
  mapM_ (checkCtor 0) ctortys
  let ctortys' = fmap (subst iref) ctortys
      motiveType = motiveTy ino iref
  undefined

  {-

    compute elimTy
      
      branches
    compute elimRules

    special case for empty type?


  -}