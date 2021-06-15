module Prettyprint where

import Core (Term(..),Error(..),Context,unrollApp)

import Data.List as L
import Data.Map as M
import Control.Monad.RWS

dbiName :: Int -> Context -> String
dbiName n ctx = f n ctx where
  f m [] = '$' : show n
  f 0 (("",_):ctx) = '$' : show n
  f 0 ((name,_) : ctx) = name
  f m (_ : ctx) = f (m - 1) ctx

embrace :: String -> String
embrace x = '(' : x ++ ")"

bracePi :: Term -> String -> String
bracePi Pi {} = embrace
bracePi _     = id

braceApp :: Term -> String -> String
braceApp App {}  = embrace
braceApp Lam {}  = embrace
braceApp Pi {}   = embrace
braceApp _       = id

showArg :: Context -> Term -> String
showArg ctx t = braceApp t (showTerm ctx t)

showLam :: Context -> String -> Term -> String
showLam ctx acc (Lam name ta tb) = showLam ((name,ta):ctx) (acc ++ showDomain ctx name ta) tb
showLam ctx acc tb = "\\" ++ acc ++ ", " ++ showTerm ctx tb

showPi :: Context -> String -> Term -> String
showPi ctx acc (Pi name ta tb) = showPi ((name,ta):ctx) (acc ++ showDomain ctx name ta) tb
showPi ctx acc tb = "Pi " ++ acc ++ ", " ++ showTerm ctx tb

showDomain :: Context -> String -> Term -> String
showDomain ctx n t
  | Prelude.null n = "(_ : " ++ showTerm ctx t ++ ")"
  | otherwise = "(" ++ n ++ " : " ++ showTerm ctx t ++ ")"

showTerm :: Context -> Term -> String
showTerm ctx Type         = "Type"
showTerm ctx Kind         = "Kind"
showTerm ctx (Var n)      = dbiName n ctx
showTerm ctx (Def s)      = s
showTerm ctx app @ App {} = unwords (fmap (showArg ctx) (f : reverse xs)) where (f,xs) = unrollApp app
showTerm ctx pi  @ Pi {}  = showPi ctx [] pi
showTerm ctx lam @ Lam {} = showLam ctx [] lam

showContext :: Context -> String
showContext [] = ""
showContext ((name,ty):ctx) = showContext ctx ++ name ++ " : " ++ showTerm ctx ty ++ "\n"

showSignature :: Map String Term -> String
showSignature = unlines . fmap (\(name,ty) -> name ++ " : " ++ showTerm [] ty) . toList

showError :: Error -> String
showError e = case e of
  ExpectedSort ctx t -> "in context:\n" ++ showContext ctx ++ "expected a sort, but got:\n" ++ showTerm ctx t
  ExpectedFunction ctx t -> "in context:\n" ++ showContext ctx ++ "expected a function, but got a term of type:\n" ++ showTerm ctx t
  ExpectedType ctx expected term ty -> "in context:\n" ++ showContext ctx ++ "Type error:\ngot term:\n" ++ showTerm ctx term ++ "\nof type:\n" ++ showTerm ctx ty ++ "\nbut expected a term of type:\n" ++ showTerm ctx expected
  NameNotDefined name -> "undefined name: " ++ name
  NameAlreadyDefined name -> "name was already defined: " ++ name
  IllFormedTypeConstructor name -> "type constructor " ++ name ++ " is ill-formed"
  IllFormedDataConstructor name -> "data constructor " ++ name ++ " is ill-formed"
  OccurrenceInIndex name -> "datatype " ++ name ++ " occurs in an illegal index"
  NegativeOccurrence name -> "datatype " ++ name ++ " occurs negatively in its constructor"

