module Main where

import Parser
import Prettyprint as P
import Core
import System.Environment 
import Control.Monad.RWS
import Control.Monad.State.Lazy as S
import Debug.Trace

main :: IO ()
main = getArgs >>= openFiles >>= checkFiles where

  openFiles :: [String] -> IO [(String,String)]
  openFiles = mapM (\name -> do file <- readFile name; pure (name,file))

  checkFiles :: [(String,String)] -> IO ()
  checkFiles files = case mapM (uncurry parse) files of
    Left err -> putStrLn err    
    Right result -> putStrLn (checkModules result)
  
  checkModules :: [[Decl]] -> String
  checkModules decls = case execStateT (mapM_ checkDecl (concat decls)) mempty of
    Left err -> showError err
    Right (defs,rules) -> "\nok"
  
  checkDecl :: Decl -> StateT Signature (Either Error) ()
  checkDecl (Data name arity ctors) = checkInductive name arity ctors
  checkDecl (Func name body) = checkDefinition name body
  checkDecl (Axiom name ty) = do
    sig <- get
    S.lift $ infer sig [] ty
    insertName name ty
  checkDecl (Print term) = do
    sig <- get
    ty <- S.lift $ infer sig [] term
    let nf = whnf sig term
    let tnf = whnf sig ty
    traceM $ P.showTerm [] nf ++ "\n: " ++ P.showTerm [] tnf ++ "\n"
    
