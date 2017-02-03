{-# language LambdaCase #-}

module Main where

import AbsExp
import ParExp
import LexExp
import SkelExp
import PrintExp
import LayoutExp
import ErrM

import System.IO
import Control.Monad
import Data.Char(ord,chr)
import System.Environment

import AbstractSyntax
import TypeChecker
import PrettyPrinting
import RawSyntax

-- =*=*=*=*=*=*=*=* Language Data *=*=*=*=*=*=*=*=*=

extention = ".itt"

endQ :: String -> Bool
endQ s = extention == reverse (take (length extention) (reverse s))

-- =*=*=*=*=*=*=*=* Declarations *=*=*=*=*=*=*=*=*=

-- Proccess out where clause
whereToExp :: ExpWhere -> Exp
whereToExp (Where e dl) = SLet dl e
whereToExp (NoWhere e) = e

-- Add a declaration to a context
addDecl :: TopCtx -> Decl -> Err TopCtx
addDecl ctx (DeclDef (AIdent defId) retTy eWhere) =
    convert ctx (whereToExp eWhere) >>= \ty ->
    convert ctx retTy >>= \ki ->
    check ctx Empty ty ki >>
    Ok ((defId , (ty , ki)) : ctx)

-- Add a list of declarations to a context
addDecls :: TopCtx -> [Decl] -> IO TopCtx
addDecls ctx [] = pure ctx
addDecls ctx (d@(DeclDef (AIdent s) _ _):dl) = case addDecl ctx d of
  -- If declaration adding failed, print error and return an empty context
  Bad e -> putStrLn e >> putStrLn ("Failed at adding definition: "++s) >> return []
  Ok ctx' -> putStrLn ("Checked: "++s) >> addDecls ctx' dl

-- Given a context and a file, import the file to the context
fileToCtx :: TopCtx -> String -> IO TopCtx
fileToCtx ctx f = do
  fileContents <- readFile f
  case (pModule . resolveLayout True . myLexer) fileContents of
    Bad s -> putStrLn s >> return [] -- If the file fails to parse, return an empty context
    Ok m -> moduleToCtx ctx m

-- Given a module with imports, combine all into a single context
moduleToCtx :: TopCtx -> Module -> IO TopCtx
moduleToCtx ctx (Module _ [] decl) = addDecls ctx decl
moduleToCtx ctx (Module a (Import (AIdent s):im) decl) = do
  sctx <- if endQ s then fileToCtx ctx s else fileToCtx ctx (s++extention)
  moduleToCtx (ctx ++ sctx) (Module a im decl)

-- =*=*=*=*=*=*=*=* REPL / Main loop *=*=*=*=*=*=*=*=*=

-- Print the content of a context, for debuging
prCtx :: TopCtx -> String
prCtx [] = ""
prCtx ((s , v):vs) = s ++ " : " ++ show v ++ "\n" ++ prCtx vs

-- Evaluate expression from user input
-- NOTE: pExp :: [Token] -> Err Exp
evaluateInput :: TopCtx -> String -> Err Term
evaluateInput ctx input =
  -- process user input into an expression
  (pExp . resolveLayout True . myLexer) input >>=
  convert ctx >>= normalize ctx >>= erase ctx

-- When needed, print contents of an Error
errIO :: Err Term -> IO ()
errIO (Bad s) = putStrLn s
errIO (Ok a)  = putStrLn $ show a

errIOT :: Err ATerm -> IO ()
errIOT (Bad s) = putStrLn s
errIOT (Ok a)  = putStrLn $ show a

-- Repl Loop
mainLoop :: String -> TopCtx -> IO String
mainLoop s ctx =
  putStr "> " >> getLine >>= \ input -> -- Print prompt and get user input
  case input of -- REPL commands
    ":q"   -> return "Goodbye!" -- Quit with ":q"
    ":con" -> putStrLn (prCtx ctx) >> mainLoop s ctx -- print everything in the current context
    ":h"   -> putStrLn (
                 ":h - Help (list of commands)\n"++
                 ":con - Print current context\n"++
                 ":q - Quit\n:r - Reload file\n"++
                 ":t <Expression> - Check the type of an expression\n"
           ) >> mainLoop s ctx -- help command
    ":r"   -> fileToCtx [] s >>= mainLoop s
    ':':'t':' ':l ->
      errIOT (
        (pExp . resolveLayout True . myLexer) l >>=
        convert ctx >>=
        infer ctx Empty) >>
      mainLoop s ctx
    _      -> errIO (evaluateInput ctx input) >> mainLoop s ctx -- Loop back with same context

-- Main program
main :: IO String
main = do
  hSetBuffering stdout NoBuffering
  name <- getArgs
  ctx <- fileToCtx [] $ head name
  mainLoop (head name) ctx
