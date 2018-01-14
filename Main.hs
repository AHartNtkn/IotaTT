module Main where

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM

import System.IO
import Control.Monad
import Data.Char(ord,chr)
import System.Environment
import qualified Data.Map.Strict as Map
import Control.Monad.Reader hiding (liftIO)
import Control.Monad.State hiding (liftIO)
import Control.Monad.Except hiding (liftIO)
import Control.Monad.Trans.Except hiding (liftIO)

import AbstractSyntax
import TypeChecker
import PrettyPrinting
import RawSyntax

-- =*=*=*=*=*=*=*=* Boilerplate *=*=*=*=*=*=*=*=*=

errPr :: Err a -> Proof a
errPr e = case e of
  Bad e -> proofError e
  Ok e -> return e

-- =*=*=*=*=*=*=*=* Language Data *=*=*=*=*=*=*=*=*=

extention = ".itt"

endQ :: String -> Bool
endQ s = extention == reverse (take (length extention) (reverse s))

-- =*=*=*=*=*=*=*=* Declarations *=*=*=*=*=*=*=*=*=

-- Process out where clause
whereToExp :: ExpWhere -> Exp
whereToExp (Where e dl) = SLet dl e
whereToExp (NoWhere e) = e

-- Add a declaration to a context
addDecl :: Decl -> Proof ()
addDecl (DeclDef (AIdent defId) retTy eWhere) = do
    tr <- convert (whereToExp eWhere)
    ty <- convert retTy
    check tr ty
    tbl <- get
    put $ Map.insert defId (tr , ty) tbl

-- Add a list of declarations to a context
addDecls :: [Decl] -> Proof ()
addDecls [] = return ()
addDecls (d@(DeclDef (AIdent s) _ _):dl) = do
  liftIO $ putStrLn ("Checking " ++ s)
  addDecl d
  addDecls dl
  
-- Given a context and a file, import the file to the context
fileToCtx :: String -> Proof ()
fileToCtx f = do
  fileContents <- liftIO $ readFile f
  case (pModule . resolveLayout True . myLexer) fileContents of
    Bad s -> liftIO $ putStrLn s -- If the file fails to parse, return an empty context
    Ok m -> moduleToCtx m

-- Given a module with imports, combine all into a single context
moduleToCtx :: Module -> Proof ()
moduleToCtx (Module _ [] decl) = addDecls decl
moduleToCtx (Module a (Import (AIdent s):im) decl) = do
  sctx <- if endQ s then fileToCtx s else fileToCtx (s++extention)
  moduleToCtx (Module a im decl)

-- =*=*=*=*=*=*=*=* REPL / Main loop *=*=*=*=*=*=*=*=*=
-- NOTE: pExp :: [Token] -> Err Exp

-- Repl Loop
mainLoop :: String -> Proof ()
mainLoop s = (do
  liftIO $ putStr "> "
  input <- liftIO getLine -- Print prompt and get user input
  case input of -- REPL commands
    ":q"   -> return () -- Quit with ":q"
    ":con" -> do
        tbl <- get
        liftIO $ putStrLn (show tbl)
        mainLoop s -- print everything in the current context
    ":h"   -> do
           liftIO $ putStrLn (
                 "<Expression> - Evaluate an expression.\n"++
                 ":a <Expression> - Print the (unevaluated) AST for an expression.\n"++
                 ":con - Print current context (for debugging)\n"++
                 ":e <Expression> - Print the erased form of an expression.\n"++
                 ":h - Help (list of commands)\n"++
                 ":q - Quit\n:r - Reload file\n"++
                 ":t <Expression> - Check the type of an expression\n")
           mainLoop s -- help command
    ':':'t':' ':l -> do
       catchError
         (errPr (pExp . resolveLayout True . myLexer $ l) >>= convert >>= infer >>= liftIO . putStrLn . pshowA)
         (\_ -> return ())
       mainLoop s
    ':':'a':' ':l -> do
       catchError
         (errPr ((pExp . resolveLayout True . myLexer) l) >>= convert >>= liftIO . putStrLn . show)
         (\_ -> return ())
       mainLoop s
    ':':'e':' ':l -> do
       catchError
         (errPr ((pExp . resolveLayout True . myLexer) l) >>= convert >>= nf >>= erase >>= liftIO . putStrLn . pshowU)
         (\_ -> return ())
       mainLoop s
    ":r"   -> put Map.empty >> fileToCtx s >> mainLoop s
    _  -> do
       catchError
         (errPr ((pExp . resolveLayout True . myLexer) input) >>= convert >>= nf >>= liftIO . putStrLn . pshowA)
         (\_ -> return ())
       mainLoop s
    ) `catchError` (\_ -> do
      liftIO $ putStrLn "Restarting with empty context. Enter \":r\" to reload from file."
      mainLoop s
      )

-- Main program
main :: IO String
main = do
  hSetBuffering stdout NoBuffering
  name <- getArgs
  runProof (do
    liftIO $ hSetBuffering stdout NoBuffering
    liftIO $ putStrLn "Starting..."
    fileToCtx (head name) `catchError` (\_ -> do
      put Map.empty
      liftIO $ putStrLn "Restarting with empty context. Enter \":r\" to reload from file." )
    mainLoop $ head name)
  return "Goodbye!"
