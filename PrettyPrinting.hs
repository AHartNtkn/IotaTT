module PrettyPrinting where

import Data.Char

import Exp.ErrM
import AbstractSyntax

char :: Int -> String
char i = [chr (i + 97)]

parenA :: Int -> ATerm -> String
parenA i a@AApp{} = "(" ++ printA i a ++ ")"
parenA i a@AAppi{} = "(" ++ printA i a ++ ")"
parenA i a@ARho{} = "(" ++ printA i a ++ ")"
parenA i a@APi{} = "(" ++ printA i a ++ ")"
parenA i a@AIPi{} = "(" ++ printA i a ++ ")"
parenA i a@AIota{} = "(" ++ printA i a ++ ")"
parenA i a@AId{} = "(" ++ printA i a ++ ")"
parenA i a@AAnn{} = "(" ++ printA i a ++ ")"
parenA i a@ALam{} = "(" ++ printA i a ++ ")"
parenA i a@ALAM{} = "(" ++ printA i a ++ ")"
parenA i a = printA i a

printA :: Int -> ATerm -> String
printA i (AVS s) = s
printA i (AV n) = char (i - n - 1)
printA i (AAnn a b) = printA i a ++ " : " ++ parenA i b
printA i (AApp a b) = printA i a ++ " " ++ parenA i b
printA i (AAppi a b) = printA i a ++ " - " ++ parenA i b
printA i (ALam a) = "\\" ++ char i ++ " . " ++ printA (1 + i) a
printA i (ALAM a) = "/" ++ char i ++ " . " ++ printA (1 + i) a
printA i (AIPair a b) = "[" ++ printA i a ++ " | " ++ printA i b ++ "]"
printA i (AFst a) = parenA i a ++ ".1"
printA i (ASnd a) = parenA i a ++ ".2"
printA i ABeta = "B"
printA i (ARho a t b) = "r(" ++ char i ++ " . " ++ printA (1 + i) t ++ ") " ++ parenA i a ++ " . " ++ printA i b
printA i (AIota a b) = "i(" ++ char i ++ " : " ++ printA i a ++ ") . " ++ printA (1 + i) b
printA i (AId a b) = printA i a ++ " ~ " ++ printA i b
printA i (APi a b) =
  if freeIn b 0
  then "(" ++ char i ++ " : " ++ printA i a ++ ") -> " ++ printA (1 + i) b
  else parenA i a ++ " -> " ++ printA (1 + i) b
printA i (AIPi a b) = "{" ++ char i ++ " : " ++ printA i a ++ "} -> " ++ printA (1 + i) b
printA i AStar = "*"

parenD :: Int -> Term -> String
parenD i a@App{} = "(" ++ printD i a ++ ")"
parenD i a@Pi{} = "(" ++ printD i a ++ ")"
parenD i a@IPi{} = "(" ++ printD i a ++ ")"
parenD i a@Lam{} = "(" ++ printD i a ++ ")"
parenD i a@Iota{} = "(" ++ printD i a ++ ")"
parenD i a = printD i a

freeIndb (V x) n       = x == n
freeIndb (Lam d) n     = freeIndb d (1 + n)
freeIndb (App d d1) n  = freeIndb d n || freeIndb d1 n
freeIndb (Pi t tp) n   = freeIndb t n || freeIndb tp (1 + n)
freeIndb (IPi t tp) n  = freeIndb t n || freeIndb tp (1 + n)
freeIndb (Iota t tp) n = freeIndb t n || freeIndb tp (1 + n)
freeIndb (Id x y)    n = freeIndb x n || freeIndb y n
freeIndb Star n        = False

printD :: Int -> Term -> String
printD i (V n) = char (i - n - 1)
printD i (App a b) = printD i a ++ " " ++ parenD i b
printD i (Lam a) = "\\" ++ char i ++ " . " ++ printD (1 + i) a
printD i (Pi a b) =
  if freeIndb b 0
  then "(" ++ char i ++ " : " ++ printD i a ++ ") -> " ++ printD (1 + i) b
  else parenD i a ++ " -> " ++ printD (1 + i) b
printD i (IPi a b) = "{" ++ char i ++ " : " ++ printD i a ++ "} -> " ++ printD (1 + i) b
printD i (Id a b) = printD i a ++ " ~ " ++ printD i b
printD i (Iota a b) = "i(" ++ char i ++ " : " ++ printD i a ++ ") . " ++ printD (1 + i) b
printD i Star = "*"

instance Show Term where
  show = printD 0
{-
instance Show ATerm where
  show = printA 0
-}
