module PrettyPrinting where

import Data.Char

import ErrM
import AbstractSyntax

char :: Int -> String
char i = chr (i + 97) : []

parenA :: Int -> ATerm -> String
parenA i a@(AApp _ _) = "(" ++ printA i a ++ ")"
parenA i a@(AAppi _ _) = "(" ++ printA i a ++ ")"
parenA i a@(ARho _ _ _) = "(" ++ printA i a ++ ")"
parenA i a@(APi _ _) = "(" ++ printA i a ++ ")"
parenA i a@(AIPi _ _) = "(" ++ printA i a ++ ")"
parenA i a@(AIota _ _) = "(" ++ printA i a ++ ")"
parenA i a@(AId _ _) = "(" ++ printA i a ++ ")"
parenA i a@(AAnn _ _) = "(" ++ printA i a ++ ")"
parenA i a = printA i a

printA :: Int -> ATerm -> String
printA i (AV n) = char (i - n - 1)
printA i (AAnn a b) = printA i a ++ " : " ++ parenA i b
printA i (AApp a b) = printA i a ++ " " ++ parenA i b
printA i (AAppi a b) = printA i a ++ " - " ++ parenA i b
printA i (ALam a) = "\\" ++ char i ++ " -> " ++ printA (1 + i) a
printA i (ALAM a) = "/" ++ char i ++ " -> " ++ printA (1 + i) a
printA i (AIPair a b) = "[" ++ printA i a ++ " | " ++ printA i b ++ "]"
printA i (AFst a) = parenA i a ++ ".1"
printA i (ASnd a) = parenA i a ++ ".2"
printA i ABeta = "Beta"
printA i (ARho a t b) = "r(" ++ char i ++ " : " ++ printA (1 + i) t ++ ") " ++ printA i a ++ " . " ++ printA i b
printA i (AIota a b) = "i(" ++ char i ++ " : " ++ printA i a ++ ") . " ++ printA (1 + i) b 
printA i (AId a b) = printA i a ++ " ~ " ++ printA i b
printA i (APi a b) =
  if freeIn b 0
  then "(" ++ char i ++ " : " ++ printA i a ++ ") -> " ++ printA (1 + i) b
  else parenA i a ++ " -> " ++ printA (1 + i) b
printA i (AIPi a b) = "{" ++ char i ++ " : " ++ printA i a ++ "} -> " ++ printA (1 + i) b
printA i AStar = "*"

parenD :: Int -> Term -> String
parenD i a@(App _ _) = "(" ++ printD i a ++ ")"
parenD i a@(Pi _ _) = "(" ++ printD i a ++ ")"
parenD i a@(IPi _ _) = "(" ++ printD i a ++ ")"
parenD i a = printD i a

printD :: Int -> Term -> String
printD i (V n) = char (i - n - 1)
printD i (App a b) = printD i a ++ " " ++ parenD i b
printD i (Lam a) = "\\" ++ char i ++ " -> " ++ printD (1 + i) a
printD i (Pi a b) =
  if freeIn b 0
  then "(" ++ char i ++ " : " ++ printD i a ++ ") -> " ++ printD (1 + i) b
  else parenD i a ++ " -> " ++ printD (1 + i) b
printD i (IPi a b) = "{" ++ char i ++ " : " ++ printD i a ++ "} -> " ++ printD (1 + i) b
printD i Star = "*"

instance Show Term where 
  show = printD 0
{-
instance Show ATerm where 
  show = printA 0
-}