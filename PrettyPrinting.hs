module PrettyPrinting where

import Data.Char

import ErrM
import AbstractSyntax

char :: Int -> String
char i = chr (i + 97) : []

parenA :: Int -> ADB -> String
parenA i a@(AAppj _ _) = "(" ++ printA i a ++ ")"
parenA i a@(Apptj _ _) = "(" ++ printA i a ++ ")"
parenA i a@(Appi _ _) = "(" ++ printA i a ++ ")"
parenA i a@(Rho _ _ _) = "(" ++ printA i a ++ ")"
parenA i a = printA i a

printA :: Int -> ADB -> String
printA i (AVj n) = char (i - n - 1)
printA i (AAppj a b) = printA i a ++ " " ++ parenA i b
printA i (Apptj a b) = printA i a ++ " . " ++ parenT i b
printA i (Appi a b) = printA i a ++ " - " ++ parenA i b
printA i (ALamj a) = "\\" ++ char i ++ " -> " ++ printA (1 + i) a
printA i (LAMj a) = "\\\\" ++ char i ++ " -> " ++ printA (1 + i) a
printA i (LAMt a) = "/\\" ++ char i ++ " -> " ++ printA (1 + i) a
printA i (IPair a b) = "[" ++ printA i a ++ " , " ++ printA i b ++ "]"
printA i (Fst a) = parenA i a ++ ".1"
printA i (Snd a) = parenA i a ++ ".2"
printA i Beta = "Beta"
printA i (Rho a t b) = "r " ++ printA i a ++ " - (" ++ char i ++ " : " ++ printT (1 + i) t ++ ") - " ++ printA i b

parenT :: Int -> AType -> String
parenT i a@(AAllk _ _) = "(" ++ printT i a ++ ")"
parenT i a@(APit _ _) = "(" ++ printT i a ++ ")"
parenT i a@(AAllt _ _) = "(" ++ printT i a ++ ")"
parenT i a@(AIota _ _) = "(" ++ printT i a ++ ")"
parenT i a@(AId _ _) = "(" ++ printT i a ++ ")"
parenT i a@(ALamt _ _) = "(" ++ printT i a ++ ")"
parenT i a@(ALAMk _ _) = "(" ++ printT i a ++ ")"
parenT i a@(AAppk _ _) = "(" ++ printT i a ++ ")"
parenT i a = printT i a

printT :: Int -> AType -> String
printT i (AVt n) = char (i - n - 1)
printT i (APit a b) =
  if freeIn b 0
  then "(" ++ char i ++ " : " ++ printT i a ++ ") -> " ++ printT (1 + i) b
  else parenT i a ++ " -> " ++ printT (1 + i) b
printT i (AAllk a b) = "A(" ++ char i ++ " : " ++ printK i a ++ ") . " ++ printT (1 + i) b
printT i (ALamt a b) = "\\(" ++ char i ++ " : " ++ printT i a ++ ") . " ++ printT (1 + i) b
printT i (ALAMk a b) = "V (" ++ char i ++ " : " ++ printK i a ++ ") . " ++ printT (1 + i) b
printT i (AAppt a b) = printT i a ++ " " ++ parenA i b
printT i (AAppk a b) = printT i a ++ " + " ++ parenT i b
printT i (AAllt a b) = "{" ++ char i ++ " : " ++ printT i a ++ "} -> " ++ printT (1 + i) b
printT i (AIota a b) = "i(" ++ char i ++ " : " ++ printT i a ++ ") . " ++ printT (1 + i) b 
printT i (AId a b) = printA i a ++ " ~ " ++ printA i b

parenK :: Int -> AKind -> String
parenK i a@(APik _ _) = "(" ++ printK i a ++ ")"
parenK i a = printK i a

printK :: Int -> AKind -> String
printK i AStar = "*"
printK i (APik a b) =
  if freeIn b 0
  then "(" ++ char i ++ " : " ++ printT i a ++ ") -> " ++ printK (1 + i) b
  else parenT i a ++ " -> " ++ printK (1 + i) b
printK i (AAlltk a b) = "A (" ++ char i ++ " : " ++ printK i a ++ ") . " ++ printK (1 + i) b


parenD :: Int -> DB -> String
parenD i a@(Appj _ _) = "(" ++ printD i a ++ ")"
parenD i a = printD i a

printD :: Int -> DB -> String
printD i (Vj n) = char (i - n - 1)
printD i (Appj a b) = printD i a ++ " " ++ parenD i b
printD i (Lamj a) = "\\" ++ char i ++ " -> " ++ printD (1 + i) a

instance Show DB where 
  show = printD 0
{-
instance Show ADB where 
  show = printA 0

instance Show AType where 
  show = printT 0

instance Show AKind where 
  show = printK 0
-}