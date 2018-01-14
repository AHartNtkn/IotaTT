module PrettyPrinting where

import AbstractSyntax

parenA :: ATerm -> String
parenA a@AApp{} = "(" ++ pshowA a ++ ")"
parenA a@AAppi{} = "(" ++ pshowA a ++ ")"
parenA a@ARho{} = "(" ++ pshowA a ++ ")"
parenA a@APi{} = "(" ++ pshowA a ++ ")"
parenA a@AIPi{} = "(" ++ pshowA a ++ ")"
parenA a@AIota{} = "(" ++ pshowA a ++ ")"
parenA a@AId{} = "(" ++ pshowA a ++ ")"
parenA a@AAnn{} = "(" ++ pshowA a ++ ")"
parenA a@ALam{} = "(" ++ pshowA a ++ ")"
parenA a@ALAM{} = "(" ++ pshowA a ++ ")"
parenA a = pshowA a

pshowA :: ATerm -> String
pshowA (AVS s) = s
pshowA (AV s n) = s
pshowA (AAnn a b) = pshowA a ++ " : " ++ parenA b
pshowA (AApp a b) = pshowA a ++ " " ++ parenA b
pshowA (AAppi a b) = pshowA a ++ " - " ++ parenA b
pshowA (ALam st a) = "\\" ++ st ++ " . " ++ pshowA a
pshowA (ALAM st a) = "/" ++ st ++ " . " ++ pshowA a
pshowA (AIPair a b) = "[" ++ pshowA a ++ " | " ++ pshowA b ++ "]"
pshowA (AFst a) = parenA a ++ ".1"
pshowA (ASnd a) = parenA a ++ ".2"
pshowA ABeta = "B"
pshowA (ARho st a t b) = "r(" ++ st ++ " . " ++ pshowA t ++ ") " ++ parenA a ++ " . " ++ pshowA b
pshowA (AIota st a b) = "i(" ++ st ++ " : " ++ pshowA a ++ ") . " ++ pshowA b
pshowA (AId a b) = pshowA a ++ " ~ " ++ pshowA b
pshowA (APi st a b) =
  if freeIn b 0
  then "(" ++ st ++ " : " ++ pshowA a ++ ") -> " ++ pshowA b
  else parenA a ++ " -> " ++ pshowA b
pshowA (AIPi st a b) = "{" ++ st ++ " : " ++ pshowA a ++ "} -> " ++ pshowA b
pshowA (AU l) = "U[" ++ show l ++ "]"

parenD :: Term -> String
parenD a@App{} = "(" ++ pshowU a ++ ")"
parenD a@Pi{} = "(" ++ pshowU a ++ ")"
parenD a@IPi{} = "(" ++ pshowU a ++ ")"
parenD a@Lam{} = "(" ++ pshowU a ++ ")"
parenD a@Iota{} = "(" ++ pshowU a ++ ")"
parenD a = pshowU a

freeIndb (V s x)        n = x == n
freeIndb (Lam st d)     n = freeIndb d (1 + n)
freeIndb (App d d1)     n = freeIndb d n || freeIndb d1 n
freeIndb (Pi st t tp)   n = freeIndb t n || freeIndb tp (1 + n)
freeIndb (IPi st t tp)  n = freeIndb t n || freeIndb tp (1 + n)
freeIndb (Iota st t tp) n = freeIndb t n || freeIndb tp (1 + n)
freeIndb (Id x y)       n = freeIndb x n || freeIndb y n
freeIndb (U _)          n = False

pshowU :: Term -> String
pshowU (V s n) = s
pshowU (App a b) = pshowU a ++ " " ++ parenD b
pshowU (Lam st a) = "\\" ++ st  ++ " . " ++ pshowU a
pshowU (Pi st a b) =
  if freeIndb b 0
  then "(" ++ st ++ " : " ++ pshowU a ++ ") -> " ++ pshowU b
  else parenD a ++ " -> " ++ pshowU b
pshowU (IPi st a b) = "{" ++ st ++ " : " ++ pshowU a ++ "} -> " ++ pshowU b
pshowU (Id a b) = pshowU a ++ " ~ " ++ pshowU b
pshowU (Iota st a b) = "i(" ++ st ++ " : " ++ pshowU a ++ ") . " ++ pshowU b
pshowU (U l) = "U[" ++ show l ++ "]"

