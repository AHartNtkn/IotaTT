{-# language MultiParamTypeClasses #-}

module AbstractSyntax where

{- Unannotated deBrujin Lambda Terms -}
class DeBruijin a where
  -- Check if a variable occures free in a term
  freeIn :: a -> Int -> Bool
  -- Increment free variables
  incFree :: a -> Int -> Int -> a

-- A type class for substitutions
class DeBruijin b => Substitute a b where
  sub :: a -> Int -> b -> b

-- A type class for normalizable entitites
class Norm a where
  -- Single Step Evaluation
  ssEval :: a -> a
  -- Superdevelopment
  sdev :: a -> a

normalize :: (Eq a, Norm a) => a -> a
normalize d = let r = sdev d in if d == r then r else normalize r  

{- Unannotated Terms -}
data Term
  = V Int
  | Lam Term
  | App Term Term
  | Pi Term Term
  | IPi Term Term
  | Iota Term Term
  | Id Term Term
  | Star
  deriving (Eq)

instance DeBruijin Term where
  freeIn (V x) n       = x == n 
  freeIn (Lam d) n     = freeIn d (1 + n)
  freeIn (App d d1) n  = freeIn d n || freeIn d1 n
  freeIn (Pi t tp) n   = freeIn t n || freeIn tp (1 + n)
  freeIn (IPi t tp) n   = freeIn t n || freeIn tp (1 + n)
  freeIn (Iota t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (Id x y)    n = freeIn x n || freeIn y n
  freeIn Star n        = False

  incFree (V x) n i       = if x >= n then V (i + x) else V x
  incFree (Lam d) n i     = Lam (incFree d (1 + n) i)
  incFree (App d1 d2) n i = App (incFree d1 n i) (incFree d2 n i)
  incFree (Pi t tp) n i   = Pi (incFree t n i) (incFree tp (1 + n) i)
  incFree (IPi t tp) n i  = IPi (incFree t n i) (incFree tp (1 + n) i)
  incFree (Iota t tp) n i = Iota (incFree t n i) (incFree tp (1 + n) i)
  incFree (Id x y) n i    = Id (incFree x n i) (incFree y n i)
  incFree Star n i        = Star

instance Substitute Term Term where
  sub s n (V x) =
    if x >= n then (if x == n
          then s           -- if n = x, return s
          else V (x - 1))  -- if n < x, Ex y . suc y = x; return y
    else V x               -- if Vj x isn't free, do nothing
  sub s n (Lam d)     = Lam (sub (incFree s 0 1) (1 + n) d)
  sub s n (App d1 d2) = App (sub s n d1) (sub s n d2)
  sub s n (Pi t tp)   = Pi (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (IPi t tp)  = IPi (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Iota t tp) = Iota (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Id x y)    = Id (sub s n x) (sub s n y)
  sub s n Star = Star

instance Norm Term where
  ssEval (App (Lam d) s) = sub s 0 d -- beta-reduction
  ssEval (Lam (App d (V 0))) =
    if freeIn d 0
    then Lam (App d (V 0))
    else sub (Lam (V 0)) 0 d -- eta-reduction
  ssEval d = d

  sdev (Lam d) = ssEval (Lam (sdev d))
  sdev (V x) = V x
  sdev (App d d1) = ssEval (App (sdev d) (sdev d1))
  sdev (Pi t tp)  = Pi (sdev t) (sdev tp)
  sdev (IPi t tp)  = IPi (sdev t) (sdev tp)
  sdev (Iota t tp) = Iota (sdev t) (sdev tp)
  sdev (Id x y)    = Id (sdev x) (sdev y)
  sdev Star = Star

{- Annotated Types -}
data ATerm
         = AV Int
         | ALam ATerm
         | AAnn ATerm ATerm
         | AApp ATerm ATerm
         | ALAM ATerm 
         | AAppi ATerm ATerm
         | AIPair ATerm ATerm
         | AFst ATerm
         | ASnd ATerm
         | ABeta 
         | ARho ATerm ATerm ATerm
         | APi ATerm ATerm
         | AIPi ATerm ATerm
         | AIota ATerm ATerm
         | AId ATerm ATerm
         | AStar
         deriving (Eq , Show)

instance DeBruijin ATerm where
  freeIn (AV x)        n = x == n 
  freeIn (ALam d)      n = freeIn d (1 + n)
  freeIn (AAnn d d1)   n = freeIn d n || freeIn d1 n
  freeIn (AApp d d1)   n = freeIn d n || freeIn d1 n
  freeIn (ALAM d)      n = freeIn d (1 + n)
  freeIn (AAppi d d1)  n = freeIn d n || freeIn d1 n
  freeIn (AIPair d d1) n = freeIn d n || freeIn d1 n
  freeIn (AFst d)      n = freeIn d n
  freeIn (ASnd d)      n = freeIn d n
  freeIn ABeta         n = False
  freeIn (ARho d tp b) n = freeIn d n || freeIn tp (1 + n) || freeIn b n
  freeIn (APi t tp)    n = freeIn t n || freeIn tp (1 + n)
  freeIn (AIPi t tp)   n = freeIn t n || freeIn tp (1 + n)
  freeIn (AIota t tp)  n = freeIn t n || freeIn tp (1 + n)
  freeIn (AId x y)     n = freeIn x n || freeIn y n
  freeIn AStar n = False

  incFree (AV x)       n i = if x >= n then AV (i + x) else AV x
  incFree (ALam d)     n i = ALam (incFree d (1 + n) i)
  incFree (AAnn d b)   n i = AAnn (incFree d n i) (incFree b n i)
  incFree (AApp d b)   n i = AApp (incFree d n i) (incFree b n i)
  incFree (ALAM d)     n i = ALAM (incFree d (1 + n) i)
  incFree (AAppi d b)  n i = AAppi (incFree d n i) (incFree b n i)
  incFree (AIPair d b) n i = AIPair (incFree d n i) (incFree b n i)
  incFree (AFst d)     n i = AFst (incFree d n i)
  incFree (ASnd d)     n i = ASnd (incFree d n i)
  incFree ABeta        n i = ABeta
  incFree (ARho d t b) n i = ARho (incFree d n i) (incFree t (1 + n) i) (incFree b n i)
  incFree (APi t tp)   n i = APi (incFree t n i) (incFree tp (1 + n) i)
  incFree (AIPi t tp)  n i = AIPi (incFree t n i) (incFree tp (1 + n) i)
  incFree (AIota t tp) n i = AIota (incFree t n i) (incFree tp (1 + n) i)
  incFree (AId x y)    n i = AId (incFree x n i) (incFree y n i)
  incFree AStar n i = AStar

instance Substitute ATerm ATerm where
  sub s n (AV x) =
    if (x >= n)
    then (if x == n 
          then s
          else AV (x - 1))
    else AV x
  sub s n (ALam d)      = ALam (sub (incFree s 0 1) (1 + n) d)
  sub s n (AAnn d b)    = AAnn (sub s n d) (sub s n b)
  sub s n (AApp d b)    = AApp (sub s n d) (sub s n b)
  sub s n (ALAM d)      = ALAM (sub (incFree s 0 1) (1 + n) d)
  sub s n (AAppi d b)   = AAppi (sub s n d) (sub s n b)
  sub s n (AIPair d b)  = AIPair (sub s n d) (sub s n b)
  sub s n (AFst d)      = AFst (sub s n d)
  sub s n (ASnd d)      = ASnd (sub s n d)
  sub s n ABeta         = ABeta
  sub s n (ARho d tp b) = ARho (sub s n d) (sub (incFree s 0 1) (1 + n) tp) (sub s n b)
  sub s n (APi t tp)    = APi (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AIPi t tp)   = AIPi (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AIota t tp)  = AIota (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AId x y)     = AId (sub s n x) (sub s n y)
  sub s n AStar = AStar

instance Norm ATerm where
  ssEval (AApp (ALam (AAnn _ tp)) s) = sub s 0 tp
  ssEval (AApp (ALam tp) s) = sub s 0 tp
  ssEval (ALam (AApp tp (AV 0))) =
    if freeIn tp 0 then ALam (AApp tp (AV 0)) else sub (AV 0) 0 tp
  ssEval (AAppi (ALAM tp) s) = sub s 0 tp
  ssEval (ALAM (AAppi tp (AV 0))) =
    if freeIn tp 0 then ALAM (AAppi tp (AV 0)) else sub (AV 0) 0 tp
  ssEval (AFst (AIPair d b)) = d
  ssEval (ASnd (AIPair d b)) = b
  ssEval (ARho ABeta _ b) = b
  ssEval tp = tp

  sdev (AV x)       = AV x
  sdev (ALam d)     = ssEval (ALam (sdev d))
  sdev (AAnn d b)   = ssEval (AAnn (sdev d) (sdev b))
  sdev (AApp d b)   = ssEval (AApp (sdev d) (sdev b))
  sdev (ALAM d)     = ssEval (ALAM (sdev d))
  sdev (AAppi d b)  = ssEval (AAppi (sdev d) (sdev b))
  sdev (AIPair d b) = AIPair (sdev d) (sdev b)
  sdev (AFst d)     = ssEval (AFst (sdev d))
  sdev (ASnd d)     = ssEval (ASnd (sdev d))
  sdev ABeta        = ABeta
  sdev (ARho d x b) = ssEval (ARho (sdev d) (sdev x) (sdev b))
  sdev (APi t tp)   = APi (sdev t) (sdev tp)
  sdev (AIPi t tp)  = AIPi (sdev t) (sdev tp)
  sdev (AIota t t') = AIota (sdev t) (sdev t')
  sdev (AId x y)    = AId (sdev x) (sdev y)
  sdev AStar = AStar

{- Annotation Erasure -}
erase :: ATerm -> Term
erase (AV x)        = V x
erase (ALam t)      = Lam (erase t)
erase (AAnn t t')   = erase t'
erase (AApp t t')   = App (erase t) (erase t')
erase (ALAM t)      = sub (Lam (V 0)) 0 (erase t) -- Free variables need to be decremented. 
erase (AAppi t t')  = erase t
erase (AIPair t t') = erase t
erase (AFst t)      = erase t
erase (ASnd t)      = erase t
erase ABeta         = Lam (V 0)
erase (ARho _ _ t') = erase t'
erase (APi t t1)    = Pi (erase t) (erase t1)
erase (AIPi t t1)   = IPi (erase t) (erase t1)
erase (AIota t t1)  = Iota (erase t) (erase t1)
erase (AId x x1)    = Id (erase x) (erase x1)
erase AStar = Star
