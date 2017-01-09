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

data DB = Vj Int | Lamj DB | Appj DB DB deriving (Eq)

instance DeBruijin DB where
  freeIn (Vj x) n = x == n 
  freeIn (Lamj d) n = freeIn d (1 + n)
  freeIn (Appj d d1) n = freeIn d n || freeIn d1 n

  incFree (Vj x) n i = if x >= n then Vj (i + x) else Vj x
  incFree (Lamj d) n i = Lamj (incFree d (1 + n) i)
  incFree (Appj d1 d2) n i = Appj (incFree d1 n i) (incFree d2 n i)

instance Substitute DB DB where
  -- Substitute and decrement free variables
  sub s n (Vj x) =
    if x >= n then (if x == n
          then s            -- if n = x, return s
          else Vj (x - 1))  -- if n < x, Ex y . suc y = x; return y
    else Vj x               -- if Vj x isn't free, do nothing
  sub s n (Lamj d) = Lamj (sub (incFree s 0 1) (1 + n) d)
  sub s n (Appj d1 d2) = Appj (sub s n d1) (sub s n d2)

instance Norm DB where
  ssEval (Appj (Lamj d) s) = sub s 0 d -- beta-reduction
  ssEval (Lamj (Appj d (Vj 0))) =
    if freeIn d 0
    then Lamj (Appj d (Vj 0))
    else sub (Lamj (Vj 0)) 0 d -- eta-reduction
  ssEval d = d

  sdev (Lamj d) = ssEval (Lamj (sdev d))
  sdev (Vj x) = Vj x
  sdev (Appj d d1) = ssEval (Appj (sdev d) (sdev d1))

{- Unannotated Types -}
data Type = Vt Int
          | Allk Kind Type
          | Pit Type Type
          | Lamt Type Type
          | LAMk Kind Type
          | Appt Type DB
          | Appk Type Type
          | Allt Type Type
          | Iota Type Type
          | Id DB DB
          deriving (Eq)

data Kind = Star
          | Pik Type Kind
          | Alltk Kind Kind
          deriving (Eq)

instance DeBruijin Type where
  freeIn (Vt x)      n = x == n
  freeIn (Allk k t)  n = freeIn k n || freeIn t (1 + n)
  freeIn (Pit t tp)  n = freeIn t n || freeIn tp (1 + n)
  freeIn (Lamt t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (LAMk t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (Appt t x)  n = freeIn t n || freeIn x n
  freeIn (Appk t x)  n = freeIn t n || freeIn x n
  freeIn (Allt t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (Iota t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (Id x y)    n = freeIn x n || freeIn y n

  incFree (Vt x)      n i = if x >= n then Vt (i + x) else Vt x
  incFree (Allk k t)  n i = Allk (incFree k n i) (incFree t (1 + n) i)
  incFree (Pit t tp)  n i = Pit (incFree t n i) (incFree tp (1 + n) i)
  incFree (Lamt t tp) n i = Lamt (incFree t n i) (incFree tp (1 + n) i)
  incFree (LAMk t tp) n i = LAMk (incFree t n i) (incFree tp (1 + n) i)
  incFree (Appt t d)  n i = Appt (incFree t n i) (incFree d n i)
  incFree (Appk t d)  n i = Appk (incFree t n i) (incFree d n i)
  incFree (Allt t tp) n i = Allt (incFree t n i) (incFree tp (1 + n) i)
  incFree (Iota t tp) n i = Iota (incFree t n i) (incFree tp (1 + n) i)
  incFree (Id x y)    n i = Id (incFree x n i) (incFree y n i)

instance DeBruijin Kind where
  freeIn Star n       = False
  freeIn (Pik tp k) n = freeIn tp n || freeIn k (1 + n)
  freeIn (Alltk tp k) n = freeIn tp n || freeIn k (1 + n)

  incFree Star n i      = Star
  incFree (Pik t k) n i = Pik (incFree t n i) (incFree k (1 + n) i)
  incFree (Alltk t k) n i = Alltk (incFree t n i) (incFree k (1 + n) i)

instance Substitute Type Type where
  sub s n (Vt x) =
    if x >= n then (if x == n
          then s            -- if n = x, return s
          else Vt (x - 1))  -- if n < x, Ex y . suc y = x; return y
    else Vt x               -- if Vt x isn't free, do nothing
  sub s n (Allk k tp) = Allk (sub s n k) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Pit t tp)  = Pit (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Lamt t tp) = Lamt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (LAMk t tp) = LAMk (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Appt t x)  = Appt (sub s n t) (sub (Lamj (Vj 0)) n x)
  sub s n (Appk t x)  = Appk (sub s n t) (sub s n x)
  sub s n (Allt t tp) = Allt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Iota t tp) = Iota (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Id x y)    = Id (sub (Lamj (Vj 0)) n x) (sub (Lamj (Vj 0)) n y)

instance Substitute Type Kind where
  sub s n Star = Star
  sub s n (Pik x k) = Pik (sub s n x) (sub (incFree s 0 1) (1 + n) k)
  sub s n (Alltk x k) = Alltk (sub s n x) (sub (incFree s 0 1) (1 + n) k)

instance Substitute DB Type where
  sub s n (Vt x)      = if (x > n) then Vt (x - 1) else Vt x
  sub s n (Allk k tp) = Allk (sub s n k) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Pit t tp)  = Pit (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Lamt t tp) = Lamt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (LAMk t tp) = LAMk (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Appt t x)  = Appt (sub s n t) (sub s n x)
  sub s n (Appk t x)  = Appk (sub s n t) (sub s n x)
  sub s n (Allt t tp) = Allt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Iota t tp) = Iota (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (Id x y)    = Id (sub s n x) (sub s n y)

instance Substitute DB Kind where
  sub s n Star = Star
  sub s n (Pik x k) = Pik (sub s n x) (sub (incFree s 0 1) (1 + n) k)
  sub s n (Alltk x k) = Alltk (sub s n x) (sub (incFree s 0 1) (1 + n) k)

instance Norm Type where
  ssEval (Appt (Lamt t tp) s) = sub s 0 tp
  ssEval (Appk (LAMk t tp) s) = sub s 0 tp
  ssEval (Lamt t (Appt tp (Vj 0))) = if freeIn tp 0 then Lamt t (Appt tp (Vj 0)) else incFree tp 0 1
  ssEval (LAMk t (Appk tp (Vt 0))) = if freeIn tp 0 then LAMk t (Appk tp (Vt 0)) else incFree tp 0 1
  ssEval tp = tp

  sdev (Vt x)      = Vt x
  sdev (Allk x t)  = Allk (sdev x) (sdev t)
  sdev (Pit t tp)  = Pit (sdev t) (sdev tp)
  sdev (Lamt t tp) = ssEval (Lamt (sdev t) (sdev tp))
  sdev (LAMk t tp) = ssEval (LAMk (sdev t) (sdev tp))
  sdev (Appt t x)  = ssEval (Appt (sdev t) (sdev x))
  sdev (Appk t x)  = ssEval (Appk (sdev t) (sdev x))
  sdev (Allt t tp) = Allt (sdev t) (sdev tp)
  sdev (Iota t tp) = Iota (sdev t) (sdev tp)
  sdev (Id x y)    = Id (sdev x) (sdev y)

instance Norm Kind where
  ssEval tp = tp

  sdev Star = Star
  sdev (Pik x k) = Pik (sdev x) (sdev k)
  sdev (Alltk x k) = Alltk (sdev x) (sdev k)

{- Annotated Types -}
data ADB = AVj Int
         | ALamj ADB
         | AAppj ADB ADB
         | LAMj ADB
         | Apptj ADB AType
         | LAMt ADB 
         | Appi ADB ADB
         | IPair ADB ADB
         | Fst ADB
         | Snd ADB
         | Beta 
         | Rho ADB AType ADB
         deriving (Eq , Show)

data AType = AVt Int
           | AAllk AKind AType
           | APit AType AType
           | ALamt AType AType
           | AAppt AType ADB
           | ALAMk AKind AType
           | AAppk AType AType
           | AAllt AType AType
           | AIota AType AType
           | AId ADB ADB
           deriving (Eq , Show)

data AKind = AStar
           | APik AType AKind
           | AAlltk AKind AKind
           deriving (Eq , Show)

instance DeBruijin ADB where
  freeIn (AVj x)      n = x == n 
  freeIn (ALamj d)    n = freeIn d (1 + n)
  freeIn (LAMj d)     n = freeIn d (1 + n)
  freeIn (LAMt d)     n = freeIn d (1 + n)
  freeIn (AAppj d d1) n = freeIn d n || freeIn d1 n
  freeIn (Apptj d tp) n = freeIn d n || freeIn tp n
  freeIn (Appi d d1)  n = freeIn d n || freeIn d1 n
  freeIn (IPair d d1) n = freeIn d n || freeIn d1 n
  freeIn (Fst d)      n = freeIn d n
  freeIn (Snd d)      n = freeIn d n
  freeIn Beta         n = False
  freeIn (Rho d tp b) n = freeIn d n && freeIn tp (1 + n) && freeIn b n

  incFree (AVj x)      n i = if x >= n then AVj (i + x) else AVj x
  incFree (ALamj d)    n i = ALamj (incFree d (1 + n) i)
  incFree (LAMj d)     n i = LAMj (incFree d (1 + n) i)
  incFree (LAMt d)     n i = LAMt (incFree d (1 + n) i)
  incFree (AAppj d b)  n i = AAppj (incFree d n i) (incFree b n i)
  incFree (Apptj d tp) n i = Apptj (incFree d n i) (incFree tp n i)
  incFree (Appi d b)   n i = Appi (incFree d n i) (incFree b n i)
  incFree (IPair d b)  n i = IPair (incFree d n i) (incFree b n i)
  incFree (Fst d)      n i = Fst (incFree d n i)
  incFree (Snd d)      n i = Snd (incFree d n i)
  incFree Beta         n i = Beta
  incFree (Rho d tp b) n i = Rho (incFree d n i) (incFree tp (1 + n) i) (incFree b n i)

instance DeBruijin AType where
  freeIn (AVt x)      n = x == n
  freeIn (AAllk k t)  n = freeIn k n || freeIn t (1 + n)
  freeIn (APit t tp)  n = freeIn t n || freeIn tp (1 + n)
  freeIn (ALamt t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (AAppt t x)  n = freeIn t n || freeIn  x n
  freeIn (ALAMk t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (AAppk t x)  n = freeIn t n || freeIn  x n
  freeIn (AAllt t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (AIota t tp) n = freeIn t n || freeIn tp (1 + n)
  freeIn (AId x y)    n = freeIn x n || freeIn y n

  incFree (AVt x)      n i = if x >= n then AVt (i + x) else AVt x
  incFree (AAllk k t)  n i = AAllk (incFree k n i) (incFree t (1 + n) i)
  incFree (APit t tp)  n i = APit (incFree t n i) (incFree tp (1 + n) i)
  incFree (ALamt t tp) n i = ALamt (incFree t n i) (incFree tp (1 + n) i)
  incFree (AAppt t d)  n i = AAppt (incFree t n i) (incFree d n i)
  incFree (ALAMk t tp) n i = ALAMk (incFree t n i) (incFree tp (1 + n) i)
  incFree (AAppk t d)  n i = AAppk (incFree t n i) (incFree d n i)
  incFree (AAllt t tp) n i = AAllt (incFree t n i) (incFree tp (1 + n) i)
  incFree (AIota t tp) n i = AIota (incFree t n i) (incFree tp (1 + n) i)
  incFree (AId x y)    n i = AId (incFree x n i) (incFree y n i)

instance DeBruijin AKind where
  freeIn AStar n = False
  freeIn (APik tp k) n = freeIn tp n || freeIn k (1 + n)
  freeIn (AAlltk tp k) n = freeIn tp n || freeIn k (1 + n)

  incFree AStar n i = AStar
  incFree (APik t k) n i = APik (incFree t n i) (incFree k (1 + n) i)
  incFree (AAlltk t k) n i = AAlltk (incFree t n i) (incFree k (1 + n) i)

instance Substitute ADB ADB where
  sub s n (AVj x) =
    if (x >= n)
    then (if x == n 
          then s
          else AVj (x - 1))
    else AVj x
  sub s n (ALamj d)    = ALamj (sub (incFree s 0 1) (1 + n) d)
  sub s n (AAppj d b)  = AAppj (sub s n d) (sub s n b)
  sub s n (LAMj d)     = LAMj (sub (incFree s 0 1) (1 + n) d)
  sub s n (Apptj d x)  = Apptj (sub s n d) (sub s n x)
  sub s n (LAMt d)     = LAMt (sub (incFree s 0 1) (1 + n) d)
  sub s n (Appi d b)   = Appi (sub s n d) (sub s n b)
  sub s n (IPair d b)  = IPair (sub s n d) (sub s n b)
  sub s n (Fst d)      = Fst (sub s n d)
  sub s n (Snd d)      = Snd (sub s n d)
  sub s n Beta         = Beta
  sub s n (Rho d tp b) = Rho (sub s n d) (sub (incFree s 0 1) (1 + n) tp) (sub s n b)

instance Substitute AType ADB where
  sub s n (AVj x) = 
    if (x > n)
    then (AVj (x - 1))
    else (AVj x)
  sub s n (ALamj d)    = ALamj (sub (incFree s 0 1) (1 + n) d)
  sub s n (AAppj d b)  = AAppj (sub s n d) (sub s n b)
  sub s n (LAMj d)     = LAMj (sub (incFree s 0 1) (1 + n) d)
  sub s n (Apptj d x)  = Apptj (sub s n d) (sub s n x)
  sub s n (LAMt d)     = LAMt (sub (incFree s 0 1) (1 + n) d)
  sub s n (Appi d b)   = Appi (sub s n d) (sub s n b)
  sub s n (IPair d b)  = IPair (sub s n d) (sub s n b)
  sub s n (Fst d)      = Fst (sub s n d)
  sub s n (Snd d)      = Snd (sub s n d)
  sub s n Beta         = Beta
  sub s n (Rho d tp b) = Rho (sub s n d) (sub (incFree s 0 1) (1 + n) tp) (sub s n b)

instance Substitute AType AType where
  sub s n (AVt x) =
    if (x >= n)
    then (if x == n
          then s
          else AVt (x - 1))
    else AVt x                     -- if AVt x isn't free, do nothing
  sub s n (AAllk k tp) = AAllk (sub s n k) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (APit t tp)  = APit (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (ALamt t tp) = ALamt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AAppt t x)  = AAppt (sub s n t) (sub s n x)
  sub s n (ALAMk t tp) = ALAMk (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AAppk t x)  = AAppk (sub s n t) (sub s n x)
  sub s n (AAllt t tp) = AAllt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AIota t tp) = AIota  (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AId x y)    = AId (sub s n x) (sub s n y)

instance Substitute AType AKind where
  sub s n AStar = AStar
  sub s n (APik x k) = APik (sub s n x) (sub (incFree s 0 1) (1 + n) k)
  sub s n (AAlltk x k) = AAlltk (sub s n x) (sub (incFree s 0 1) (1 + n) k)

instance Substitute ADB AType where
  sub s n (AVt x) =
    if (x > n)
    then AVt (x - 1)
    else AVt x
  sub s n (AAllk k tp) = AAllk (sub s n k) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (APit t tp)  = APit (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (ALamt t tp) = ALamt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AAppt t x)  = AAppt (sub s n t) (sub s n x)
  sub s n (ALAMk t tp) = ALAMk (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AAppk t x)  = AAppk (sub s n t) (sub s n x)
  sub s n (AAllt t tp) = AAllt (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AIota t tp) = AIota (sub s n t) (sub (incFree s 0 1) (1 + n) tp)
  sub s n (AId x y)    = AId (sub s n x) (sub s n y)

instance Substitute ADB AKind where
  sub s n AStar = AStar
  sub s n (APik x k) = APik (sub s n  x) (sub (incFree s 0 1) (1 + n) k)
  sub s n (AAlltk x k) = AAlltk (sub s n  x) (sub (incFree s 0 1) (1 + n) k)

instance Norm ADB where
  ssEval (AAppj (ALamj tp) s) = sub s 0 tp
  ssEval (ALamj (AAppj tp (AVj 0))) =
    if freeIn tp 0 then ALamj (AAppj tp (AVj 0)) else sub (ALamj (AVj 0)) 0 tp
  ssEval (Apptj (LAMt tp) s) = sub s 0 tp
  ssEval (LAMt (Apptj tp (AVt 0))) =
    if freeIn tp 0 then LAMt (Apptj tp (AVt 0)) else sub (ALamj (AVj 0)) 0 tp
  ssEval (Appi (LAMj tp) s) = sub s 0 tp
  ssEval (LAMj (Appi tp (AVj 0))) =
    if freeIn tp 0 then LAMj (Appi tp (AVj 0)) else sub (ALamj (AVj 0)) 0 tp
  ssEval tp = tp

  sdev (AVj x)     = AVj x
  sdev (ALamj d)   = ssEval (ALamj (sdev d))
  sdev (AAppj d b) = ssEval (AAppj (sdev d) (sdev b))
  sdev (LAMj d)    = ssEval (LAMj (sdev d))
  sdev (Apptj d x) = ssEval (Apptj (sdev d) (sdev x))
  sdev (LAMt d)    = ssEval (LAMt (sdev d))
  sdev (Appi d b)  = ssEval (Appi (sdev d) (sdev b))
  sdev (IPair d b) = IPair (sdev d) (sdev b)
  sdev (Fst d)     = Fst (sdev d)
  sdev (Snd d)     = Snd (sdev d)
  sdev Beta        = Beta
  sdev (Rho d x b) = Rho (sdev d) (sdev x) (sdev b)

instance Norm AType where
  ssEval (AAppt (ALamt t tp) s) = sub s 0 tp
  ssEval (ALamt t (AAppt tp (AVj 0))) =
    if freeIn tp 0 then ALamt t (AAppt tp (AVj 0)) else sub (ALamj (AVj 0)) 0 tp
  ssEval (AAppk (ALAMk t tp) s) = sub s 0 tp
  ssEval (ALAMk t (AAppk tp (AVt 0))) =
    if freeIn tp 0 then ALAMk t (AAppk tp (AVt 0)) else sub (ALamj (AVj 0)) 0 tp
  ssEval tp = tp

  sdev (AVt x)      = AVt x
  sdev (AAllk x t)  = AAllk (sdev x) (sdev t)
  sdev (APit t tp)  = APit (sdev t) (sdev tp)
  sdev (ALamt t tp) = ssEval (ALamt (sdev t) (sdev tp))
  sdev (AAppt t x)  = ssEval (AAppt (sdev t) (sdev x))
  sdev (ALAMk t tp) = ssEval (ALAMk (sdev t) (sdev tp))
  sdev (AAppk t x)  = ssEval (AAppk (sdev t) (sdev x))
  sdev (AAllt t tp) = AAllt (sdev t) (sdev tp)
  sdev (AIota t tp) = AIota (sdev t) (sdev tp)
  sdev (AId x y)    = AId (sdev x) (sdev y)

instance Norm AKind where
  ssEval tp = tp

  sdev AStar = AStar
  sdev (APik x k) = APik (sdev x) (sdev k)
  sdev (AAlltk x k) = AAlltk (sdev x) (sdev k)

{- Annotation Erasure -}
erase :: ADB -> DB
erase (AVj x)      = Vj x
erase (ALamj t)    = Lamj (erase t)
erase (AAppj t t') = Appj (erase t) (erase t')
erase (LAMj t)     = sub (Lamj (Vj 0)) 0 (erase t) -- Free variables need to be decremented. 
erase (Apptj t _)  = erase t                         
erase (LAMt t)     = sub (Lamj (Vj 0)) 0 (erase t) -- Is there a better way to do this?
erase (Appi t t')  = erase t
erase (IPair t t') = erase t
erase (Fst t)      = erase t
erase (Snd t)      = erase t
erase Beta         = Lamj (Vj 0)
erase (Rho _ _ t') = erase t'

eraseAType :: AType -> Type
eraseAType (AVt x)      = Vt x
eraseAType (AAllk x t)  = Allk (eraseAKind x) (eraseAType t)
eraseAType (APit t t1)  = Pit (eraseAType t) (eraseAType t1)
eraseAType (ALamt t t1) = Lamt (eraseAType t) (eraseAType t1)
eraseAType (AAppt t x)  = Appt (eraseAType t) (erase x)
eraseAType (ALAMk t t1) = LAMk (eraseAKind t) (eraseAType t1)
eraseAType (AAppk t x)  = Appk (eraseAType t) (eraseAType x)
eraseAType (AAllt t t1) = Allt (eraseAType t) (eraseAType t1)
eraseAType (AIota t t1) = Iota (eraseAType t) (eraseAType t1)
eraseAType (AId x x1)   = Id (erase x) (erase x1)

eraseAKind :: AKind -> Kind
eraseAKind AStar = Star
eraseAKind (APik x k) = Pik (eraseAType x) (eraseAKind k)
eraseAKind (AAlltk x k) = Alltk (eraseAKind x) (eraseAKind k)
