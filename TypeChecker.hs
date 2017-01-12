{-# language MultiParamTypeClasses #-}

module TypeChecker where

import ErrM
import AbstractSyntax

{- The Type Checker -}
data Ctx = Empty
         | Snoc Ctx ATerm

infer :: Ctx -> ATerm -> Err ATerm
infer g (AV n) = case (g , n) of
  (Empty , _) -> Bad "Cannot infer term variable in empty context."
  (Snoc g x , 0) -> check g (sdev x) AStar >> Ok (sdev (incFree x 0 1))
  (Snoc g k , n) -> infer g (AV (n - 1)) >>= \t -> Ok (incFree t 0 1)
infer g (ALam (AAnn tp tpp))
  = check g (sub (AV 0) 0 tp) AStar >>
    infer (Snoc g (sub (AV 0) 0 tp)) tpp >>= \ it ->
    Ok (APi (sub (AV 0) 0 tp) it)
infer g (ALam t) = Bad "Cannot infer the type of an unannotated lambda term."
infer (Snoc g tp1) (AAnn t1 t2) =
  if (normalize t1 == normalize (incFree tp1 0 1))
  then infer (Snoc g tp1) (sdev t2)
  else Bad "Type annotation didn't match durring inference."
infer g (AApp (ALam t) s) = infer g (sub s 0 t) >>= Ok . sdev
infer g (AApp t t') = case infer g (sdev t) of
  Bad y -> Bad y
  Ok (APi tp1 tp2) -> check g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a pi type."
infer g (ALAM t) = Bad "Cannot infer the type of an implicit lambda term."
infer g (AAppi (ALAM t) s) = infer g (sub s 0 t) >>= Ok . sdev
infer g (AAppi t t') = case infer g (sdev t) of
  Bad y -> Bad y
  Ok (AIPi tp1 tp2) -> check g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not an implicit product type."
infer g (AIPair t t') = Bad "Cannot infer the type of an iota constructor."
infer g (AFst t) = case infer g (sdev t) of
  Bad y -> Bad y
  Ok (AIota tp1 tp2) -> Ok (sdev tp1)
  Ok _ -> Bad "Term is not an iota constructor (#1)."
infer g (ASnd t) = case infer g (sdev t) of
  Bad y -> Bad y
  Ok (AIota tp1 tp2) -> Ok (sdev (sub (AFst t) 0 tp2))
  Ok _ -> Bad "Term is not an iota constructor (#2)."
infer g ABeta = Bad "Identity proofs cannot be inferred"
infer g (ARho t' tp t) = case infer g (sdev t') of
  Bad y -> Bad y
  Ok (AId t1 t2) ->
    check g t (sub t1 0 tp) >> check g (sub t1 0 tp) AStar >> Ok (sdev (sub t2 0 tp))
  Ok _ -> Bad "Term is not an identity durring term inferrence"
infer g (APi tp tpp) = check g tp AStar >> check (Snoc g tp) tpp AStar >> Ok AStar
infer g (AIPi tp tpp) = check g tp AStar >> check (Snoc g tp) tpp AStar >> Ok AStar
infer g (AIota tp tpp) = check g tp AStar >> check (Snoc g tp) tpp AStar >> Ok AStar
infer g (AId x y) = Ok AStar
infer g AStar = Ok AStar

check :: Ctx -> ATerm -> ATerm -> Err ()
check g (AV n) tp = case (g , n) of 
  (Empty , _) -> Bad "Cannot check type of variable term in an empty context."
  (Snoc g x , 0) -> case normalize (erase tp) == normalize (erase (incFree x 0 1)) of
    True -> check (Snoc g (sdev x)) (sdev tp) AStar >> check g (sdev x) AStar >> Ok ()
    False -> Bad "Term does not have correct type."
  (Snoc g k , n) -> check g (AV (n - 1)) (sub (AV 0) 0 tp) >> Ok ()
check g (ALam t) k = case sdev k of
  APi tp1 tp2 -> check (Snoc g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Lambdas can only be Pi types"
check (Snoc g tp1) (AAnn t1 t2) tp2 =
    if (normalize t1 == normalize (incFree tp1 0 1))
    then check (Snoc g tp1) (sdev t2) tp2 >> Ok ()
    else Bad "Type annotation didn't match check."
check g (AApp (ALam t) s) tp = check g (sub s 0 t) tp >> Ok ()
check g (AApp t t1) tp = infer g (sdev (AApp t t1)) >>= \k ->
    if normalize (erase tp) == normalize (erase k)
    then check g tp AStar >> Ok ()
    else Bad "Failed to unify at application"
check g (ALAM t) k = case sdev k of
  AIPi tp1 tp2 -> check (Snoc g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Implicit lambdas must be implicit products."
check g (AAppi (ALAM t) s) tp = check g (sub s 0 t) tp >> Ok ()
check g (AAppi t t1) tp = infer g (sdev (AAppi t t1)) >>= \ k ->
    if normalize (erase tp) == normalize (erase k)
    then check g tp AStar >> Ok ()
    else Bad "Failed to unify at implicit application"
check g (AIPair t1 t2) k = case sdev k of
  AIota tp1 tp2 ->
    if normalize (erase t1) == normalize (erase t2)
    then check g (sdev t1) tp1 >> check g (sdev t2) (sub (sdev t1) 0 tp2) >> Ok ()
    else Bad "Iota constructor does not erase properly."
  _ -> Bad "Iota contructor must be a dependent intersection."
check g (AFst t) tp = infer g (AFst (sdev t)) >>= \k ->
    if normalize (erase tp) == normalize (erase k)
    then check g tp AStar >> Ok ()
    else Bad "Failed to unify at iota elimination (#1)"
check g (ASnd t) tp = infer g (ASnd (sdev t)) >>= \k ->
    if normalize (erase tp) == normalize (erase k)
    then check g tp AStar >> Ok ()
    else Bad "Failed to unify at iota elimination (#2)"
check g ABeta k = case sdev k of
  AId t1 t2 ->
    if erase t1 == erase t2
    then Ok ()
    else Bad "Lhs does not match rhs of identity"
  _ -> Bad "Identity constructor must construct identity."
check g (ARho t' x t) tp = case infer g (sdev t') of
  Bad s -> Bad s
  Ok (AId t1 t2) ->
    if normalize (erase tp) == normalize (erase (sub t2 0 x))
    then check g tp AStar >> check g (sdev t) (sub t1 0 x) >> Ok ()
    else Bad "LHS and RHS of identity don't match after erasure"
  Ok _ -> Bad "Term is not an identity durring term checking"
check g (APi tp tp1) AStar = check g tp AStar >> check (Snoc g tp) tp1 AStar >> Ok ()
check g (APi tp tp1) _ = Bad "Pi types can only have AStar kind."
check g (AIPi tp tpp) AStar = check g (sdev tp) AStar >> check (Snoc g (sdev tp)) (sdev tpp) AStar >> Ok ()
check g (AIPi x tp) _ = Bad "Implicit products can only have AStar kind."
check g (AIota tp tpp) AStar = check g (sdev tp) AStar >> check (Snoc g (sdev tp)) (sdev tpp) AStar >> Ok ()
check g (AIota x tp) _ = Bad "Dependent intersections can only have AStar kind."
check g (AId x y) AStar = Ok ()
check g (AId x y) _ = Bad "Heterogenious equalities can only have AStar kind."
check g AStar AStar = Ok () 
check g AStar _ = Bad "* can only have type *."
