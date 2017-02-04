{-# language MultiParamTypeClasses #-}

module TypeChecker where

import Exp.ErrM
import AbstractSyntax

{- The Type Checker -}
data Ctx = Empty
         | Snoc Ctx ATerm

infer :: TopCtx -> Ctx -> ATerm -> Err ATerm
infer c g (AV n) = case (g , n) of
  (Empty , _) -> Bad "Cannot infer term variable in empty context."
  (Snoc g x , 0) -> check c g (sdev x) AStar >> ssdev c (incFree x 0 1)
  (Snoc g k , n) -> infer c g (AV (n - 1)) >>= \t -> Ok (incFree t 0 1)
infer c g (AVS s) = errLookup s c >>= Ok . snd
infer c g (ALam (AAnn tp tpp))
  = check c g (sub (AV 0) 0 tp) AStar >>
    infer c (Snoc g (sub (AV 0) 0 tp)) tpp >>= \ it ->
    Ok (APi (sub (AV 0) 0 tp) it)
infer c g (ALam t) = Bad "Cannot infer the type of an unannotated lambda term."
infer c (Snoc g tp1) (AAnn t1 t2) =
  if normalize c t1 == normalize c (incFree tp1 0 1)
  then infer c (Snoc g tp1) (sdev t2)
  else Bad "Type annotation didn't match durring inference."
infer c g (AApp (ALam t) s) = infer c g (sub s 0 t) >>= Ok . sdev
infer c g (AApp t t') = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok (APi tp1 tp2) -> check c g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a pi type."
infer c g (ALAM t) = Bad "Cannot infer the type of an implicit lambda term."
infer c g (AAppi (ALAM t) s) = infer c g (sub s 0 t) >>= Ok . sdev
infer c g (AAppi t t') = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok (AIPi tp1 tp2) -> check c g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not an implicit product type."
infer c g (AIPair t t') = Bad "Cannot infer the type of an iota constructor."
infer c g (AFst t) = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok i ->
    do
      is <- ssdev c i
      case is of 
        AIota tp1 tp2 -> Ok (sdev tp1)
        _ -> Bad "Term is not an iota constructor (#1)."
infer c g (ASnd t) = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok i ->
    do
      is <- ssdev c i
      case is of 
        AIota tp1 tp2 -> Ok (sdev (sub (AFst t) 0 tp2))
        _ -> Bad "Term is not an iota constructor (#2)."
infer c g ABeta = Bad "Identity proofs cannot be inferred"
infer c g (ARho t' tp t) = case infer c g (sdev t') of
  Bad y -> Bad y
  Ok (AId t1 t2) ->
    check c g t (sub t1 0 tp) >> check c g (sub t1 0 tp) AStar >> Ok (sdev (sub t2 0 tp))
  Ok _ -> Bad "Term is not an identity durring term inferrence"
infer c g (APi tp tpp) = check c g tp AStar >> check c (Snoc g tp) tpp AStar >> Ok AStar
infer c g (AIPi tp tpp) = check c g tp AStar >> check c (Snoc g tp) tpp AStar >> Ok AStar
infer c g (AIota tp tpp) = check c g tp AStar >> check c (Snoc g tp) tpp AStar >> Ok AStar
infer c g (AId x y) = Ok AStar
infer c g AStar = Ok AStar

check :: TopCtx -> Ctx -> ATerm -> ATerm -> Err ()
check c g k (AVS s) =
  do
    ty <- errLookup s c
    check c g k (fst ty)
check c g (AV n) tp = case (g , n) of 
  (Empty , _) -> Bad "Cannot check type of variable term in an empty context."
  (Snoc g x , 0) ->
    if (normalize c tp >>= erase c) == (normalize c (incFree x 0 1) >>= erase c)
    then check c (Snoc g (sdev x)) (sdev tp) AStar >> check c g (sdev x) AStar 
    else Bad "Term does not have correct type."
  (Snoc g k , n) -> check c g (AV (n - 1)) (sub (AV 0) 0 tp) 
check c g (AVS s) tp =
    if (errLookup s c >>= normalize c . snd) == normalize c tp
    then Ok ()
    else Bad "Type didn't match durring name lookup."
check c g (ALam t) k = case ssdev c k of
  Ok (APi tp1 tp2) -> check c (Snoc g tp1) (sdev t) tp2 
  _ -> Bad "Lambdas can only be Pi types"
check c (Snoc g tp1) (AAnn t1 t2) tp2 =
    if (normalize c t1 == normalize c (incFree tp1 0 1))
    then check c (Snoc g tp1) (sdev t2) tp2 
    else Bad "Type annotation didn't match check."
check c g (AApp (ALam t) s) tp = check c g (sub s 0 t) tp 
check c g (AApp t t1) tp = infer c g (sdev (AApp t t1)) >>= \k ->
    if (normalize c tp >>= erase c) == (normalize c k >>= erase c)
    then check c g tp AStar 
    else Bad "Failed to unify at application"
check c g (ALAM t) k = case ssdev c k of
  Ok (AIPi tp1 tp2) -> check c (Snoc g tp1) (sdev t) tp2 
  _ -> Bad "Implicit lambdas must be implicit products."
check c g (AAppi (ALAM t) s) tp = check c g (sub s 0 t) tp 
check c g (AAppi t t1) tp = infer c g (sdev (AAppi t t1)) >>= \ k ->
    if (normalize c tp >>= erase c) == (normalize c k >>= erase c)
    then check c g tp AStar 
    else Bad "Failed to unify at implicit application"
check c g (AIPair t1 t2) k = case ssdev c k of
  Ok (AIota tp1 tp2) ->
    if (normalize c t1 >>= erase c) == (normalize c t2 >>= erase c)
    then check c g (sdev t1) tp1 >> check c g (sdev t2) (sub (sdev t1) 0 tp2) 
    else Bad "Iota constructor does not erase properly."
  _ -> Bad "Iota contructor must be a dependent intersection."
check c g (AFst t) tp = infer c g (AFst (sdev t)) >>= \k ->
    if (normalize c tp >>= erase c) == (normalize c k >>= erase c)
    then check c g tp AStar 
    else Bad "Failed to unify at iota elimination (#1)"
check c g (ASnd t) tp = infer c g (ASnd (sdev t)) >>= \k ->
    if (normalize c tp >>= erase c) == (normalize c k >>= erase c)
    then check c g tp AStar 
    else Bad "Failed to unify at iota elimination (#2)"
check c g ABeta k = case ssdev c k of
  Ok (AId t1 t2) ->
    if (normalize c t1 >>= erase c) == (normalize c t2 >>= erase c)
    then Ok ()
    else Bad "Lhs does not match rhs of identity"
  _ -> Bad "Identity constructor must construct identity."
check c g (ARho t' x t) tp = case infer c g (sdev t') of
  Bad s -> Bad s
  Ok (AId t1 t2) ->
    if (normalize c tp >>= erase c) == (normalize c (sub t2 0 x) >>= erase c)
    then check c g tp AStar >> check c g (sdev t) (sub t1 0 x) 
    else Bad "LHS and RHS of identity don't match after erasure"
  Ok _ -> Bad "Term is not an identity durring term checking"
check c g (APi tp tp1) AStar = check c g tp AStar >> check c (Snoc g tp) tp1 AStar 
check c g (APi tp tp1) _ = Bad "Pi types can only have AStar kind."
check c g (AIPi tp tpp) AStar = check c g (sdev tp) AStar >> check c (Snoc g (sdev tp)) (sdev tpp) AStar 
check c g (AIPi x tp) _ = Bad "Implicit products can only have AStar kind."
check c g (AIota tp tpp) AStar = check c g (sdev tp) AStar >> check c (Snoc g (sdev tp)) (sdev tpp) AStar 
check c g (AIota x tp) _ = Bad "Dependent intersections can only have AStar kind."
check c g (AId x y) AStar = Ok ()
check c g (AId x y) _ = Bad "Heterogenious equalities can only have AStar kind."
check c g AStar AStar = Ok () 
check c g AStar _ = Bad "* can only have type *."
