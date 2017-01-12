{-# language MultiParamTypeClasses #-}

module TypeChecker where

import ErrM
import AbstractSyntax

{- The Type Checker -}
data Ctx = Empty
         | Snok Ctx AKind
         | Snot Ctx AType

checkKind :: Ctx -> AKind -> Err ()
checkKind Empty AStar = Ok ()
checkKind (Snot g _) AStar = checkKind g AStar >> Ok ()
checkKind (Snok g _) AStar = checkKind g AStar >> Ok ()
checkKind g (APik x k) = checkType g x AStar >> checkKind (Snot g x) k >> Ok ()
checkKind g (AAlltk x k) = checkKind g x >> checkKind (Snok g x) k >> Ok ()

inferType :: Ctx -> AType -> Err AKind
inferType g (AVt n) = case (g , n) of
  (Empty , _) -> Bad "Cannot infer Kind of variable in empty context"
  (Snot g _ , 0) -> Bad "Type cannot be infered to be a Kind"
  (Snok g k , 0) -> checkKind g k >> Ok (incFree k 0 1)
  (Snot g k , n) -> inferType g (AVt (n - 1)) >>= \t -> Ok (incFree t 0 1)
  (Snok g k , n) -> inferType g (AVt (n - 1)) >>= \t -> Ok (incFree t 0 1)
inferType g (AAllk x tp) = checkKind g x >> checkType (Snok g x) tp AStar >> Ok (AStar)
inferType g (APit tp tpp) = checkType g tp AStar >> checkType (Snot g tp) tpp AStar >> Ok (AStar)
inferType g (ALamt tp tpp) = checkType g tp AStar >> inferType (Snot g tp) tpp >>= \ it -> Ok (APik tp it)
inferType g (ALAMk tp tpp) = checkKind g tp >> inferType (Snok g tp) tpp >>= \ it -> Ok (AAlltk tp it)
inferType g (AAppt tp t) = case inferType g (sdev tp) of
  Bad s -> Bad s
  Ok (APik tp1 tp2) -> checkTerm g t tp1 >> Ok (sub t 0 tp2)
  Ok _ -> Bad "Non-type-level-product applied durring inference"
inferType g (AAppk tp t) = case inferType g (sdev tp) of
  Bad s -> Bad s
  Ok (AAlltk tp1 tp2) -> checkType g t tp1 >> Ok (sub t 0 tp2)
  Ok _ -> Bad "Non-type-kind-level-product applied durring inference"
inferType g (AAllt tp tpp) = checkType g tp AStar >> checkType (Snot g tp) tpp AStar >> Ok (AStar)
inferType g (AIota tp tpp) = checkType g tp AStar >> checkType (Snot g tp) tpp AStar >> Ok (AStar)
inferType g (AId x y) = Ok (AStar)

checkType :: Ctx -> AType -> AKind -> Err ()
checkType g (AVt n) ka = case (g , n) of
  (Empty , _) -> Bad "Cannot Kind variable in empty context"
  (Snot g _ , 0) -> Bad "Type cannot have a type which is a type."
  (Snok g x , 0) -> case ka == incFree x 0 1 of
    True -> checkKind g x >> Ok ()
    False -> Bad "Type does not have correct kind."
  (Snot g _ , n) -> checkType g (AVt (n - 1)) (sub (AVj 0) 0 ka) >> Ok ()
  (Snok g _ , n) -> checkType g (AVt (n - 1)) (sub (AVt 0) 0 ka) >> Ok ()
checkType g (AAllk x tp) AStar = checkKind g (sdev x) >> checkType (Snok g (sdev x)) (sdev tp) AStar >> Ok ()
checkType g (AAllk x tp) _ = Bad "Type-level products can only have AStar kind."
checkType g (APit tp tp1) AStar = checkType g tp AStar >> checkType (Snot g tp) tp1 AStar >> Ok ()
checkType g (APit tp tp1) _ = Bad "Pi types can only have AStar kind."
checkType g (ALamt tp1 tpp) (APik tp2 ka) = case normalize tp1 == normalize tp2 of
  True -> checkType g (sdev tp2) AStar >> checkType (Snot g (sdev tp2)) (sdev tpp) ka >> Ok ()
  False -> Bad "Lambda binds wring type for Pi" 
checkType g (ALamt tp tpp) _ = Bad "Type-level lambdas can only have type APik"
checkType g (ALAMk tp1 tpp) (AAlltk tp2 ka) = case normalize tp1 == normalize tp2 of
  True -> checkKind g (sdev tp2) >> checkType (Snok g (sdev tp2)) (sdev tpp) ka >> Ok ()
  False -> Bad "Lambda binds wring type for Pi"
checkType g (ALAMk tp tpp) _ = Bad "Type-level kind lambdas can only have type AAlltk"
checkType g (AAppt tp t) ka = case inferType g (sdev (AAppt tp t)) of
  Bad s -> Bad s
  Ok k ->
    if ka == k
    then Ok ()
    else Bad "Failed to unify at type-level application"
checkType g (AAppk tp t) ka = case inferType g (sdev (AAppk tp t)) of
  Bad s -> Bad s
  Ok k ->
    if ka == k
    then Ok ()
    else Bad "Failed to unify at type-level type application"
checkType g (AAllt tp tpp) AStar = checkType g (sdev tp) AStar >> checkType (Snot g (sdev tp)) (sdev tpp) AStar >> Ok ()
checkType g (AAllt x tp) _ = Bad "Implicit products can only have AStar kind."
checkType g (AIota tp tpp) AStar = checkType g (sdev tp) AStar >> checkType (Snot g (sdev tp)) (sdev tpp) AStar >> Ok ()
checkType g (AIota x tp) _ = Bad "Dependent intersections can only have AStar kind."
checkType g (AId x y) AStar = Ok ()
checkType g (AId x y) _ = Bad "Heterogenious equalities can only have AStar kind."

inferTerm :: Ctx -> ADB -> Err AType
inferTerm g (AVj n) = case (g , n) of
  (Empty , _) -> Bad "Cannot infer term variable in empty context."
  (Snot g x , 0) -> checkType g (sdev x) AStar >> Ok (sdev (incFree x 0 1))
  (Snok g k , 0) -> Bad "Term cannot be infered to have a kind."
  (Snot g k , n) -> inferTerm g (AVj (n - 1)) >>= \t -> Ok (incFree t 0 1)
  (Snok g k , n) -> inferTerm g (AVj (n - 1)) >>= \t -> Ok (incFree t 0 1)
inferTerm g (ALamj t) = Bad "Cannot infer the type of a lambda term."
inferTerm g (LAMj t) = Bad "Cannot infer the type of an implicit lambda term."
inferTerm g (LAMt t) = Bad "Cannot infer the type of a type-lambda term."
inferTerm g (AAppj (ALamj t) s) = inferTerm g (sub s 0 t) >>= \ ct -> Ok (sdev ct)
inferTerm g (AAppj t t') = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (APit tp1 tp2) -> checkTerm g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a pi type."
inferTerm g (Apptj (LAMt t) s) = inferTerm g (sub s 0 t) >>= \ ct -> Ok (sdev ct)
inferTerm g (Apptj t t') = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (AAllk tp1 tp2) -> checkType g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a type-product type."
inferTerm g (Appi (LAMj t) s) = inferTerm g (sub s 0 t) >>= \ ct -> Ok (sdev ct)
inferTerm g (Appi t t') = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (AAllt tp1 tp2) -> checkTerm g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not an implicit product type."
inferTerm g (IPair t t') = Bad "Cannot infer the type of an iota constructor."
inferTerm g (Fst t) = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (AIota tp1 tp2) -> Ok (sdev tp1)
  Ok _ -> Bad "Term is not an iota constructor (#1)."
inferTerm g (Snd t) = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (AIota tp1 tp2) -> Ok (sdev (sub (Fst t) 0 tp2))
  Ok _ -> Bad "Term is not an iota constructor (#2)."
inferTerm g Beta = Bad "Identity proofs cannot be inferred"
inferTerm g (Rho t' tp t) = case inferTerm g (sdev t') of
  Bad y -> Bad y
  Ok (AId t1 t2) ->
    checkTerm g t (sub t1 0 tp) >> checkType g (sub t1 0 tp) AStar >> Ok (sdev (sub t2 0 tp))
  Ok _ -> Bad "Term is not an identity durring term inferrence"

checkTerm :: Ctx -> ADB -> AType -> Err ()
checkTerm g (AVj n) tp = case (g , n) of 
  (Empty , _) -> Bad "Cannot check type of variable term in empty context."
  (Snot g x , 0) -> case normalize (eraseAType tp) == normalize (eraseAType (incFree x 0 1)) of
    True -> checkType (Snot g (sdev x)) (sdev tp) AStar >> checkType g (sdev x) AStar >> Ok ()
    False -> Bad "Term does not have correct type."
  (Snok g k , 0) -> Bad "Term cannot have a kind"
  (Snot g k , n) -> checkTerm g (AVj (n - 1)) (sub (AVj 0) 0 tp) >> Ok ()
  (Snok g k , n) -> checkTerm g (AVj (n - 1)) (sub (AVj 0) 0 tp) >> Ok ()
checkTerm g (ALamj t) k = case sdev k of
  APit tp1 tp2 -> checkTerm (Snot g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Lambdas must be pi-types."
checkTerm g (LAMj t) k = case sdev k of
  AAllt tp1 tp2 -> checkTerm (Snot g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Implicit lambdas must be implicit products."
checkTerm g (LAMt t) k = case sdev k of
  AAllk tp1 tp2 -> checkTerm (Snok g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Type-Lambdas must be type-products."
checkTerm g (AAppj (ALamj t) s) tp = checkTerm g (sub s 0 t) tp >> Ok ()
checkTerm g (AAppj t t1) tp = case inferTerm g (sdev (AAppj t t1)) of
  Bad s -> Bad s
  Ok k ->
    if normalize (eraseAType tp) == normalize (eraseAType k)
    then checkType g tp AStar >> Ok ()
    else Bad "Failed to unify at term-level application"
checkTerm g (Apptj (LAMt t) s) tp = checkTerm g (sub s 0 t) tp >> Ok ()
checkTerm g (Apptj t x) tp = case inferTerm g (sdev (Apptj t x)) of
  Bad s -> Bad s
  Ok k ->
    if normalize (eraseAType tp) == normalize (eraseAType k)
    then checkType g tp AStar >> Ok ()
    else Bad "Failed to unify at term-level type application"
checkTerm g (Appi (LAMj t) s) tp = checkTerm g (sub s 0 t) tp >> Ok ()
checkTerm g (Appi t t1) tp = case inferTerm g (sdev (Appi t t1)) of
  Bad s -> Bad s
  Ok k ->
    if normalize (eraseAType tp) == normalize (eraseAType k)
    then checkType g tp AStar >> Ok ()
    else Bad "Failed to unify at implicit application"
checkTerm g (IPair t1 t2) k = case sdev k of
  AIota tp1 tp2 ->
    if normalize (erase t1) == normalize (erase t2)
    then checkTerm g (sdev t1) tp1 >> checkTerm g (sdev t2) (sub (sdev t1) 0 tp2) >> Ok ()
    else Bad "Iota constructor does not erase properly."
  _ -> Bad "Iota contructor must be a dependent intersection."
checkTerm g (Fst t) tp = case inferTerm g (Fst (sdev t)) of
  Bad s -> Bad s
  Ok k ->
    if normalize (eraseAType tp) == normalize (eraseAType k)
    then checkType g tp AStar >> Ok ()
    else Bad "Failed to unify at iota elimination (#1)"
checkTerm g (Snd t) tp = case inferTerm g (Snd (sdev t)) of
  Bad s -> Bad s
  Ok k ->
    if normalize (eraseAType tp) == normalize (eraseAType k)
    then checkType g tp AStar >> Ok ()
    else Bad "Failed to unify at iota elimination (#2)"
checkTerm g Beta k = case sdev k of
  AId t1 t2 ->
    if erase t1 == erase t2
    then Ok ()
    else Bad "Lhs does not match rhs of identity"
  _ -> Bad "Identity constructor must construct identity."
checkTerm g (Rho t' x t) tp = case inferTerm g (sdev t') of
  Bad s -> Bad s
  Ok (AId t1 t2) ->
    if normalize (eraseAType tp) == normalize (eraseAType (sub t2 0 x))
    then checkType g tp AStar >> checkTerm g (sdev t) (sub t1 0 x) >> Ok ()
    else Bad "LHS and RHS of identity don't match after erasure"
  Ok _ -> Bad "Term is not an identity durring term checking"
