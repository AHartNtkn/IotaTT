{-# language MultiParamTypeClasses #-}

module TypeChecker where

import ErrM
import AbstractSyntax

{- Attempt reversing a substituted variable -}
reverseSubA :: ADB -> ADB  -> Int -> ADB
reverseSubA s (AVj x) n = case x >= n of
  True -> AVj (1 + x)
  False -> AVj x
reverseSubA s (ALamj d) n = case (incFree s 0 1) == d of
  True -> ALamj (AVj (1 + n))
  False -> ALamj (reverseSubA (incFree s 0 1) d (1 + n))
reverseSubA s (AAppj d b) n = case (s == d , s == b) of
  (True , True)  -> AAppj (AVj n) (AVj n)
  (False , True) -> AAppj (reverseSubA s d n) (AVj n)
  (True , False) -> AAppj (AVj n) (reverseSubA s b n)
  (False , False) -> AAppj (reverseSubA s d n) (reverseSubA s b n)
reverseSubA s (LAMj d) n = case (incFree s 0 1) == d of
  True -> LAMj (AVj (1 + n))
  False -> LAMj (reverseSubA (incFree s 0 1) d (1 + n))
reverseSubA s (Apptj d x) n = case s == d of
  True -> Apptj (AVj n) (reverseSubT s x n)
  False -> Apptj (reverseSubA s d n) (reverseSubT s x n)
reverseSubA s (LAMt d) n = case (incFree s 0 1) == d of
  True -> LAMt (AVj (1 + n))
  False -> LAMt (reverseSubA (incFree s 0 1) d (1 + n))
reverseSubA s (Appi d b) n = case (s == d , s == b) of
  (True , True)  -> Appi (AVj n) (AVj n)
  (False , True) -> Appi (reverseSubA s d n) (AVj n)
  (True , False) -> Appi (AVj n) (reverseSubA s b n)
  (False , False) -> Appi (reverseSubA s d n) (reverseSubA s b n)
reverseSubA s (IPair d b) n = case (s == d , s == b) of
  (True , True)  -> IPair (AVj n) (AVj n)
  (False , True) -> IPair (reverseSubA s d n) (AVj n)
  (True , False) -> IPair (AVj n) (reverseSubA s b n)
  (False , False) -> IPair (reverseSubA s d n) (reverseSubA s b n)
reverseSubA s (Fst d) n = case s == d of
  True -> Fst (AVj n)
  False -> Fst (reverseSubA s d n)
reverseSubA s (Snd d) n = case s == d of
  True -> Snd (AVj n)
  False -> Snd (reverseSubA s d n)
reverseSubA s Beta n = Beta
reverseSubA s (Rho d x b) n = case (s == d , s == b) of
  (True , True)  -> Rho (AVj n) (reverseSubT (incFree s 0 1) x (1 + n)) (AVj n)
  (False , True) -> Rho (reverseSubA s d n) (reverseSubT (incFree s 0 1) x (1 + n)) (AVj n)
  (True , False) -> Rho (AVj n) (reverseSubT (incFree s 0 1) x (1 + n)) (reverseSubA s b n)
  (False , False) -> Rho (reverseSubA s d n) (reverseSubT (incFree s 0 1) x (1 + n)) (reverseSubA s b n)

reverseSubT :: ADB -> AType -> Int -> AType
reverseSubT s (AVt x) n = case x >= n of
  True -> AVt (1 + x)
  False -> AVt x
reverseSubT s (AAllk x t) n = AAllk (reverseSubK s x n) (reverseSubT (incFree s 0 1) t (1 + n))
reverseSubT s (APit x t)  n = APit (reverseSubT s x n) (reverseSubT (incFree s 0 1) t (1 + n))
reverseSubT s (ALamt x t) n = ALamt (reverseSubT s x n) (reverseSubT (incFree s 0 1) t (1 + n))
reverseSubT s (AAppt t x) n = case s == x of
  True -> AAppt (reverseSubT s t n) (AVj n)
  False -> AAppt (reverseSubT s t n) (reverseSubA s x n)
reverseSubT s (AAllt x t) n = AAllt (reverseSubT s x n) (reverseSubT (incFree s 0 1) t (1 + n))
reverseSubT s (AIota x t) n = AIota (reverseSubT s x n) (reverseSubT (incFree s 0 1) t (1 + n))
reverseSubT s (AId x y) n = case (s == x , s == y) of
  (True , True)  -> AId (AVj n) (AVj n)
  (False , True) -> AId (reverseSubA s x n) (AVj n)
  (True , False) -> AId (AVj n) (reverseSubA s y n)
  (False , False) -> AId (reverseSubA s x n) (reverseSubA s y n)

reverseSubK :: ADB -> AKind -> Int -> AKind
reverseSubK s AStar n = AStar
reverseSubK s (APik x k) n = APik (reverseSubT s x n) (reverseSubK (incFree s 0 1) k (1 + n))

-- Reverse type substitutions
reverseSubTA :: AType -> ADB  -> Int -> ADB
reverseSubTA s (AVj x) n = case x >= n of
  True -> AVj (1 + x) 
  False -> AVj x
reverseSubTA s (ALamj d) n = ALamj (reverseSubTA (incFree s 0 1) d (1 + n))
reverseSubTA s (AAppj d b) n = AAppj (reverseSubTA s d n) (reverseSubTA s b n)
reverseSubTA s (LAMj d) n = LAMj (reverseSubTA (incFree s 0 1) d (1 + n))
reverseSubTA s (Apptj d x) n = case s == x of
  True -> Apptj (reverseSubTA s d n) (AVt n)
  False -> Apptj (reverseSubTA s d n) (reverseSubTT s x n)
reverseSubTA s (LAMt d) n = LAMt (reverseSubTA (incFree s 0 1) d (1 + n))
reverseSubTA s (Appi d b) n = Appi (reverseSubTA s d n) (reverseSubTA s b n)
reverseSubTA s (IPair d b) n = IPair (reverseSubTA s d n) (reverseSubTA s b n)
reverseSubTA s (Fst d) n = Fst (reverseSubTA s d n)
reverseSubTA s (Snd d) n = Snd (reverseSubTA s d n)
reverseSubTA s Beta n = Beta
reverseSubTA s (Rho d x b) n = case incFree s 0 1 == x of
  True -> Rho (reverseSubTA s d n) (AVt (1 + n)) (reverseSubTA s b n)
  False -> Rho (reverseSubTA s d n) (reverseSubTT (incFree s 0 1) x (1 + n)) (reverseSubTA s b n)

reverseSubTT :: AType -> AType -> Int -> AType
reverseSubTT s (AVt x) n = case x >= n of
  True -> AVt (1 + x)
  False -> AVt x
reverseSubTT s (AAllk x t) n = case (incFree s 0 1) == t of
  True -> AAllk (reverseSubTK s x n) (AVt (1 + n))
  False -> AAllk (reverseSubTK s x n) (reverseSubTT (incFree s 0 1) t (1 + n))
reverseSubTT s (APit x t) n = case (s == x , incFree s 0 1 == t) of
  (True , True)  -> APit (AVt n) (AVt (1 + n))
  (False , True) -> APit (reverseSubTT s x n) (AVt (1 + n))
  (True , False) -> APit (AVt n) (reverseSubTT (incFree s 0 1) t (1 + n))
  (False , False) -> APit (reverseSubTT s x n) (reverseSubTT (incFree s 0 1) t (1 + n))
reverseSubTT s (ALamt x t) n = case (s == x , incFree s 0 1 == t) of
  (True , True)  -> ALamt (AVt n) (AVt (1 + n))
  (False , True) -> ALamt (reverseSubTT s x n) (AVt (1 + n))
  (True , False) -> ALamt (AVt n) (reverseSubTT (incFree s 0 1) t (1 + n))
  (False , False) -> ALamt (reverseSubTT s x n) (reverseSubTT (incFree s 0 1) t (1 + n))
reverseSubTT s (AAppt t x) n = case s == t of
  True -> AAppt (AVt n) (reverseSubTA s x n)
  False -> AAppt (reverseSubTT s t n) (reverseSubTA s x n)
reverseSubTT s (AAllt x t) n = case (s == x , (incFree s 0 1) == t) of
  (True , True)  -> AAllt (AVt n) (AVt (1 + n))
  (False , True) -> AAllt (reverseSubTT s x n) (AVt (1 + n))
  (True , False) -> AAllt (AVt n) (reverseSubTT (incFree s 0 1) t (1 + n))
  (False , False) -> AAllt (reverseSubTT s x n) (reverseSubTT (incFree s 0 1) t (1 + n))
reverseSubTT s (AIota x t) n = case (s == x , (incFree s 0 1) == t) of
  (True , True)  -> AIota (AVt n) (AVt (1 + n))
  (False , True) -> AIota (reverseSubTT s x n) (AVt (1 + n))
  (True , False) -> AIota (AVt n) (reverseSubTT (incFree s 0 1) t (1 + n))
  (False , False) -> AIota (reverseSubTT s x n) (reverseSubTT (incFree s 0 1) t (1 + n))
reverseSubTT s (AId d b) n = AId (reverseSubTA s d n) (reverseSubTA s b n)

reverseSubTK :: AType -> AKind -> Int -> AKind
reverseSubTK s AStar n = AStar
reverseSubTK s (APik x k) n = case s == x of
  True -> APik (AVt n) (reverseSubTK (incFree s 0 1) k (1 + n))
  False -> APik (reverseSubTT s x n) (reverseSubTK (incFree s 0 1) k (1 + n))

{- The Type Checker -}
data Ctx = Empty
         | Snok Ctx AKind
         | Snot Ctx AType

checkKind :: Ctx -> AKind -> Err ()
checkKind Empty AStar = Ok ()
checkKind (Snot g _) AStar = checkKind g AStar >> Ok ()
checkKind (Snok g _) AStar = checkKind g AStar >> Ok ()
checkKind g (APik x k) = checkType g x AStar >> checkKind (Snot g x) k >> Ok ()

inferType :: Ctx -> AType -> Err AKind
inferType g (AVt n) = case (g , n) of
  (Empty , _) -> Bad "Cannot infer Kind of variable in empty context"
  (Snot g _ , 0) -> Bad "Type cannot be infered to be a Kind"
  (Snok g k , 0) -> checkKind g k >> Ok (incFree k 0 1)
  (Snot g k , n) -> case inferType g (AVt (n - 1)) of -- Is there a better way to do this?
    Bad s -> Bad s
    Ok t -> 
      if t == sub (AVj 0) 0 (reverseSubK (AVj 0) t 0)
      then Ok (reverseSubK (AVj 0) t 0)
      else Bad "Cannot weaken type (Type)"
  (Snok g k , n) -> case inferType g (AVt (n - 1)) of -- Is there a better way to do this?
    Bad s -> Bad s
    Ok t -> 
      if t == sub (AVt 0) 0 (reverseSubTK (AVt 0) t 0)
      then Ok (reverseSubTK (AVt 0) t 0)
      else Bad "Cannot weaken type (Kind)"
inferType g (AAllk x tp) = checkKind g x >> checkType (Snok g x) tp AStar >> Ok (AStar)
inferType g (APit tp tpp) = checkType g tp AStar >> checkType (Snot g tp) tpp AStar >> Ok (AStar)
inferType g (ALamt tp tpp) = checkType g tp AStar >> inferType (Snot g tp) tpp >>= \ it -> Ok (APik tp it)
inferType g (AAppt tp t) = case inferType g (sdev tp) of
  Bad s -> Bad s
  Ok (APik tp1 tp2) -> checkTerm g t tp1 >> Ok (sub t 0 tp2)
  Ok _ -> Bad "Non-type-level-product applied durring inference"
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
checkType g (AAllk x tp) AStar = checkKind g x >> checkType (Snok g x) tp AStar >> Ok ()
checkType g (AAllk x tp) _ = Bad "Type-level products can only have AStar kind."
checkType g (APit tp tp1) AStar = checkType g tp AStar >> checkType (Snot g tp) tp1 AStar >> Ok ()
checkType g (APit tp tp1) _ = Bad "Pi types can only have AStar kind."
checkType g (ALamt tp1 tpp) (APik tp2 ka) = case tp1 == tp2 of
  True -> checkType g tp2 AStar >> checkType (Snot g tp2) tpp ka >> Ok ()
  False -> Bad "Lambda binds wring type for Pi" 
checkType g (ALamt tp tpp) _ = Bad "Type-level lambdas can only have type APik"
checkType g (AAppt tp t) ka = case inferType g (sdev (AAppt tp t)) of
  Bad s -> Bad s
  Ok k ->
    if ka == k
    then Ok ()
    else Bad "Failed to unify at type-level application"
checkType g (AAllt tp tpp) AStar = checkType g tp AStar >> checkType (Snot g tp) tpp AStar >> Ok ()
checkType g (AAllt x tp) _ = Bad "Implicit products can only have AStar kind."
checkType g (AIota tp tpp) AStar = checkType g tp AStar >> checkType (Snot g tp) tpp AStar >> Ok ()
checkType g (AIota x tp) _ = Bad "Dependent intersections can only have AStar kind."
checkType g (AId x y) AStar = Ok ()
checkType g (AId x y) _ = Bad "Heterogenious equalities can only have AStar kind."

inferTerm :: Ctx -> ADB -> Err AType
inferTerm g (AVj n) = case (g , n) of
  (Empty , _) -> Bad "Cannot infer term variable in empty context."
  (Snot g x , 0) -> checkType g x AStar >> Ok (sdev (incFree x 0 1))
  (Snok g k , 0) -> Bad "Term cannot be infered to have a kind."
  (Snot g k , n) -> case inferTerm g (AVj (n - 1)) of -- There's got to be a better way to do this.
    Bad s -> Bad s
    Ok t ->
      if t == (sub (AVj 0) 0 (reverseSubT (AVj 0) t 0))
      then Ok (reverseSubT (AVj 0) t 0)
      else Bad "Cannot weaken term (Type)"
  (Snok g k , n) -> case inferTerm g (AVj (n - 1)) of -- There's got to be a better way to do this.
    Bad s -> Bad s
    Ok t -> 
      if t == sub (AVt 0) 0 (reverseSubTT (AVt 0) t 0)
      then Ok (reverseSubTT (AVt 0) t 0)
      else Bad "Cannot weaken term (Kind)"
inferTerm g (ALamj t) = Bad "Cannot infer the type of a lambda term."
inferTerm g (LAMj t) = Bad "Cannot infer the type of an implicit lambda term."
inferTerm g (LAMt t) = Bad "Cannot infer the type of a type-lambda term."
inferTerm g (AAppj (ALamj t) s) = inferTerm g (sub s 0 t) >>= \ ct -> Ok (sdev ct)
inferTerm g (AAppj t t') = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (APit tp1 tp2) -> checkTerm g t' tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a pi type."
inferTerm g (Apptj (LAMt t) s) = inferTerm g (sub s 0 t) >>= \ ct -> Ok (sdev ct)
inferTerm g (Apptj t t') = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (AAllk tp1 tp2) -> checkType g t' tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a type-product type."
inferTerm g (Appi (LAMj t) s) = inferTerm g (sub s 0 t) >>= \ ct -> Ok (sdev ct)
inferTerm g (Appi t t') = case inferTerm g (sdev t) of
  Bad y -> Bad y
  Ok (AAllt tp1 tp2) -> checkTerm g t' tp1 >> Ok (sdev (sub t' 0 tp2))
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
    True -> checkType (Snot g x) tp AStar >> checkType g x AStar >> Ok ()
    False -> Bad "Term does not have correct type."
  (Snok g k , 0) -> checkTerm g (AVj (n - 1)) (sub (AVt 0) 0 tp) >> Ok ()
  (Snot g k , n) -> checkTerm g (AVj (n - 1)) (sub (AVj 0) 0 tp) >> Ok ()
  (Snok g k , n) -> checkTerm g (AVj (n - 1)) (sub (AVj 0) 0 tp) >> Ok ()
checkTerm g (ALamj t) k = case sdev k of
  APit tp1 tp2 -> checkTerm (Snot g tp1) t tp2 >> Ok ()
  _ -> Bad "Lambdas must be pi-types."
checkTerm g (LAMj t) k = case sdev k of
  AAllt tp1 tp2 -> checkTerm (Snot g tp1) t tp2 >> Ok ()
  _ -> Bad "Implicit lambdas must be implicit products."
checkTerm g (LAMt t) k = case sdev k of
  AAllk tp1 tp2 -> checkTerm (Snok g tp1) t tp2 >> Ok ()
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
    then checkTerm g t1 tp1 >> checkTerm g t2 (sub t1 0 tp2) >> Ok ()
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
