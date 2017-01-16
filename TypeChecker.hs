{-# language MultiParamTypeClasses #-}

module TypeChecker where

import ErrM
import AbstractSyntax

{- Handle dimention variables -}
dimSub :: TopCtx -> ((Ctx , ATerm) , (Ctx , ATerm)) -> Int -> Err (ATerm , ATerm)
dimSub c ((g1, AV n1), (g2, AV n2)) n = if n1 == n2 then Ok (AV n1 , AV n2) else Bad "Bound vars didn't match."
dimSub c ((g1, AVS x1), (g2, AVS x2)) n = if x1 == x2 then Ok (AVS x1, AVS x2) else Bad "Defined vars didn't match."
dimSub c ((g1, ALam (AAnn ty1 e1)), (g2, ALam (AAnn ty2 e2))) n =
  dimSub c ((Snoc g1 (sub (AV 0) 0 ty1), e1), (Snoc g2 (sub (AV 0) 0 ty2), e2)) (1 + n) >>= \(fs, sn) ->
  Ok (ALam fs , ALam sn)
dimSub c ((g1, ALam e1), (g2, ALam e2)) n =
  dimSub c ((Snoc g1 (APi AStar (APi (AV 0) (AV 0))), e1),
            (Snoc g2 (APi AStar (APi (AV 0) (AV 0))), e2)) (1 + n) >>= \(fs, sn) ->
  Ok (ALam fs , ALam sn)
dimSub c ((g1, ALAM (AAnn ty1 e1)), (g2, ALAM (AAnn ty2 e2))) n =
  dimSub c ((Snoc g1 (sub (AV 0) 0 ty1), e1), (Snoc g2 (sub (AV 0) 0 ty2), e2)) (1 + n) >>= \(fs, sn) ->
  Ok (ALAM fs , ALAM sn)
dimSub c ((g1, ALAM e1), (g2, ALAM e2)) n =
  dimSub c ((Snoc g1 (APi AStar (APi (AV 0) (AV 0))), e1),
            (Snoc g2 (APi AStar (APi (AV 0) (AV 0))), e2)) (1 + n) >>= \(fs, sn) ->
  Ok (ALAM fs , ALAM sn)
dimSub c ((g1, APB e1), (g2, APB e2)) n =
  dimSub c ((Snoc g1 AI, e1), (Snoc g2 AI, e2)) (1 + n) >>= \(fs, sn) ->
  Ok (APB fs , APB sn)
dimSub c ((g1, AApp e11 e12), (g2, AApp e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) n >>= \(e12, e22) ->
  Ok (AApp e11 e12 , AApp e21 e22)
dimSub c ((g1, AAppi e11 e12), (g2, AAppi e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) n >>= \(e12, e22) ->
  Ok (AAppi e11 e12 , AAppi e21 e22)
dimSub c ((g1, AIPair e11 e12), (g2, AIPair e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) n >>= \(e12, e22) ->
  Ok (AIPair e11 e12 , AIPair e21 e22)
dimSub c ((g1, AFst e1), (g2, AFst e2)) n =
  dimSub c ((g1, e1), (g2, e2)) n >>= \(e1, e2) ->
  Ok (AFst e1 , AFst e2)
dimSub c ((g1, ASnd e1), (g2, ASnd e2)) n =
  dimSub c ((g1, e1), (g2, e2)) n >>= \(e1, e2) ->
  Ok (ASnd e1 , ASnd e2)
dimSub c ((g1, AT0), (g2, AT0)) n = Ok (AT0, AT0)
dimSub c ((g1, AT1), (g2, AT1)) n = Ok (AT1, AT1)
dimSub c ((g1, AI), (g2, AI)) n = Ok (AI, AI)
dimSub c ((g1, AId e11 e12), (g2, AId e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) n >>= \(e12, e22) ->
  Ok (AId e11 e12 , AId e21 e22)
dimSub c ((g1, AStar), (g2, AStar)) n = Ok (AStar, AStar)
dimSub c ((g1, APi e11 e12), (g2, APi e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) (1 + n) >>= \(e12, e22) ->
  Ok (APi e11 e12 , APi e21 e22)
dimSub c ((g1, AIPi e11 e12), (g2, AIPi e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) (1 + n) >>= \(e12, e22) ->
  Ok (AIPi e11 e12 , AIPi e21 e22)
dimSub c ((g1, AIota e11 e12), (g2, AIota e21 e22)) n =
  dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
  dimSub c ((g1, e12), (g2, e22)) (1 + n) >>= \(e12, e22) ->
  Ok (AIota e11 e12 , AIota e21 e22)
dimSub c ((g1, ARho e11 ty1 e12), (g2, ARho e21 ty2 e22)) n =
  if freeIn ty1 (n + 1) && freeIn ty2 (n + 1)
  then
    dimSub c ((g1, e11), (g2, e21)) n >>= \(e11, e21) ->
    dimSub c ((g1, e12), (g2, e22)) (1 + n) >>= \(e12, e22) ->
    Ok (ARho e11 ty1 e12 , ARho e21 ty2 e22)
  else Bad "Path variables cannot apear in Rho patterns."
dimSub c ((g1, APApp e1 n0), (g2, APApp e2 n1)) n =
  if n0 == AT0 && n1 == AT1
  then
    case infer c g1 e1 >>= ssdev c of
      Ok (AId lf ri) -> Ok (lf , ri)
      Bad s -> Bad s
      _ -> Bad "Cannot apply path variable to non-path"
  else 
    dimSub c ((g1, e1), (g2, e2)) n >>= \(e1, e2) ->
    Ok (AApp e1 n0 , AApp e2 n1)
-- Remove loose anotations
dimSub c ((g1, AAnn a1 e1), (g2, e2)) n = dimSub c ((g1, e1), (g2, e2)) n
dimSub c ((g1, e1), (g2, AAnn a1 e2)) n = dimSub c ((g1, e1), (g2, e2)) n
dimSub c _ _ = Bad "LHS and RHS of path expression didn't match."

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
  if (normalize c t1 == normalize c (incFree tp1 0 1))
  then infer c (Snoc g tp1) (sdev t2)
  else Bad "Type annotation didn't match durring inference."
infer c g (AApp (ALam t) s) = infer c g (sub s 0 t) >>= Ok . sdev
infer c g (AApp t t') = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok (APi tp1 tp2) -> check c g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not a pi type."
infer c g (ALAM (AAnn tp tpp))
  = check c g (sub (AV 0) 0 tp) AStar >>
    infer c (Snoc g (sub (AV 0) 0 tp)) tpp >>= \ it ->
    Ok (AIPi (sub (AV 0) 0 tp) it)
infer c g (ALAM t) = Bad "Cannot infer the type of an unannotated implicit lambda term."
infer c g (AAppi (ALAM t) s) = infer c g (sub s 0 t) >>= Ok . sdev
infer c g (AAppi t t') = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok (AIPi tp1 tp2) -> check c g (sdev t') tp1 >> Ok (sdev (sub t' 0 tp2))
  Ok _ -> Bad "Term is not an implicit product type."
infer c g (AIPair t t') = Bad "Cannot infer the type of an iota constructor."
infer c g (AFst t) = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok (AIota tp1 tp2) -> Ok (sdev tp1)
  Ok _ -> Bad "Term is not an iota constructor (#1)."
infer c g (ASnd t) = case infer c g (sdev t) of
  Bad y -> Bad y
  Ok (AIota tp1 tp2) -> Ok (sdev (sub (AFst t) 0 tp2))
  Ok _ -> Bad "Term is not an iota constructor (#2)."
infer c g (ARho t' tp t) = case infer c g (sdev t') of
  Bad y -> Bad y
  Ok (AId t1 t2) ->
    check c g t (sub t1 0 tp) >> check c g (sub t1 0 tp) AStar >> Ok (sdev (sub t2 0 tp))
  Ok _ -> Bad "Term is not an identity durring term inferrence"
infer c g (APi tp tpp) = check c g tp AStar >> check c (Snoc g tp) tpp AStar >> Ok AStar
infer c g (AIPi tp tpp) = check c g tp AStar >> check c (Snoc g tp) tpp AStar >> Ok AStar
infer c g (AIota tp tpp) = check c g tp AStar >> check c (Snoc g tp) tpp AStar >> Ok AStar
infer c g (AId x y) = Ok AStar
infer c g AT0 = Ok AI
infer c g AT1 = Ok AI
infer c g AI = Ok AStar
infer c g (APB a) = 
  do 
    (fs , sn) <- dimSub c ((g, sub AT0 0 a), (g, sub AT1 0 a)) 0
    Ok $ AId fs sn
infer c g (APApp a b) = Bad "Cannot infer the type of a naked path application."
infer c g AStar = Ok AStar

check :: TopCtx -> Ctx -> ATerm -> ATerm -> Err ()
check c g k (AVS s) =
  do
    ty <- errLookup s c
    check c g k (fst ty)
check c g (AV n) tp = case (g , n) of 
  (Empty , _) -> Bad "Cannot check type of variable term in an empty context."
  (Snoc g x , 0) -> 
    do
      etp <- erase c tp
      ee  <- erase c (incFree x 0 1)
      if normalize [] etp == normalize [] ee
      then check c (Snoc g (sdev x)) (sdev tp) AStar >> check c g (sdev x) AStar >> Ok ()
      else Bad "Term does not have correct type."
  (Snoc g k , n) -> check c g (AV (n - 1)) (sub (AV 0) 0 tp) >> Ok ()
check c g (AVS s) tp = 
  do
    ts <- errLookup s c
    if normalize c (snd ts) == normalize c tp
    then Ok ()
    else Bad "Type didn't match durring name lookup."
check c g (ALam t) k = case ssdev c k of
  Ok (APi tp1 tp2) -> check c (Snoc g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Lambdas can only be Pi types"
check c (Snoc g tp1) (AAnn t1 t2) tp2 =
    if (normalize c t1 == normalize c (incFree tp1 0 1))
    then check c (Snoc g tp1) (sdev t2) tp2 >> Ok ()
    else Bad "Type annotation didn't match check."
check c g (AApp (ALam t) s) tp = check c g (sub s 0 t) tp >> Ok ()
check c g (AApp t t1) tp = infer c g (sdev (AApp t t1)) >>= \k ->
    do
      etp <- erase c tp
      ek <- erase c k
      if normalize [] etp == normalize [] ek
      then check c g tp AStar >> Ok ()
      else Bad "Failed to unify at application"
check c g (ALAM t) k = case ssdev c k of
  Ok (AIPi tp1 tp2) -> check c (Snoc g tp1) (sdev t) tp2 >> Ok ()
  _ -> Bad "Implicit lambdas must be implicit products."
check c g (AAppi (ALAM t) s) tp = check c g (sub s 0 t) tp >> Ok ()
check c g (AAppi t t1) tp = infer c g (sdev (AAppi t t1)) >>= \ k ->
    do
      etp <- erase c tp
      ek <- erase c k
      if normalize [] etp == normalize [] ek
      then check c g tp AStar >> Ok ()
      else Bad "Failed to unify at implicit application"
check c g (AIPair t1 t2) k = case ssdev c k of
  Ok (AIota tp1 tp2) ->
    do
      et1 <- erase c t1
      et2 <- erase c t2
      if normalize [] et1 == normalize [] et2
      then check c g (sdev t1) tp1 >> check c g (sdev t2) (sub (sdev t1) 0 tp2) >> Ok ()
      else Bad "Iota constructor does not erase properly."
  _ -> Bad "Iota contructor must be a dependent intersection."
check c g (AFst t) tp = infer c g (AFst (sdev t)) >>= \k ->
    do
      etp <- erase c tp
      ek <- erase c k
      if normalize [] etp == normalize [] ek
      then check c g tp AStar >> Ok ()
      else Bad "Failed to unify at iota elimination (#1)"
check c g (ASnd t) tp = infer c g (ASnd (sdev t)) >>= \k ->
    do
      etp <- erase c tp
      ek <- erase c k
      if normalize [] etp == normalize [] ek
      then check c g tp AStar >> Ok ()
      else Bad "Failed to unify at iota elimination (#2)"
check c g (ARho t' x t) tp = case infer c g (sdev t') of
  Bad s -> Bad s
  Ok (AId t1 t2) ->
    do
      etp <- erase c tp
      et2 <- erase c (sub t2 0 x)
      ntp <- normalize [] etp
      nt2 <- normalize [] et2
      if ntp == nt2
      then check c g tp AStar >> check c g (sdev t) (sub t1 0 x) >> Ok ()
      else Bad "LHS and RHS of identity don't match after erasure"
  Ok _ -> Bad "Term is not an identity durring term checking"
check c g (APi tp tp1) AStar = check c g tp AStar >> check c (Snoc g tp) tp1 AStar >> Ok ()
check c g (APi tp tp1) _ = Bad "Pi types can only have AStar kind."
check c g (AIPi tp tpp) AStar = check c g (sdev tp) AStar >> check c (Snoc g (sdev tp)) (sdev tpp) AStar >> Ok ()
check c g (AIPi x tp) _ = Bad "Implicit products can only have AStar kind."
check c g (AIota tp tpp) AStar = check c g (sdev tp) AStar >> check c (Snoc g (sdev tp)) (sdev tpp) AStar >> Ok ()
check c g (AIota x tp) _ = Bad "Dependent intersections can only have AStar kind."
check c g (AId x y) AStar = Ok ()
check c g (AId x y) _ = Bad "Heterogenious equalities can only have AStar kind."
check c g AT0 AI = Ok () 
check c g AT0 _ = Bad "A0 can only have type AI."
check c g AT1 AI = Ok () 
check c g AT1 _ = Bad "A1 can only have type AI."
check c g AI AStar = Ok () 
check c g AI _ = Bad "AI can only have type *."
check c g (APB a) k = case ssdev c k of
  Ok (AId t1 t2) ->
    do
      (fs , sn) <- dimSub c ((g, sub AT0 0 a), (g, sub AT1 0 a)) 0
      nfs <- normalize [] <$> erase c fs
      nsn <- normalize [] <$> erase c sn
      nt1 <- normalize [] <$> erase c t1
      nt2 <- normalize [] <$> erase c t2
      if nfs == nt1 && nsn == nt2
      then Ok ()
      else Bad "LHS and RHS of path don't match"
  _ -> Bad "Identity path constructor must construct identity."
check c g (APApp a b) _ = Bad "Cannot check the type of a naked path application."
check c g AStar AStar = Ok () 
check c g AStar _ = Bad "* can only have type *."
