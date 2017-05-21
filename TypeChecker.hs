module TypeChecker where

import Exp.ErrM
import AbstractSyntax

data Ctx = Empty
         | Snoc Ctx ATerm

infer :: TopCtx -> Ctx -> ATerm -> Err ATerm
infer c g tr =
  case whnf c tr of
    Ok (AVS s) -> snd <$> errLookup s c
    Ok (AV n) ->
      case (g , n) of
        (Empty , _) -> Bad "Cannot infer term variable in empty context."
        (Snoc g x , 0) -> check c g x AStar >> Ok (incFree x)
        (Snoc g k , n) -> infer c g (AV (n - 1)) >>= Ok . incFree
    Ok (ALam (AAnn ty tr)) ->
      do check c g (sub (AV 0) 0 ty) AStar
         ity <- infer c (Snoc g (sub (AV 0) 0 tr)) tr
         Ok (APi (sub (AV 0) 0 ty) ity)
    Ok (ALam tr) -> Bad "Cannot infer the type of an unannotated lambda term."
    Ok (AAnn aty tr) ->
      case g of
        Snoc g cty ->
          if nf c aty == nf c (incFree cty)
          then infer c (Snoc g cty) tr
          else Bad "Type annotation didn'tr match durring inference."
        _ ->  Bad "Annotation appeared without being added to local context durring type inference."
    Ok (AApp tr1 tr2) ->
      case infer c g tr1 >>= nwhnf c of
        Bad y -> Bad y
        Ok (APi tp1 tp2) -> check c g tr2 tp1 >> Ok (sub tr2 0 tp2)
        Ok _ -> Bad "Term is not a pi type."
    Ok (ALAM (AAnn ty tr)) ->
      do check c g (sub (AV 0) 0 ty) AStar
         ity <- infer c (Snoc g (sub (AV 0) 0 tr)) tr
         Ok (AIPi (sub (AV 0) 0 ty) ity)
    Ok (ALAM tr) -> Bad "Cannot infer the type of an implicit lambda term."
    Ok (AAppi tr1 tr2) ->
      case infer c g tr1 >>= nwhnf c of
        Bad y -> Bad y
        Ok (AIPi tp1 tp2) -> check c g tr2 tp1 >> Ok (sub tr2 0 tp2)
        Ok _ -> Bad "Term is not an implicit product type."
    Ok (AIPair tr1 tr2) -> Bad "Cannot infer the type of an iota constructor."
    Ok (AFst tr) ->
      case infer c g tr >>= nwhnf c of
        Bad y -> Bad y
        Ok (AIota ty1 ty2) -> Ok ty1
        _ -> Bad "Term is not an iota constructor (#1)."
    Ok (ASnd tr) ->
      case infer c g tr >>= nwhnf c of
        Bad y -> Bad y
        Ok (AIota tp1 tp2) -> Ok (sub (AFst tr) 0 tp2)
        _ -> Bad "Term is not an iota constructor (#2)."
    Ok ABeta -> Bad "Identity proofs cannot be inferred."
    Ok (ARho tr1 ty tr2) ->
      case infer c g tr1 >>= nwhnf c of
        Bad y -> Bad y
        Ok (AId x y) -> check c g tr2 (sub x 0 ty) >> check c g (sub x 0 ty) AStar >> Ok (sub y 0 ty)
        Ok _ -> Bad "Term is not an identity durring term inferrence."
    Ok (APi ty1 ty2) -> check c g ty1 AStar >> check c (Snoc g ty1) ty2 AStar >> Ok AStar
    Ok (AIPi ty1 ty2) -> check c g ty1 AStar >> check c (Snoc g ty1) ty2 AStar >> Ok AStar
    Ok (AIota ty1 ty2) -> check c g ty1 AStar >> check c (Snoc g ty1) ty2 AStar >> Ok AStar
    Ok (AId x y) -> Ok AStar -- Perhapse a check should be added to verify that x and y are valid terms
    Ok AStar -> Ok AStar

check :: TopCtx -> Ctx -> ATerm -> ATerm -> Err ()
check c g tr ty =
  case tr of
    AVS s ->
      do cty <- snd <$> errLookup s c
         if nf c cty == nf c ty
         then Ok ()
         else Bad "Type didn't match durring lookup."
    AV n ->
      case (g , n) of
        (Empty , _) -> Bad "Cannot check type of variable term in an empty context."
        (Snoc g x , 0) ->
          if (nf c ty >>= erase c) == (nf c (incFree x) >>= erase c)
          then check c (Snoc g x) ty AStar >> check c g x AStar
          else Bad "Term does not have correct type."
        (Snoc g _ , n) -> check c g (AV (n - 1)) (sub (AV 0) 0 ty)
    ALam tr ->
      case nwhnf c ty of
        Ok (APi ty1 ty2) -> check c (Snoc g ty1) tr ty2
        _ -> Bad "Lambdas can only be Pi types."
    AAnn aty tr ->
      case g of
        Snoc g cty ->
          if nf c aty == nf c (incFree cty)
          then check c (Snoc g cty) tr ty
          else Bad "Type annotation didn'tr match check."
        _ -> Bad "Annotation appeared without being added to local context."
    AApp tr1 tr2 ->
      do ity <- infer c g (AApp tr1 tr2)
         if (nf c ty >>= erase c) == (nf c ity >>= erase c)
         then check c g ty AStar
         else Bad "Failed to unify at application."
    ALAM tr ->
      case nwhnf c ty of
        Ok (AIPi ty1 ty2) -> check c (Snoc g ty1) tr ty2
        _ -> Bad "Implicit lambdas must be implicit products."
    AAppi tr1 tr2 ->
      do ity <- infer c g (AAppi tr1 tr2)
         if (nf c ty >>= erase c) == (nf c ity >>= erase c)
         then check c g ty AStar
         else Bad "Failed to unify at implicit application."
    AIPair t1 t2 ->
      case nwhnf c ty of
        Ok (AIota tp1 tp2) ->
          if (nf c t1 >>= erase c) == (nf c t2 >>= erase c)
          then check c g t1 tp1 >> check c g t2 (sub t1 0 tp2)
          else Bad "Iota constructor does not erase properly."
        _ -> Bad "Iota contructor must be a dependent intersection."
    AFst tr ->
      do ity <- infer c g (AFst tr)
         if (nf c ty >>= erase c) == (nf c ity >>= erase c)
         then check c g ty AStar
         else Bad "Failed to unify at iota elimination. (#1)"
    ASnd tr ->
      do ity <- infer c g (ASnd tr)
         if (nf c ty >>= erase c) == (nf c ity >>= erase c)
         then check c g ty AStar
         else Bad "Failed to unify at iota elimination. (#2)"
    ABeta ->
      case nwhnf c ty of
        Ok (AId t1 t2) ->
          if (nf c t1 >>= erase c) == (nf c t2 >>= erase c)
          then Ok ()
          else Bad "Lhs does not match rhs of identity."
        _ -> Bad "Identity constructor must construct identity."
    ARho tr1 x tr2 ->
      case infer c g tr1 >>= nwhnf c of
        Bad s -> Bad s
        Ok (AId t1 t2) ->
          if (nf c ty >>= erase c) == (nf c (sub t2 0 x) >>= erase c)
          then check c g ty AStar >> check c g tr2 (sub t1 0 x)
          else Bad "LHS and RHS of identity don't match after erasure."
        Ok _ -> Bad "Term is not an identity durring term checking."
    APi ty1 ty2 ->
      case nwhnf c ty of
        Ok AStar -> check c g ty1 AStar >> check c (Snoc g ty1) ty2 AStar
        _ -> Bad "Pi types can only have type *."
    AIPi ty1 ty2 ->
      case nwhnf c ty of
        Ok AStar -> check c g ty1 AStar >> check c (Snoc g ty1) ty2 AStar
        _ -> Bad "Implicit products can only have type *."
    AIota ty1 ty2 ->
      case nwhnf c ty of
        Ok AStar -> check c g ty1 AStar >> check c (Snoc g ty1) ty2 AStar
        _ -> Bad "Dependent intersections can only have type *."
    AId x y ->
      case nwhnf c ty of
        Ok AStar -> Ok () -- Perhapse a better check is needed. x and y *should* be valid terms.
        _ -> Bad "Heterogenious equalities can only have type *."
    AStar ->
      case nwhnf c ty of
        Ok AStar -> Ok ()
        _ -> Bad "* can only have type *."
