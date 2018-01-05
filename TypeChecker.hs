module TypeChecker where

import Control.Monad.Reader hiding (liftIO)
import Control.Monad.State hiding (liftIO)
import Control.Monad.Except hiding (liftIO)
import Control.Monad.Trans.Except hiding (liftIO)

import AbstractSyntax

infer :: ATerm -> Proof ATerm
infer tr = do
  wtr <- whnf tr
  case wtr of
    AVS s -> snd <$> lookupVar s
    AV n -> do
      ctx <- ask
      case (ctx , n) of
        ([] , _) -> proofError "Cannot infer term variable in empty context."
        ((x : _) , 0) -> local tail (check x AStar) >> return (quote x)
        ((_ : _) , n) -> local tail (infer (AV (n - 1))) >>= return . quote
    ALam (AAnn ty tr) -> do
      check (unquote ty) AStar
      ity <- local (unquote tr:) (infer tr)
      return (APi (unquote ty) ity)
    ALam tr -> proofError "Cannot infer the type of an unannotated lambda term."
    AAnn aty tr -> do
      ctx <- ask
      case ctx of
        (cty : _) -> do
          naty <- nf aty
          ncty <- nf (quote cty)
          if naty == ncty
          then infer tr
          else proofError "Type annotation didn't match during inference."
        _ ->  proofError "Annotation appeared without being added to local context durring type inference."
    AApp tr1 tr2 -> do
      tr1ty <- nwhnf =<< infer tr1
      case tr1ty of
        APi tp1 tp2 -> check tr2 tp1 >> return (sub tr2 0 tp2)
        _ -> proofError "Term is not a pi type."
    ALAM (AAnn ty tr) -> do
      check (unquote ty) AStar
      ity <- local (unquote tr:) (infer tr)
      return (AIPi (unquote ty) ity)
    ALAM tr -> proofError "Cannot infer the type of an implicit lambda term."
    AAppi tr1 tr2 -> do
      tr1ty <- nwhnf =<< infer tr1
      case tr1ty of
        AIPi tp1 tp2 -> check tr2 tp1 >> return (sub tr2 0 tp2)
        _ -> proofError "Term is not an implicit product type."
    AIPair tr1 tr2 -> proofError "Cannot infer the type of an iota constructor."
    AFst tr -> do
      trty <- nwhnf =<< infer tr
      case trty of
        AIota ty1 ty2 -> return ty1
        _ -> proofError "Term is not an iota constructor (#1)."
    ASnd tr -> do
      trty <- nwhnf =<< infer tr
      case trty of
        AIota tp1 tp2 -> return (sub (AFst tr) 0 tp2)
        _ -> proofError "Term is not an iota constructor (#2)."
    ABeta -> proofError "Identity proofs cannot be inferred."
    ARho tr1 ty tr2 -> do
      tr1ty <- nwhnf =<< infer tr1
      case tr1ty of
        AId x y -> check tr2 (sub x 0 ty) >> check (sub x 0 ty) AStar >> return (sub y 0 ty)
        _ -> proofError "Term is not an identity durring term inferrence."
    APi ty1 ty2 -> check ty1 AStar >> local (ty1:) (check ty2 AStar) >> return AStar
    AIPi ty1 ty2 -> check ty1 AStar >> local (ty1:) (check ty2 AStar) >> return AStar
    AIota ty1 ty2 -> check ty1 AStar >> local (ty1:) (check ty2 AStar) >> return AStar
    AId x y -> return AStar -- Perhaps a check should be added to verify that x and y are valid terms
    AStar -> return AStar

check :: ATerm -> ATerm -> Proof ()
check tr ty =
  case tr of
    AVS s ->
      do ncty <- nf =<< snd <$> lookupVar s
         nty  <- nf ty
         if ncty == nty
         then return ()
         else proofError "Type didn't match durring lookup."
    AV n -> do
      ctx <- ask
      case (ctx , n) of
        ([] , _) -> proofError "Cannot check type of variable term in an empty context."
        ((x : _) , 0) -> do
          nty  <- erase =<< nf ty
          nqty <- erase =<< nf (quote x)
          if nty == nqty
          then check ty AStar >> local tail (check x AStar)
          else proofError "Term does not have correct type."
        ((_ : _) , n) -> local tail (check (AV (n - 1)) (unquote ty))
    ALam tr -> do
      nty <- nwhnf ty
      case nty of
        APi ty1 ty2 -> local (ty1:) (check tr ty2)
        _ -> proofError "Lambdas can only be Pi types."
    AAnn aty tr -> do
      ctx <- ask
      case ctx of
        (cty : _)  -> do
          naty <- nf aty
          ncty <- nf (quote cty)
          if naty == ncty
          then check tr ty
          else proofError "Type annotation didn't match check."
        _ -> proofError "Annotation appeared without being added to local context."
    AApp tr1 tr2 -> do
      ity <- infer (AApp tr1 tr2)
      nty  <- erase =<< nf ty
      nity <- erase =<< nf ity
      if nty == nity
      then check ty AStar
      else proofError "Failed to unify at application."
    ALAM tr -> do
      nty <- nwhnf ty
      case nty of
        AIPi ty1 ty2 -> local (ty1:) (check tr ty2)
        _ -> proofError "Implicit lambdas must be implicit products."
    AAppi tr1 tr2 -> do
      ity <- infer (AAppi tr1 tr2)
      nty  <- erase =<< nf ty
      nity <- erase =<< nf ity
      if nty == nity
      then check ty AStar
      else proofError "Failed to unify at implicit application."
    AIPair t1 t2 -> do
      nty <- nwhnf ty
      case nty of
        AIota tp1 tp2 -> do
          nt1 <- erase =<< nf t1
          nt2 <- erase =<< nf t2
          if nt1 == nt2
          then check t1 tp1 >> check t2 (sub t1 0 tp2)
          else proofError "Iota constructor does not erase properly."
        _ -> proofError "Iota constructor must be a dependent intersection."
    AFst tr -> do
      ity <- infer (AFst tr)
      nty  <- erase =<< nf ty
      nity <- erase =<< nf ity
      if nty == nity
      then check ty AStar
      else proofError "Failed to unify at iota elimination. (#1)"
    ASnd tr -> do
      ity <- infer (ASnd tr)
      nty  <- erase =<< nf ty
      nity <- erase =<< nf ity
      if nty == nity
      then check ty AStar
      else proofError "Failed to unify at iota elimination. (#2)"
    ABeta -> do
      nty <- nwhnf ty
      case nty of
        AId t1 t2 -> do
          nt1 <- erase =<< nf t1
          nt2 <- erase =<< nf t2
          if nt1 == nt2
          then return ()
          else proofError "Lhs does not match rhs of identity."
        _ -> proofError "Identity constructor must construct identity."
    ARho tr1 x tr2 -> do
      ntr1ty <- nwhnf =<< infer tr1
      case ntr1ty of
        AId t1 t2 -> do
          nty <- erase =<< nf ty
          nt2 <- erase =<< nf (sub t2 0 x)
          if nty == nt2
          then check ty AStar >> check tr2 (sub t1 0 x)
          else proofError "LHS and RHS of identity don't match after erasure."
        _ -> proofError "Term is not an identity during term checking."
    APi ty1 ty2 -> do
      nty <- nwhnf ty
      case nty of
        AStar -> check ty1 AStar >> local (ty1:) (check ty2 AStar)
        _ -> proofError "Pi types can only have type *."
    AIPi ty1 ty2 -> do
      nty <- nwhnf ty
      case nty of
        AStar -> check ty1 AStar >> local (ty1:) (check ty2 AStar)
        _ -> proofError "Implicit products can only have type *."
    AIota ty1 ty2 -> do
      nty <- nwhnf ty
      case nty of
        AStar -> check ty1 AStar >> local (ty1:) (check ty2 AStar)
        _ -> proofError "Dependent intersections can only have type *."
    AId x y -> do
      nty <- nwhnf ty
      case nty of
        AStar -> return () -- Perhaps a better check is needed. x and y *should* be valid terms.
        _ -> proofError "Heterogeneous equalities can only have type *."
    AStar -> do
      nty <- nwhnf ty
      case nty of
        AStar -> return ()
        _ -> proofError "* can only have type *."
