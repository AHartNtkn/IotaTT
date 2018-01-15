module TypeChecker where

import qualified Data.Map.Strict as Map
import Control.Monad.Reader hiding (liftIO)
import Control.Monad.State hiding (liftIO)
import Control.Monad.Except hiding (liftIO)
import Control.Monad.Trans.Except hiding (liftIO)

import AbstractSyntax
import PrettyPrinting

infer :: ATerm -> Proof ATerm
infer tr = do
  wtr <- whnf tr
  case wtr of
    AVS s -> snd <$> lookupVar s
    AV s n -> do
      ctx <- ask
      case (ctx , n) of
        ([] , _) -> proofError $ "Cannot infer term variable " ++ pshowA (AV s n) ++ " in empty context."
        ((x : _) , 0) -> local tail $ do
           infer x -- Note: this isn't used, x just needs some type.
           return (quote x)
        ((_ : _) , n) -> local tail (infer (AV s (n - 1))) >>= return . quote
    ALam st (AAnn ty tr) -> do
      liftMin (unquote ty) -- Note: this isn't used, unquote ty just needs some type.
      ity <- local (unquote tr:) (infer tr)
      return (APi st (unquote ty) ity)
    ALam st tr -> proofError $ "Cannot infer the type of unannotated lambda term " ++ pshowA (ALam st tr) ++ "."
    AAnn aty tr -> do
      ctx <- ask
      case ctx of
        (cty : _) -> do
          naty <- nf aty
          ncty <- nf (quote cty)
          if naty == ncty
          then infer tr
          else proofError $ "Type annotation " ++ pshowA aty ++ " didn't match contextual " ++
                            pshowA cty ++ " during inference."
        _ ->  proofError $ "Annotation " ++ pshowA aty ++
                           " appeared without being added to local context during type inference."
    AApp tr1 tr2 -> do
      tr1ty <- nwhnf =<< infer tr1
      case tr1ty of
        APi _ tp1 tp2 -> check tr2 tp1 >> return (sub tr2 tp2)
        _ -> proofError $ "Term " ++ pshowA tr1 ++ " is not a pi type, and so cannot be applied to an argument."
    ALAM st (AAnn ty tr) -> do
      liftMin (unquote ty) -- Note: this isn't used, unquote ty just needs to be a.
      ity <- local (unquote tr:) (infer tr)
      return (AIPi st (unquote ty) ity)
    ALAM st tr -> proofError $ "Cannot infer the type of unannotated implicit lambda term " ++ pshowA (ALam st tr) ++ "."
    AAppi tr1 tr2 -> do
      tr1ty <- nwhnf =<< infer tr1
      case tr1ty of
        AIPi _ tp1 tp2 -> check tr2 tp1 >> return (sub tr2 tp2)
        _ -> proofError $ "Term " ++ pshowA tr1 ++
                          " is not an implicit product type, and so cannot be applied to an argument."
    AIPair tr1 tr2 -> proofError $ "Cannot infer the type of iota constructor " ++ pshowA (AIPair tr1 tr2) ++ "."
    AFst tr -> do
      trty <- nwhnf =<< infer tr
      case trty of
        AIota _ ty1 ty2 -> return ty1
        _ -> proofError $ "Term " ++ pshowA tr ++ " is not a dependent intersection, and so cannot take first element."
    ASnd tr -> do
      trty <- nwhnf =<< infer tr
      case trty of
        AIota _ tp1 tp2 -> return (sub (AFst tr) tp2)
        _ -> proofError $ "Term " ++ pshowA tr ++ " is not a dependent intersection, and so cannot take second element."
    ABeta -> proofError "Identity proofs cannot be inferred."
    ARho st tr1 ty tr2 -> do
      tr1ty <- nwhnf =<< infer tr1
      case tr1ty of
        AId x y -> do 
          check tr2 (sub x ty)
          liftMin (sub x ty) -- Note: this isn't used, unquote ty just needs some type.
          return (sub y ty)
        _ -> proofError $ "Term " ++ pshowA tr1 ++ " is a " ++ pshowA tr1ty  ++ ", not an identity during term inference."
    APi st ty1 ty2 -> do
      liftMin ty1
      local (ty1:) $ do
        i <- liftMin ty2
        return (AU i)
    AIPi st ty1 ty2 -> do
      liftMin ty1
      local (ty1:) $ do
        i <- liftMin ty2
        return (AU i)
    AIota st ty1 ty2 -> do
      liftMin ty1
      local (ty1:) $ do
        i <- liftMin ty2
        return (AU i)
    AId x y -> do
      xty <- infer x
      ix <- liftMin xty
      yty <- infer y
      iy <- liftMin yty
      return (AU (max ix iy))
    AU i -> return (AU (i + 1))

check :: ATerm -> ATerm -> Proof ()
check tr ty = do
  tyw <- nwhnf ty
  case (tr, tyw) of
    (AVS s, ty) -> do
      tbl <- get
      case Map.lookup s tbl of
           Nothing -> proofError $ "Token " ++ s ++ " not found in context during type checking."
           Just (_, t)  -> do
             tynf <- nf ty
             tnf <- nf t
             case (tynf, tnf) of
               (AU j, AU i) ->
                 if i <= j
                 then return ()
                 else proofError $ "Size error during global name lookup. " ++ pshowA tr ++ " of type "
                                    ++ pshowA tnf ++ " is too big for universe " ++ pshowA tynf ++ "."
               _   -> do
                 if tnf == tynf
                 then return ()
                 else proofError $ "Type didn't match during lookup.  Expected something of type "
                                    ++ pshowA tynf ++ "; saw " ++ pshowA (AVS s) ++ " of type " ++ pshowA tnf ++ " instead."
    (AV st n, ty) -> do
      ctx <- ask
      case (ctx , n) of
        ([], _) -> proofError $ "Cannot check type of variable term in an empty context."
        (x:g, 0) -> do
          tynf <- erase =<< nf ty
          xnf  <- erase =<< nf (quote x)
          case (tynf, xnf) of
            (U j, U i) ->
              if i <= j
              then return ()
              else proofError $ "Size error during local variable lookup. " ++ pshowA tr ++ " of type "
                                 ++ pshowA x ++ " is too big for universe " ++ pshowA ty ++ "."
            _ ->
              if tynf == xnf
              then do 
                tyty <- infer ty
                local tail $ check x (unquote tyty)
              else proofError $ "Term does not have correct type. Expected something of type "
                                 ++ pshowA ty ++ "; saw " ++ pshowA (AV st n) ++ " of type " ++ pshowA x ++ " instead."
        (_:g, _) -> local tail $ check (AV st (n - 1)) (unquote ty)
    (ALam st tr, APi _ ty1 ty2) -> local (ty1:) (check tr ty2)
    (ALam st tr, _) -> proofError $ "Lambdas can only be Pi types, not " ++ pshowA tyw ++ "."
    (AAnn aty tr, ty) -> do
      ctx <- ask
      case ctx of
        (cty : _)  -> do
          naty <- nf aty
          ncty <- nf (quote cty)
          case (naty, ncty) of
            (AU j, AU i) ->
              if i <= j
              then return ()
              else proofError $ "Size error during annotation check. " ++ pshowA tr ++ " of type "
                                  ++ pshowA naty ++ " is too big for universe " ++ pshowA ncty ++ "."
            _ ->
              if naty == ncty
              then check tr ty
              else proofError "Type annotation didn't match check."
        _ -> proofError "Annotation appeared without being added to local context."
    (AApp tr1 tr2, ty) -> do
      tynf <- erase =<< nf ty
      itynf <- erase =<< nf =<< infer (AApp tr1 tr2)
      case (tynf, itynf) of
        (U j, U i) ->
          if i <= j
          then return ()
          else proofError $ "Size error during application check. " ++ pshowA (AApp tr1 tr2) ++ " of type "
                              ++ pshowU (itynf) ++ " is too big for universe " ++ pshowA ty ++ "."
        _ ->
          if tynf == itynf
          then do
            liftMin ty
            return () -- Note: this isn't used, ty just needs some type.
          else proofError $ "Failed to unify at application. Expected something of type "
                             ++ pshowA ty ++ "; instead saw " ++ pshowA (AApp tr1 tr2) ++ " of type " ++
                             pshowU (itynf) ++ "."
    (ALAM st tr, AIPi _ ty1 ty2) -> local (ty1:) (check tr ty2)
    (ALAM st tr, _) -> proofError $ "Implicit lambdas can only be implicit products types, not " ++ pshowA tyw ++ "."
    (AAppi tr1 tr2, ty)-> do
      tynf <- erase =<< nf ty
      itynf <- erase =<< nf =<< infer (AAppi tr1 tr2)
      case (tynf, itynf) of
        (U j, U i) ->
          if i <= j
          then return ()
          else proofError $ "Size error during application check. " ++ pshowA (AAppi tr1 tr2) ++ " of type "
                              ++ pshowU (itynf) ++ " is too big for universe " ++ pshowA ty ++ "."
        _ ->
          if tynf == itynf
          then liftMin ty >> return () -- Note: this isn't used, ty just needs some type.
          else proofError $ "Failed to unify at application. Expected something of type "
                             ++ pshowA ty ++ "; instead saw " ++ pshowA (AAppi tr1 tr2) ++ " of type " ++
                             pshowU (itynf) ++ "."
    (AIPair t1 t2, AIota st tp1 tp2) -> do
          nt1 <- erase =<< nf t1
          nt2 <- erase =<< nf t2
          if nt1 == nt2
          then check t1 tp1 >> check t2 (sub t1 tp2)
          else proofError $ "Iota constructor does not erase properly. " ++ pshowA t1 ++ " erases to " ++
                             pshowU nt1 ++ " while " ++ pshowA t2 ++ " erases to " ++ pshowU nt2 ++ "."
    (AIPair t1 t2, _) -> proofError $ "IIota constructor must be a dependent intersection, not " ++ pshowA tyw ++ "."
    (AFst tr, ty) -> do
      ity <- infer (AFst tr)
      nty  <- erase =<< nf ty
      nity <- erase =<< nf ity
      case (nty, nity) of
        (U j, U i) -> 
          if i <= j
          then return () 
          else proofError $ "Size error during iota elimination (#1). " ++ pshowA (AFst tr) ++ " of type "
                              ++ pshowA (ity) ++ " is too big for universe " ++ pshowA ty ++ "."
        _ ->
          if nty == nity
          then infer ty >> return () -- Note: this isn't used, ty just needs some type.
          else proofError $ "Failed to unify at iota elimination. (#1) " ++  pshowA (AFst tr) ++ " of type "
                              ++ pshowA (ity) ++ " is not of type " ++ pshowA ty ++ "."
    (ASnd tr, ty) -> do
      ity <- infer (ASnd tr)
      nty  <- erase =<< nf ty
      nity <- erase =<< nf ity
      case (nty, nity) of
        (U j, U i) -> 
          if i <= j
          then return () 
          else proofError $ "Size error during iota elimination (#2). " ++ pshowA (ASnd tr) ++ " of type "
                              ++ pshowA (ity) ++ " is too big for universe " ++ pshowA ty ++ "."
        _ ->
          if nty == nity
          then infer ty >> return () -- Note: this isn't used, ty just needs some type.
          else proofError $ "Failed to unify at iota elimination. (#2) " ++  pshowA (ASnd tr) ++ " of type "
                              ++ pshowA (ity) ++ " is not of type " ++ pshowA ty ++ "."
    (ABeta, AId t1 t2) -> do
          nt1 <- erase =<< nf t1
          nt2 <- erase =<< nf t2
          if nt1 == nt2
          then return ()
          else proofError $ "Left hand side " ++ pshowA t1 ++ ", which erased to " ++ pshowU nt1 ++
                            ", did not match right hand side " ++ pshowA t2  ++ ", which erased to "
                            ++ pshowU nt2 ++ " during Beta check."
    (ABeta, _) -> proofError "Identity constructor must construct identity."
    (ARho st tr1 x tr2, ty) -> do
      ntr1ty <- nwhnf =<< infer tr1
      case ntr1ty of
        AId t1 t2 -> do
          nty <- erase =<< nf ty
          nt2 <- erase =<< nf (sub t2 x)
          if nty == nt2
          then do
            liftMin ty -- Note: This isn't used, ty just needs to have some type.
            check tr2 (sub t1 x)
          else proofError $ "Left hand side " ++ pshowA ty ++ ", which erased to " ++ pshowU nty ++
                            ", did not match right hand side " ++ pshowA (sub t2 x) ++ ", which erased to "
                            ++ pshowU nt2 ++ " during Rho check."
        _ -> proofError "Term is not an identity during term checking."
    (APi st ty1 ty2, AU i) -> liftMin ty1 >> local (ty1:) (check ty2 (AU i))
    (APi st ty1 ty2, _) -> proofError $ "Pi types can only be in Universe types, not " ++ pshowA tyw ++ "."
    (AIPi st ty1 ty2, AU i) -> liftMin ty1 >> local (ty1:) (check ty2 (AU i))
    (AIPi st ty1 ty2, _) -> proofError $ "Implicit product types can only be in Universe types, not " ++ pshowA tyw ++ "."
    (AIota st ty1 ty2, AU i) -> check ty1 (AU i) >> local (ty1:) (check ty2 (AU i))
    (AIota st ty1 ty2, _) -> proofError $ "Dependent intersections types can only be in Universe types, not " ++ pshowA tyw ++ "."
    (AId x y, AU i) -> do 
          xty <- infer x
          check xty (AU i)
          yty <- infer y
          check yty (AU i)
          return ()
    (AId x y, _) -> proofError $ "Heterogeneous equalities can only be in Universe types, not " ++ pshowA tyw ++ "."
    (AU i, AU j) -> if i < j then return () else proofError $ "Size error, level " ++ show i ++
                                                          " universe is not a term in the level " ++ show j ++ " universe."
    (AU i, _) -> proofError $ "Universes can only exist in other universes, not " ++ pshowA tyw ++ "."

-- Gives the lowest type universe of a term.
liftMin :: ATerm -> Proof Int
liftMin a = do
  aty <- infer a
  case aty of
    AU j -> return j
    _ -> proofError $ "Universe error during lift, " ++ pshowA a ++ " is a " ++ pshowA aty ++ " , not a type ."







