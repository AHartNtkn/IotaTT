module AbstractSyntax where

import qualified Data.Map.Strict as Map
import Control.Monad.Reader hiding (liftIO)
import Control.Monad.State hiding (liftIO)
import Control.Monad.Except hiding (liftIO)
import Control.Monad.Trans.Except hiding (liftIO)

-- =*=*=*=*=*=*=*=* Proof Environment Monad *=*=*=*=*=*=*=*=*=

type Proof = ExceptT String (ReaderT [ATerm] (StateT (Map.Map String (ATerm, ATerm)) IO))

runProof :: Proof a -> IO (Either String a, Map.Map String (ATerm, ATerm))
runProof p = runStateT (runReaderT (runExceptT p) []) Map.empty

liftIO :: IO a -> Proof a
liftIO act = lift $ lift $ lift act

proofError :: String -> Proof a
proofError s = do
  liftIO $ putStrLn s
  throwError s

lookupVar :: String -> Proof (ATerm, ATerm)
lookupVar i = do
  tbl <- get
  case Map.lookup i tbl of
    Nothing -> proofError $ "Token " ++ i ++ " not found in context."
    Just t  -> return t

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

{- Annotated Terms -}
data ATerm
  = AV Int
  | AVS String
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

-- Check if a variable occurs free in a term
freeIn (AV x)        n = x == n
freeIn (AVS x)       n = False
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
freeIn AStar         n = False

-- Increment free variables
increaseFree (AV x)       n i = if x >= n then AV (i + x) else AV x
increaseFree (AVS s)      n i = AVS s
increaseFree (ALam d)     n i = ALam   (increaseFree d (1 + n) i)
increaseFree (AAnn d b)   n i = AAnn   (increaseFree d n i) (increaseFree b n i)
increaseFree (AApp d b)   n i = AApp   (increaseFree d n i) (increaseFree b n i)
increaseFree (ALAM d)     n i = ALAM   (increaseFree d (1 + n) i)
increaseFree (AAppi d b)  n i = AAppi  (increaseFree d n i) (increaseFree b n i)
increaseFree (AIPair d b) n i = AIPair (increaseFree d n i) (increaseFree b n i)
increaseFree (AFst d)     n i = AFst   (increaseFree d n i)
increaseFree (ASnd d)     n i = ASnd   (increaseFree d n i)
increaseFree ABeta        n i = ABeta
increaseFree (ARho d t b) n i = ARho   (increaseFree d n i) (increaseFree t (1 + n) i) (increaseFree b n i)
increaseFree (APi t tp)   n i = APi    (increaseFree t n i) (increaseFree tp (1 + n) i)
increaseFree (AIPi t tp)  n i = AIPi   (increaseFree t n i) (increaseFree tp (1 + n) i)
increaseFree (AIota t tp) n i = AIota  (increaseFree t n i) (increaseFree tp (1 + n) i)
increaseFree (AId x y)    n i = AId    (increaseFree x n i) (increaseFree y n i)
increaseFree AStar        n i = AStar

quote s = increaseFree s 0 1

unquote = sub (AV 0) 0

sub s n (AV x) =
  if x >= n
  then (if x == n
        then s
        else AV (x - 1))
  else AV x
sub _ _ (AVS s)       = AVS s
sub s n (ALam d)      = ALam (sub (quote s) (1 + n) d)
sub s n (AAnn d b)    = AAnn (sub s n d) (sub s n b)
sub s n (AApp d b)    = AApp (sub s n d) (sub s n b)
sub s n (ALAM d)      = ALAM (sub (quote s) (1 + n) d)
sub s n (AAppi d b)   = AAppi (sub s n d) (sub s n b)
sub s n (AIPair d b)  = AIPair (sub s n d) (sub s n b)
sub s n (AFst d)      = AFst (sub s n d)
sub s n (ASnd d)      = ASnd (sub s n d)
sub s n ABeta         = ABeta
sub s n (ARho d tp b) = ARho (sub s n d) (sub (quote s) (1 + n) tp) (sub s n b)
sub s n (APi t tp)    = APi (sub s n t) (sub (quote s) (1 + n) tp)
sub s n (AIPi t tp)   = AIPi (sub s n t) (sub (quote s) (1 + n) tp)
sub s n (AIota t tp)  = AIota (sub s n t) (sub (quote s) (1 + n) tp)
sub s n (AId x y)     = AId (sub s n x) (sub s n y)
sub s n AStar         = AStar

-- Weak Head Normal Form
whnf' :: Bool -> ATerm -> Proof ATerm
whnf' names ee = spine ee []
    where spine (AVS s) xs =
            if names -- If true, then remove names. Used only on types.
            then lookupVar s >>= flip spine xs . fst
            else app (AVS s) xs
          spine (AApp f a) xs = spine f (Left a:xs)
          spine (AAppi f a) xs = spine f (Right a:xs)
          spine (AAnn _ tp) xs = spine tp xs
          spine (ALam (AAnn _ e)) (Left a:xs) = spine (sub a 0 e) xs
          spine (ALam e) (Left a:xs) = spine (sub a 0 e) xs

          -- Eta conversion
          spine (ALam (AApp tp (AV 0))) [] =
            if freeIn tp 0 then return $ ALam (AApp tp (AV 0)) else spine (sub (AV 0) 0 tp) []
          spine (ALam (AAnn t (AApp tp (AV 0)))) [] =
            if freeIn tp 0 then return $ ALam (AAnn t (AApp tp (AV 0))) else spine (sub (AV 0) 0 tp) []

          spine (ALAM (AAnn _ e)) (Right a:xs) = spine (sub a 0 e) xs
          spine (ALAM e) (Right a:xs) = spine (sub a 0 e) xs

          -- Eta conversion
          spine (ALAM (AAnn t (AAppi tp (AV 0)))) [] =
            if freeIn tp 0 then return $ ALAM (AAnn t (AAppi tp (AV 0))) else spine (sub (AV 0) 0 tp) []
          spine (ALAM (AAppi tp (AV 0))) [] =
            if freeIn tp 0 then return $ ALAM (AAppi tp (AV 0)) else spine (sub (AV 0) 0 tp) []

          spine (AFst (AIPair d b)) xs = spine d xs
          spine (ASnd (AIPair d b)) xs = spine b xs
          spine (ARho ABeta _ b) xs = spine b xs
          spine f xs = app f xs
          app = (return .) . foldl (flip $ either (flip AApp) (flip AAppi))

whnf = whnf' False
nwhnf = whnf' True

-- Normal Form
nf' :: ATerm -> Proof ATerm
nf' ee = spine ee []
    where spine (AVS s) xs = lookupVar s >>= flip spine xs . fst
          spine (AApp f a)  xs = spine f (Left a:xs)
          spine (AAppi f a) xs = spine f (Right a:xs)
          spine (AAnn _ tp) xs = spine tp xs

          spine (ALam e) (Left a:xs) = spine (sub a 0 e) xs
          -- Eta conversion
          spine (ALam (AApp tp (AV 0))) [] =
            if freeIn tp 0
            then ALam <$> nf' (AApp tp (AV 0))
            else nf' (sub (AV 0) 0 tp)
          spine (ALam (AAnn t (AApp tp (AV 0)))) [] =
            if freeIn tp 0
            then ALam <$> (AAnn t <$> nf' (AApp tp (AV 0)))
            else nf' (sub (AV 0) 0 tp)
          spine (ALam e) [] = ALam <$> nf' e

          spine (ALAM e) (Right a:xs) = spine (sub a 0 e) xs
          -- Eta conversion
          spine (ALAM (AAppi tp (AV 0))) [] =
            if freeIn tp 0
            then ALAM <$> nf' (AAppi tp (AV 0))
            else nf' (sub (AV 0) 0 tp)
          spine (ALAM (AAnn t (AAppi tp (AV 0)))) [] =
            if freeIn tp 0
            then ALAM <$> (AAnn t <$> nf' (AAppi tp (AV 0)))
            else nf' (sub (AV 0) 0 tp)
          spine (ALAM e) [] = ALAM <$> nf' e

          spine (AFst (AIPair d b)) xs = spine d xs
          spine (AFst a) xs = AFst <$> nf' a >>= \f -> app f xs

          spine (ASnd (AIPair d b)) xs = spine b xs
          spine (ASnd a) xs = ASnd <$> nf' a >>= \f -> app f xs

          spine (AId a b) xs = AId <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (AIPair a b) xs = AIPair <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (ARho ABeta _ b) xs = spine b xs
          spine (ARho d x b) xs = ARho <$> nf' d <*> nf' x <*> nf' b >>= \f -> app f xs
          spine (APi a b) xs = APi <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (AIPi a b) xs = AIPi <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (AIota a b) xs = AIota <$> nf' a <*> nf' b >>= \f -> app f xs
          spine f xs = app f xs
          app f xs = foldl (flip $ either (flip AApp) (flip AAppi)) f <$> mapM (either ((Left <$>) . nf') ((Right <$>) . nf')) xs
  -- TO DO: MORE TESTING!!!

nf d = do
  r <- nf' d
  if d == r
  then return r
  else nf r

{- Annotation Erasure -}
erase :: ATerm -> Proof Term
erase (AV x)        = return $ V x
erase (AVS x)       = lookupVar x >>= erase . fst
erase (ALam t)      = Lam <$> erase t
erase (AAnn t t')   = erase t'
erase (AApp t t')   = App <$> erase t <*> erase t'
erase (ALAM t)      = erase (sub (AV 0) 0 t) -- Free variables need to be decremented.
erase (AAppi t t')  = erase t
erase (AIPair t t') = erase t
erase (AFst t)      = erase t
erase (ASnd t)      = erase t
erase ABeta         = return $ Lam (V 0)
erase (ARho _ _ t') = erase t'
erase (APi t t1)    = Pi <$> erase t <*> erase t1
erase (AIPi t t1)   = IPi <$> erase t <*> erase t1
erase (AIota t t1)  = Iota <$> erase t <*> erase t1
erase (AId x x1)    = Id <$> erase x <*> erase x1
erase AStar         = return Star
