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
  = V String Int
  | Lam String Term
  | App Term Term
  | Pi String Term Term
  | IPi String Term Term
  | Iota String Term Term
  | Id Term Term
  | U Int
  deriving (Show)

instance Eq Term where
  V s t == V s' t' = t == t'
  Lam _ t == Lam _ t' = t == t'
  App t t2 == App t' t2' = t == t' && t2 == t2'
  Pi _ t t2 == Pi _ t' t2' = t == t' && t2 == t2'
  IPi _ t t2 == IPi _ t' t2' = t == t' && t2 == t2'
  Iota _ t t2 == Iota _ t' t2' = t == t' && t2 == t2'
  Id t t2 == Id t' t2' = t == t' && t2 == t2'
  U t == U t' = t == t'
  _ == _ = False

{- Annotated Terms -}
data ATerm
  = AV String Int
  | AVS String
  | APi String ATerm ATerm
  | ALam String ATerm
  | AAnn ATerm ATerm
  | AApp ATerm ATerm
  | ALAM String ATerm
  | AAppi ATerm ATerm
  | AIPi String ATerm ATerm
  | AIota String ATerm ATerm
  | AIPair ATerm ATerm
  | AFst ATerm
  | ASnd ATerm
  | AId ATerm ATerm
  | ARho String ATerm ATerm ATerm
  | ABeta
  | AU Int
  deriving (Show)

instance Eq (ATerm) where
  AV s t == AV s' t' = t == t'
  AVS t == AVS t' = t == t'
  ALam _ t == ALam _ t' = t == t'
  AAnn t t2 == AAnn t' t2' = t == t' && t2 == t2'
  AApp t t2 == AApp t' t2' = t == t' && t2 == t2'
  APi _ t t2 == APi _ t' t2' = t == t' && t2 == t2'
  AIPi _ t t2 == AIPi _ t' t2' = t == t' && t2 == t2'
  ALAM _ t == ALAM _ t' = t == t'
  AAppi t t2 == AAppi t' t2' = t == t' && t2 == t2'
  AIota _ t t2 == AIota _ t' t2' = t == t' && t2 == t2'
  AIPair t t2 == AIPair t' t2' = t == t' && t2 == t2'
  AFst t == AFst t' = t == t'
  ASnd t == ASnd t' = t == t'
  AId t t2 == AId t' t2' = t == t' && t2 == t2'
  ARho _ t t2 t3 == ARho _ t' t2' t3' = t == t' && t2 == t2' && t3 == t3'
  ABeta == ABeta = True
  AU t == AU t' = t == t'
  _ == _ = False

-- Check if a variable occurs free in a term
freeIn (AV s x)        n = x == n
freeIn (AVS x)         n = False
freeIn (ALam _ d)      n = freeIn d (1 + n)
freeIn (AAnn d d1)     n = freeIn d n || freeIn d1 n
freeIn (AApp d d1)     n = freeIn d n || freeIn d1 n
freeIn (ALAM _ d)      n = freeIn d (1 + n)
freeIn (AAppi d d1)    n = freeIn d n || freeIn d1 n
freeIn (AIPair d d1)   n = freeIn d n || freeIn d1 n
freeIn (AFst d)        n = freeIn d n
freeIn (ASnd d)        n = freeIn d n
freeIn ABeta           n = False
freeIn (ARho _ d tp b) n = freeIn d n || freeIn tp (1 + n) || freeIn b n
freeIn (APi _ t tp)    n = freeIn t n || freeIn tp (1 + n)
freeIn (AIPi _ t tp)   n = freeIn t n || freeIn tp (1 + n)
freeIn (AIota _ t tp)  n = freeIn t n || freeIn tp (1 + n)
freeIn (AId x y)       n = freeIn x n || freeIn y n
freeIn (AU l)          n = False

-- Increment free variables
increaseFree (AV s x)       n i = if x >= n then AV s (i + x) else AV s x
increaseFree (AVS s)        n i = AVS   s
increaseFree (ALam s d)     n i = ALam  s (increaseFree d (1 + n) i)
increaseFree (AAnn d b)     n i = AAnn   (increaseFree d n i) (increaseFree b n i)
increaseFree (AApp d b)     n i = AApp   (increaseFree d n i) (increaseFree b n i)
increaseFree (ALAM s d)     n i = ALAM  s (increaseFree d (1 + n) i)
increaseFree (AAppi d b)    n i = AAppi   (increaseFree d n i) (increaseFree b n i)
increaseFree (AIPair d b)   n i = AIPair  (increaseFree d n i) (increaseFree b n i)
increaseFree (AFst d)       n i = AFst    (increaseFree d n i)
increaseFree (ASnd d)       n i = ASnd    (increaseFree d n i)
increaseFree ABeta          n i = ABeta
increaseFree (ARho s d t b) n i = ARho  s (increaseFree d n i) (increaseFree t (1 + n) i) (increaseFree b n i)
increaseFree (APi s t tp)   n i = APi   s (increaseFree t n i) (increaseFree tp (1 + n) i)
increaseFree (AIPi s t tp)  n i = AIPi  s (increaseFree t n i) (increaseFree tp (1 + n) i)
increaseFree (AIota s t tp) n i = AIota s (increaseFree t n i) (increaseFree tp (1 + n) i)
increaseFree (AId x y)      n i = AId     (increaseFree x n i) (increaseFree y n i)
increaseFree (AU l)         n i = AU l

quote s = increaseFree s 0 1

unquote = sub (AV "" 0)

subn s n (AV st x) =
  case x `compare` n of
    GT -> AV st (x - 1)
    EQ -> s
    LT -> AV st x
subn _ _ (AVS s)          = AVS s
subn s n (ALam st d)      = ALam st (subn (quote s) (1 + n) d)
subn s n (AAnn d b)       = AAnn (subn s n d) (subn s n b)
subn s n (AApp d b)       = AApp (subn s n d) (subn s n b)
subn s n (ALAM st d)      = ALAM st (subn (quote s) (1 + n) d)
subn s n (AAppi d b)      = AAppi (subn s n d) (subn s n b)
subn s n (AIPair d b)     = AIPair (subn s n d) (subn s n b)
subn s n (AFst d)         = AFst (subn s n d)
subn s n (ASnd d)         = ASnd (subn s n d)
subn s n ABeta            = ABeta
subn s n (ARho st d tp b) = ARho st (subn s n d) (subn (quote s) (1 + n) tp) (subn s n b)
subn s n (APi st t tp)    = APi st (subn s n t) (subn (quote s) (1 + n) tp)
subn s n (AIPi st t tp)   = AIPi st (subn s n t) (subn (quote s) (1 + n) tp)
subn s n (AIota st t tp)  = AIota st (subn s n t) (subn (quote s) (1 + n) tp)
subn s n (AId x y)        = AId (subn s n x) (subn s n y)
subn s n (AU l)           = AU l

sub s b = subn s 0 b

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
          spine (ALam st (AAnn _ e)) (Left a:xs) = spine (sub a e) xs
          spine (ALam st e) (Left a:xs) = spine (sub a e) xs

          -- Eta conversion
          spine (ALam st (AApp tp (AV s 0))) [] =
            if freeIn tp 0 then return $ ALam st (AApp tp (AV s 0)) else spine (unquote tp) []
          spine (ALam st (AAnn t (AApp tp (AV s 0)))) [] =
            if freeIn tp 0 then return $ ALam st (AAnn t (AApp tp (AV s 0))) else spine (unquote tp) []

          spine (ALAM st (AAnn _ e)) (Right a:xs) = spine (sub a e) xs
          spine (ALAM st e) (Right a:xs) = spine (sub a e) xs

          -- Eta conversion
          spine (ALAM st (AAnn t (AAppi tp (AV s 0)))) [] =
            if freeIn tp 0 then return $ ALAM st (AAnn t (AAppi tp (AV s 0))) else spine (unquote tp) []
          spine (ALAM st (AAppi tp (AV s 0))) [] =
            if freeIn tp 0 then return $ ALAM st (AAppi tp (AV s 0)) else spine (unquote tp) []

          spine (AFst (AIPair d b)) xs = spine d xs
          spine (ASnd (AIPair d b)) xs = spine b xs
          spine (ARho _ ABeta _ b) xs = spine b xs
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

          spine (ALam st e) (Left a:xs) = spine (sub a e) xs
          -- Eta conversion
          spine (ALam st (AApp tp (AV s 0))) [] =
            if freeIn tp 0
            then ALam st <$> nf' (AApp tp (AV s 0))
            else nf' (unquote tp)
          spine (ALam st (AAnn t (AApp tp (AV s 0)))) [] =
            if freeIn tp 0
            then ALam st <$> (AAnn t <$> nf' (AApp tp (AV s 0)))
            else nf' (unquote tp)
          spine (ALam st e) [] = ALam st <$> nf' e

          spine (ALAM st e) (Right a:xs) = spine (sub a e) xs
          -- Eta conversion
          spine (ALAM st (AAppi tp (AV s 0))) [] =
            if freeIn tp 0
            then ALAM st <$> nf' (AAppi tp (AV s 0))
            else nf' (unquote tp)
          spine (ALAM st (AAnn t (AAppi tp (AV s 0)))) [] =
            if freeIn tp 0
            then ALAM st <$> (AAnn t <$> nf' (AAppi tp (AV s 0)))
            else nf' (unquote tp)
          spine (ALAM st e) [] = ALAM st <$> nf' e

          spine (AFst (AIPair d b)) xs = spine d xs
          spine (AFst a) xs = AFst <$> nf' a >>= \f -> app f xs

          spine (ASnd (AIPair d b)) xs = spine b xs
          spine (ASnd a) xs = ASnd <$> nf' a >>= \f -> app f xs

          spine (AId a b) xs = AId <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (AIPair a b) xs = AIPair <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (ARho st ABeta _ b) xs = spine b xs
          spine (ARho st d x b) xs = ARho st <$> nf' d <*> nf' x <*> nf' b >>= \f -> app f xs
          spine (APi st a b) xs = APi st <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (AIPi st a b) xs = AIPi st <$> nf' a <*> nf' b >>= \f -> app f xs
          spine (AIota st a b) xs = AIota st <$> nf' a <*> nf' b >>= \f -> app f xs
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
erase (AV s x)        = return $ V s x
erase (AVS x)         = lookupVar x >>= erase . fst
erase (ALam st t)     = Lam st <$> erase t
erase (AAnn t t')     = erase t'
erase (AApp t t')     = App <$> erase t <*> erase t'
erase (ALAM _ t)      = erase (unquote t) -- Free variables need to be decremented.
erase (AAppi t t')    = erase t
erase (AIPair t t')   = erase t
erase (AFst t)        = erase t
erase (ASnd t)        = erase t
erase ABeta           = return $ Lam "x" (V "x" 0)
erase (ARho _ _ _ t') = erase t'
erase (APi st t t1)   = Pi st <$> erase t <*> erase t1
erase (AIPi st t t1)  = IPi st <$> erase t <*> erase t1
erase (AIota st t t1) = Iota st <$> erase t <*> erase t1
erase (AId x x1)      = Id <$> erase x <*> erase x1
erase (AU l)          = return (U l)
