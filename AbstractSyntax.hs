module AbstractSyntax where

import Exp.ErrM

errLookup :: (Show a, Eq a) => a -> [(a, b)] -> Err b
errLookup a l =
  case lookup a l of
    Nothing -> Bad $ "Failed to locate "++ show a ++"."
    Just k -> Ok k

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

{- The context used by the interpreter -}
type TopCtx = [(String, (ATerm, ATerm))]

-- Check if a variable occures free in a term
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

incFree s = increaseFree s 0 1

sub s n (AV x) =
  if x >= n
  then (if x == n
        then s
        else AV (x - 1))
  else AV x
sub _ _ (AVS s)       = AVS s
sub s n (ALam d)      = ALam (sub (incFree s) (1 + n) d)
sub s n (AAnn d b)    = AAnn (sub s n d) (sub s n b)
sub s n (AApp d b)    = AApp (sub s n d) (sub s n b)
sub s n (ALAM d)      = ALAM (sub (incFree s) (1 + n) d)
sub s n (AAppi d b)   = AAppi (sub s n d) (sub s n b)
sub s n (AIPair d b)  = AIPair (sub s n d) (sub s n b)
sub s n (AFst d)      = AFst (sub s n d)
sub s n (ASnd d)      = ASnd (sub s n d)
sub s n ABeta         = ABeta
sub s n (ARho d tp b) = ARho (sub s n d) (sub (incFree s) (1 + n) tp) (sub s n b)
sub s n (APi t tp)    = APi (sub s n t) (sub (incFree s) (1 + n) tp)
sub s n (AIPi t tp)   = AIPi (sub s n t) (sub (incFree s) (1 + n) tp)
sub s n (AIota t tp)  = AIota (sub s n t) (sub (incFree s) (1 + n) tp)
sub s n (AId x y)     = AId (sub s n x) (sub s n y)
sub s n AStar         = AStar

-- Weak Head Normal Form
whnf' :: Bool -> TopCtx -> ATerm -> Err ATerm
whnf' names c ee = spine ee []
    where spine (AVS s) xs =
            if names -- If true, then remove names. Used only on types.
            then errLookup s c >>= flip spine xs . fst
            else app (AVS s) xs
          spine (AApp f a) xs = spine f (Left a:xs)
          spine (AAppi f a) xs = spine f (Right a:xs)
          spine (AAnn _ tp) xs = spine tp xs
          spine (ALam (AAnn _ e)) (Left a:xs) = spine (sub a 0 e) xs
          spine (ALam e) (Left a:xs) = spine (sub a 0 e) xs

          -- Eta conversion
          spine (ALam (AApp tp (AV 0))) [] =
            if freeIn tp 0 then Ok $ ALam (AApp tp (AV 0)) else spine (sub (AV 0) 0 tp) []
          spine (ALam (AAnn t (AApp tp (AV 0)))) [] =
            if freeIn tp 0 then Ok $ ALam (AAnn t (AApp tp (AV 0))) else spine (sub (AV 0) 0 tp) []

          spine (ALAM (AAnn _ e)) (Right a:xs) = spine (sub a 0 e) xs
          spine (ALAM e) (Right a:xs) = spine (sub a 0 e) xs

          -- Eta conversion
          spine (ALAM (AAnn t (AAppi tp (AV 0)))) [] =
            if freeIn tp 0 then Ok $ ALAM (AAnn t (AAppi tp (AV 0))) else spine (sub (AV 0) 0 tp) []
          spine (ALAM (AAppi tp (AV 0))) [] =
            if freeIn tp 0 then Ok $ ALAM (AAppi tp (AV 0)) else spine (sub (AV 0) 0 tp) []

          spine (AFst (AIPair d b)) xs = spine d xs
          spine (ASnd (AIPair d b)) xs = spine b xs
          spine (ARho ABeta _ b) xs = spine b xs
          spine f xs = app f xs
          app = (Ok .) . foldl (flip $ either (flip AApp) (flip AAppi))

whnf = whnf' False
nwhnf = whnf' True

-- Normal Form
nf' :: TopCtx -> ATerm -> Err ATerm
nf' c ee = spine ee []
    where spine (AVS s) xs = errLookup s c >>= flip spine xs . fst
          spine (AApp f a)  xs = spine f (Left a:xs)
          spine (AAppi f a) xs = spine f (Right a:xs)
          spine (AAnn _ tp) xs = spine tp xs

          spine (ALam e) (Left a:xs) = spine (sub a 0 e) xs
          -- Eta conversion
          spine (ALam (AApp tp (AV 0))) [] =
            if freeIn tp 0
            then ALam <$> nf' c (AApp tp (AV 0))
            else nf' c (sub (AV 0) 0 tp)
          spine (ALam (AAnn t (AApp tp (AV 0)))) [] =
            if freeIn tp 0
            then ALam <$> (AAnn t <$> nf' c (AApp tp (AV 0)))
            else nf' c (sub (AV 0) 0 tp)
          spine (ALam e) [] = ALam <$> nf' c e

          spine (ALAM e) (Right a:xs) = spine (sub a 0 e) xs
          -- Eta conversion
          spine (ALAM (AAppi tp (AV 0))) [] =
            if freeIn tp 0
            then ALAM <$> nf' c (AAppi tp (AV 0))
            else nf' c (sub (AV 0) 0 tp)
          spine (ALAM (AAnn t (AAppi tp (AV 0)))) [] =
            if freeIn tp 0
            then ALAM <$> (AAnn t <$> nf' c (AAppi tp (AV 0)))
            else nf' c (sub (AV 0) 0 tp)
          spine (ALAM e) [] = ALAM <$> nf' c e

          spine (AFst (AIPair d b)) xs = spine d xs
          spine (AFst a) xs = AFst <$> nf' c a >>= \f -> app f xs

          spine (ASnd (AIPair d b)) xs = spine b xs
          spine (ASnd a) xs = ASnd <$> nf' c a >>= \f -> app f xs

          spine (AId a b) xs = AId <$> nf' c a <*> nf' c b >>= \f -> app f xs
          spine (AIPair a b) xs = AIPair <$> nf' c a <*> nf' c b >>= \f -> app f xs
          spine (ARho ABeta _ b) xs = spine b xs
          spine (ARho d x b) xs = ARho <$> nf' c d <*> nf' c x <*> nf' c b >>= \f -> app f xs
          spine (APi a b) xs = APi <$> nf' c a <*> nf' c b >>= \f -> app f xs
          spine (AIPi a b) xs = AIPi <$> nf' c a <*> nf' c b >>= \f -> app f xs
          spine (AIota a b) xs = AIota <$> nf' c a <*> nf' c b >>= \f -> app f xs
          spine f xs = app f xs
          app f xs = foldl (flip $ either (flip AApp) (flip AAppi)) f <$> mapM (either ((Left <$>) . nf' c) ((Right <$>) . nf' c)) xs
  -- TO DO: MORE TESTING!!!

nf ctx d =
  let r = nf' ctx d in
    if Ok d == r
    then r
    else r >>= nf ctx

{- Annotation Erasure -}
erase :: TopCtx -> ATerm -> Err Term
erase c (AV x)        = Ok $ V x
erase c (AVS x)       = errLookup x c >>= erase c . fst
erase c (ALam t)      = Lam <$> erase c t
erase c (AAnn t t')   = erase c t'
erase c (AApp t t')   = App <$> erase c t <*> erase c t'
erase c (ALAM t)      = erase c (sub (AV 0) 0 t) -- Free variables need to be decremented.
erase c (AAppi t t')  = erase c t
erase c (AIPair t t') = erase c t
erase c (AFst t)      = erase c t
erase c (ASnd t)      = erase c t
erase c ABeta         = Ok $ Lam (V 0)
erase c (ARho _ _ t') = erase c t'
erase c (APi t t1)    = Pi <$> erase c t <*> erase c t1
erase c (AIPi t t1)   = IPi <$> erase c t <*> erase c t1
erase c (AIota t t1)  = Iota <$> erase c t <*> erase c t1
erase c (AId x x1)    = Id <$> erase c x <*> erase c x1
erase c AStar         = Ok Star
