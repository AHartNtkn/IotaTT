{-# language LambdaCase #-}

module RawSyntax where

import AbstractSyntax
import PrettyPrinting

-- Representation for printing
import AbsExp
import ErrM

import Control.Monad
import Data.String

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HM

{- The context used by the interpreter -}
type TopCtx = [(String, Either (AType, AKind) (ADB, AType))]

errLookup :: (Show a, Eq a) => a -> [(a, b)] -> Err b
errLookup a l = (\case { Nothing -> Bad ("Failed to locate "++ show a++".") ; Just k -> Ok k}) (lookup a l)

{- Intermediate raw instax -}
data IADB
   = IVSj String
   | IVj Int
   | ILamj String IADB
   | IAppj IADB IADB
   | ILAMj String IADB
   | IApptj IADB IType
   | ILAMt String IADB
   | IAppi IADB IADB
   | IIPair IADB IADB
   | IFst IADB
   | ISnd IADB
   | IBeta
   | IRho IADB String IType IADB
   deriving (Show)

data IType
   = IVSt String
   | IVt Int
   | IAllk String IKind IType
   | IPit String IType IType
   | ILamt String IType IType
   | IAppt IType IADB
   | IAllt String IType IType
   | IIota String IType IType
   | IId IADB IADB
   deriving (Show)

data IKind
   = IStar
   | IPik String IType IKind
   deriving (Show)

{- Convert intermediate syntax into abstract syntax -}

-- Replace string variables with deBruijin indices
indexA :: String -> Int -> IADB -> IADB
indexA s n (IVSj x) = if s == x then IVj n else IVSj x
indexA s n (IVj x) = IVj x
indexA s n (ILamj x d) = ILamj x (indexA s (1 + n) (indexA x 0 d))
indexA s n (IAppj d d1) = IAppj (indexA s n d) (indexA s n d1)
indexA s n (ILAMj x d) = ILAMj x (indexA s (1 + n) (indexA x 0 d))
indexA s n (IApptj d x) = IApptj (indexA s n d) (indexT s n x)
indexA s n (ILAMt x d) = ILAMt x (indexA s (1 + n) (indexA x 0 d))
indexA s n (IAppi d d1) = IAppi (indexA s n d) (indexA s n d1)
indexA s n (IIPair d d1) = IIPair (indexA s n d) (indexA s n d1)
indexA s n (IFst d) = IFst (indexA s n d)
indexA s n (ISnd d) = ISnd (indexA s n d)
indexA s n IBeta = IBeta
indexA s n (IRho d x tp d1) = IRho (indexA s n d) x (indexT s (1 + n) (indexT x 0 tp)) (indexA s n d1)

indexT :: String -> Int -> IType -> IType
indexT s n (IVSt x) = if s == x then IVt n else IVSt x
indexT s n (IVt x) = IVt x
indexT s n (IAllk x d d1) = IAllk x (indexK s n d) (indexT s (1 + n) (indexT x 0 d1))
indexT s n (IPit x d d1) = IPit x (indexT s n d) (indexT s (1 + n) (indexT x 0 d1))
indexT s n (ILamt x d d1) = ILamt x (indexT s n d) (indexT s (1 + n) (indexT x 0 d1))
indexT s n (IAppt d x) = IAppt (indexT s n d) (indexA s n x)
indexT s n (IAllt x d d1) = IAllt x (indexT s n d) (indexT s (1 + n) (indexT x 0 d1))
indexT s n (IIota x d d1) = IIota x (indexT s n d) (indexT s (1 + n) (indexT x 0 d1))
indexT s n (IId d x) = IId (indexA s n d) (indexA s n x)

indexK :: String -> Int -> IKind -> IKind
indexK s n IStar = IStar
indexK s n (IPik x d d1) = IPik x (indexT s n d) (indexK s (1 + n) (indexK x 0 d1))

-- Convert intermediate syntax into abstract syntax
fromInterA :: TopCtx -> IADB -> Err ADB
fromInterA g (IVj x) = Ok (AVj x)
fromInterA g (IVSj x) = errLookup x g >>= \case { Left _ -> Bad "Lookup had wron sort." ; Right (a , _) -> Ok a }
fromInterA g (ILamj x d) = fromInterA g d >>= Ok . ALamj
fromInterA g (IAppj d d1) = fromInterA g d >>= \dd -> fromInterA g d1 >>= Ok . AAppj dd
fromInterA g (ILAMj x d) = fromInterA g d >>= Ok . LAMj
fromInterA g (IApptj d x) = fromInterA g d >>= \dd -> fromInterT g x >>= Ok . Apptj dd
fromInterA g (ILAMt x d) = fromInterA g d >>= Ok . LAMt
fromInterA g (IAppi d d1) = fromInterA g d >>= \dd -> fromInterA g d1 >>= Ok . Appi dd
fromInterA g (IIPair d d1) = fromInterA g d >>= \dd -> fromInterA g d1 >>= Ok . IPair dd
fromInterA g (IFst d) = fromInterA g d >>= Ok . Fst
fromInterA g (ISnd d) = fromInterA g d >>= Ok . Snd
fromInterA g IBeta = Ok Beta
fromInterA g (IRho d x tp d1) =
  fromInterA g d >>= \dd -> fromInterT g tp >>= \dtp -> fromInterA g d1 >>= Ok . Rho dd dtp

fromInterT :: TopCtx -> IType -> Err AType
fromInterT g (IVt x) = Ok (AVt x)
fromInterT g (IVSt x) = errLookup x g >>= \case { Left (a , _) -> Ok a ; Right _ -> Bad "Lookup had wrong sort" }
fromInterT g (IAllk x x1 d) = fromInterK g x1 >>= \dx1 -> fromInterT g d >>= Ok . AAllk dx1
fromInterT g (IPit x d d1) = fromInterT g d >>= \dd -> fromInterT g d1 >>= Ok . APit dd
fromInterT g (ILamt x d d1) = fromInterT g d >>= \dd -> fromInterT g d1 >>= Ok . ALamt dd
fromInterT g (IAppt d x) = fromInterT g d >>= \dd -> fromInterA g x >>= Ok . AAppt dd
fromInterT g (IAllt x d d1) = fromInterT g d >>= \dd -> fromInterT g d1 >>= Ok . AAllt dd
fromInterT g (IIota x d d1) = fromInterT g d >>= \dd -> fromInterT g d1 >>= Ok . AIota dd
fromInterT g (IId x y) = fromInterA g x >>= \dx -> fromInterA g y >>= Ok . AId dx

fromInterK :: TopCtx -> IKind -> Err AKind
fromInterK g IStar = Ok AStar
fromInterK g (IPik x x1 d) = fromInterT g x1 >>= \dx1 -> fromInterK g d >>= Ok . APik dx1

{- Convert concrete syntax into intermediate syntax -}
fromConA :: Exp -> Err IADB
fromConA (SLet d e) = Bad "TO DO: Implement let expressions"
fromConA (SLamj (SVar (AIdent e) : []) o) = fromConA o >>= Ok . ILamj e
fromConA (SLamj (SVar (AIdent e) : l) o) = fromConA (SLamj l o) >>= Ok . ILamj e
fromConA (SLami (SVar (AIdent e) : []) o) = fromConA o >>= Ok . ILAMj e
fromConA (SLami (SVar (AIdent e) : l) o) = fromConA (SLami l o) >>= Ok . ILAMj e
fromConA (SLamtj (SVar (AIdent e) : []) o) = fromConA o >>= Ok . ILAMt e
fromConA (SLamtj (SVar (AIdent e) : l) o) = fromConA (SLamtj l o) >>= Ok . ILAMt e
fromConA (SIApp a b) = fromConA a >>= \ca -> fromConA b >>= Ok . IAppi ca
fromConA (STApp a b) = fromConA a >>= \ca -> fromConT b >>= Ok . IApptj ca
fromConA (SApp a b) = fromConA a >>= \ca -> fromConA b >>= Ok . IAppj ca
fromConA (SRho (PTele (SVar (AIdent e)) t) a b) =
  fromConA a >>= \ca -> fromConT t >>= \ct -> fromConA b >>= Ok . IRho ca e ct
fromConA (SFst a) = fromConA a >>= \ca -> Ok $ IFst ca
fromConA (SSnd a) = fromConA a >>= \ca -> Ok $ ISnd ca
fromConA (SPair a b) = fromConA a >>= \ca -> fromConA b >>= Ok . IIPair ca
fromConA SBeta = Ok IBeta
fromConA (SVar (AIdent e)) = Ok $ IVSj e
fromConA _ = Bad "Parsing Error"

fromConT :: Exp -> Err IType
fromConT (SLamt (PTele (SVar (AIdent e)) t : []) o) = fromConT t >>= \ct -> fromConT o >>= Ok . ILamt e ct
fromConT (SLamt (PTele (SVar (AIdent e)) t : l) o) = fromConT t >>= \ct -> fromConT (SLamt l o) >>= Ok . ILamt e ct
fromConT (SApp a b) = fromConT a >>= \ca -> fromConA b >>= Ok . IAppt ca
fromConT (SFun a b) = fromConT a >>= \ca -> fromConT b >>= Ok . IPit "" ca
fromConT (SPi (PTele (SVar (AIdent e)) t : []) o) = fromConT t >>= \ct -> fromConT o >>= Ok . IPit e ct
fromConT (SPi (PTele (SVar (AIdent e)) t : l) o) = fromConT t >>= \ct -> fromConT (SPi l o) >>= Ok . IPit e ct
fromConT (SIPi (ITele (SVar (AIdent e)) t : []) o) = fromConT t >>= \ct -> fromConT o >>= Ok . IAllt e ct
fromConT (SIPi (ITele (SVar (AIdent e)) t : l) o) = fromConT t >>= \ct -> fromConT (SIPi l o) >>= Ok . IAllt e ct
fromConT (SAll (PTele (SVar (AIdent e)) t : []) o) = fromConK t >>= \ct -> fromConT o >>= Ok . IAllk e ct
fromConT (SAll (PTele (SVar (AIdent e)) t : l) o) = fromConK t >>= \ct -> fromConT (SAll l o) >>= Ok . IAllk e ct
fromConT (SId a b) = fromConA a >>= \ca -> fromConA b >>= Ok . IId ca
fromConT (SIota (PTele (SVar (AIdent e)) t) b) = fromConT t >>= \ct -> fromConT b >>= Ok . IIota e ct
fromConT (SVar (AIdent e)) = Ok $ IVSt e
fromConT _ = Bad "Parsing Error"

fromConK :: Exp -> Err IKind
fromConK SU = Ok IStar
fromConK (SFun a b) = fromConT a >>= \ca -> fromConK b >>= Ok . IPik "" ca
fromConK (SPi (PTele (SVar (AIdent e)) t : []) o) = fromConT t >>= \ct -> fromConK o >>= Ok . IPik e ct
fromConK (SPi (PTele (SVar (AIdent e)) t : l) o) = fromConT t >>= \ct -> fromConK (SPi l o) >>= Ok . IPik e ct
fromConK _ = Bad "Parsing Error"

{- Convert Concrete Syntax into Abstract Syntax -}
convertA :: TopCtx -> Exp -> Err ADB
convertA t e = fromConA e >>= fromInterA t . indexA "" 0

convertT :: TopCtx -> Exp -> Err AType
convertT t e = fromConT e >>= fromInterT t . indexT "" 0

convertK :: TopCtx -> Exp -> Err AKind
convertK t e = fromConK e >>= fromInterK t . indexK "" 0

test8 = (STApp (SSnd (SVar (AIdent "n"))) (SVar (AIdent "P")))
test7 = (SApp test8 (SVar (AIdent "s")))
test6 = (SApp test7 (SVar (AIdent "z")))
test5 = (SApp (SIApp (SVar (AIdent "s")) (SFst (SVar (AIdent "n")))) test6)
test4 = (SLamj [SVar (AIdent "s"),SVar (AIdent "z")] test5)
test3 = (SLamtj [SVar (AIdent "p")] test4)
test2 = (SPair (SApp (SVar (AIdent "cS")) (SFst (SVar (AIdent "n")))) test3)
test = (SLamj [SVar (AIdent "n")] test2)
