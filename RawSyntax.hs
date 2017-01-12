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

{- Intermediate raw instax -}
data ITerm
   = IVS String
   | IV Int
   | ILam String ITerm
   | IAnn ITerm ITerm
   | IApp ITerm ITerm
   | ILAM String ITerm
   | IAppi ITerm ITerm
   | IIPair ITerm ITerm
   | IFst ITerm
   | ISnd ITerm
   | IBeta
   | IRho ITerm String ITerm ITerm
   | IPit String ITerm ITerm
   | IIPi String ITerm ITerm
   | IIota String ITerm ITerm
   | IId ITerm ITerm
   | IStar
   deriving (Show)

{- Convert intermediate syntax into abstract syntax -}

-- Replace string variables with deBruijin indices
index :: String -> Int -> ITerm -> ITerm
index s n (IVS x) = if s == x then IV n else IVS x
index s n (IV x) = IV x
index s n (ILam x d) = ILam x (index s (1 + n) (index x 0 d))
index s n (IAnn d d1) = IAnn (index s n d) (index s n d1)
index s n (IApp d d1) = IApp (index s n d) (index s n d1)
index s n (ILAM x d) = ILAM x (index s (1 + n) (index x 0 d))
index s n (IAppi d d1) = IAppi (index s n d) (index s n d1)
index s n (IIPair d d1) = IIPair (index s n d) (index s n d1)
index s n (IFst d) = IFst (index s n d)
index s n (ISnd d) = ISnd (index s n d)
index s n IBeta = IBeta
index s n (IRho d x tp d1) = IRho (index s n d) x (index s (1 + n) (index x 0 tp)) (index s n d1)
index s n (IPit x d d1) = IPit x (index s n d) (index s (1 + n) (index x 0 d1))
index s n (IIPi x d d1) = IIPi x (index s n d) (index s (1 + n) (index x 0 d1))
index s n (IIota x d d1) = IIota x (index s n d) (index s (1 + n) (index x 0 d1))
index s n (IId d x) = IId (index s n d) (index s n x)
index s n IStar = IStar

-- Convert intermediate syntax into abstract syntax
fromInter :: TopCtx -> ITerm -> Err ATerm
fromInter g (IV x) = Ok $ AV x
fromInter g (IVS x) = Ok $ AVS x
fromInter g (ILam x d) = fromInter g d >>= Ok . ALam
fromInter g (IApp d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . AApp dd
fromInter g (IAnn d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . AAnn dd
fromInter g (ILAM x d) = fromInter g d >>= Ok . ALAM
fromInter g (IAppi d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . AAppi dd
fromInter g (IIPair d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . AIPair dd
fromInter g (IFst d) = fromInter g d >>= Ok . AFst
fromInter g (ISnd d) = fromInter g d >>= Ok . ASnd
fromInter g IBeta = Ok ABeta
fromInter g (IRho d x tp d1) =
  fromInter g d >>= \dd -> fromInter g tp >>= \dtp -> fromInter g d1 >>= Ok . ARho dd dtp
fromInter g (IPit x d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . APi dd
fromInter g (IIPi x d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . AIPi dd
fromInter g (IIota x d d1) = fromInter g d >>= \dd -> fromInter g d1 >>= Ok . AIota dd
fromInter g (IId x y) = fromInter g x >>= \dx -> fromInter g y >>= Ok . AId dx
fromInter g IStar = Ok AStar

{- Convert concrete syntax into intermediate syntax -}
fromCon :: Exp -> Err ITerm
fromCon (SLet d e) = Bad "TO DO: Implement let expressions"
fromCon (SLam (AOTele (AIdent e) : []) o) = fromCon o >>= Ok . ILam e
fromCon (SLam (AOTele (AIdent e) : l) o) = fromCon (SLam l o) >>= Ok . ILam e
fromCon (SLam (POTele (PTele (SVar (AIdent e)) t) : []) o) =
  fromCon t >>= \ct -> fromCon o >>= Ok . ILam e . IAnn ct
fromCon (SLam (POTele (PTele (SVar (AIdent e)) t) : l) o) =
  fromCon t >>= \ct -> fromCon (SLam l o) >>= Ok . ILam e . IAnn ct
fromCon (SLami (AIdent e : []) o) = fromCon o >>= Ok . ILAM e
fromCon (SLami (AIdent e : l) o) = fromCon (SLami l o) >>= Ok . ILAM e
fromCon (SAppi a b) = fromCon a >>= \ca -> fromCon b >>= Ok . IAppi ca
fromCon (SApp a b) = fromCon a >>= \ca -> fromCon b >>= Ok . IApp ca
fromCon (SRho (PTele (SVar (AIdent e)) t) a b) =
  fromCon a >>= \ca -> fromCon t >>= \ct -> fromCon b >>= Ok . IRho ca e ct
fromCon (SFst a) = fromCon a >>= \ca -> Ok $ IFst ca
fromCon (SSnd a) = fromCon a >>= \ca -> Ok $ ISnd ca
fromCon (SPair a b) = fromCon a >>= \ca -> fromCon b >>= Ok . IIPair ca
fromCon SBeta = Ok IBeta
fromCon (SVar (AIdent e)) = Ok $ IVS e
fromCon (SFun a b) = fromCon a >>= \ca -> fromCon b >>= Ok . IPit "" ca
fromCon (SPi (PTele (SVar (AIdent e)) t : []) o) = fromCon t >>= \ct -> fromCon o >>= Ok . IPit e ct
fromCon (SPi (PTele (SVar (AIdent e)) t : l) o) = fromCon t >>= \ct -> fromCon (SPi l o) >>= Ok . IPit e ct
fromCon (SIPi (ITele (SVar (AIdent e)) t : []) o) = fromCon t >>= \ct -> fromCon o >>= Ok . IIPi e ct
fromCon (SIPi (ITele (SVar (AIdent e)) t : l) o) = fromCon t >>= \ct -> fromCon (SIPi l o) >>= Ok . IIPi e ct
fromCon (SId a b) = fromCon a >>= \ca -> fromCon b >>= Ok . IId ca
fromCon (SIota (PTele (SVar (AIdent e)) t) b) = fromCon t >>= \ct -> fromCon b >>= Ok . IIota e ct
fromCon SU = Ok IStar
fromCon _ = Bad "Parsing Error"

{- Convert Concrete Syntax into Abstract Syntax -}
convert :: TopCtx -> Exp -> Err ATerm
convert t e = fromCon e >>= fromInter t . index "" 0
