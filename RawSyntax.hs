module RawSyntax where

import AbstractSyntax
import PrettyPrinting

-- Representation for printing
import Exp.Abs

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
fromInter :: ITerm -> Proof ATerm
fromInter (IV x) = return $ AV x
fromInter (IVS x) = return $ AVS x
fromInter (ILam x d) = ALam <$> fromInter d
fromInter (IApp d d1) = AApp <$> fromInter d <*> fromInter d1
fromInter (IAnn d d1) = AAnn <$> fromInter d <*> fromInter d1
fromInter (ILAM x d) = ALAM <$> fromInter d
fromInter (IAppi d d1) = AAppi <$> fromInter d <*> fromInter d1
fromInter (IIPair d d1) = AIPair <$> fromInter d <*> fromInter d1
fromInter (IFst d) = AFst <$> fromInter d
fromInter (ISnd d) = ASnd <$> fromInter d
fromInter IBeta = return ABeta
fromInter (IRho d x tp d1) = ARho <$> fromInter d <*> fromInter tp <*> fromInter d1
fromInter (IPit x d d1) = APi <$> fromInter d <*> fromInter d1
fromInter (IIPi x d d1) = AIPi <$> fromInter d <*> fromInter d1
fromInter (IIota x d d1) = AIota <$> fromInter d <*> fromInter d1
fromInter (IId x y) = AId <$> fromInter x <*> fromInter y
fromInter IStar = return AStar

{- Convert concrete syntax into intermediate syntax -}
fromCon :: Exp -> Proof ITerm
fromCon (SLet d e) = proofError "TO DO: Implement let expressions"
fromCon (SLam [AOTele (AIdent e)] o) = ILam e <$> fromCon o
fromCon (SLam (AOTele (AIdent e) : l) o) = ILam e <$> fromCon (SLam l o)
fromCon (SLam [POTele (PTele (SVar (AIdent e)) t)] o)
  = ILam e <$> (IAnn <$> fromCon t <*> fromCon o)
fromCon (SLam (POTele (PTele (SVar (AIdent e)) t) : l) o)
  = ILam e <$> (IAnn <$> fromCon t <*> fromCon (SLam l o))
fromCon (SLami [AIdent e] o) = ILAM e <$> fromCon o
fromCon (SLami (AIdent e : l) o) = ILAM e <$> fromCon (SLami l o)
fromCon (SAppi a b) = IAppi <$> fromCon a <*> fromCon b
fromCon (SApp a b) = IApp <$> fromCon a <*> fromCon b
fromCon (SRho (SVar (AIdent e)) t a b) =  IRho <$> fromCon a <*> return e <*> fromCon t <*> fromCon b
fromCon (SFst a) = IFst <$> fromCon a
fromCon (SSnd a) = ISnd <$> fromCon a
fromCon (SPair a b) = IIPair <$> fromCon a <*> fromCon b
fromCon SBeta = return IBeta
fromCon (SVar (AIdent e)) = return $ IVS e
fromCon (SFun a b) = IPit "" <$> fromCon a <*> fromCon b
fromCon (SPi [PTele (SVar (AIdent e)) t] o) = IPit e <$> fromCon t <*> fromCon o
fromCon (SPi (PTele (SVar (AIdent e)) t : l) o) = IPit e <$> fromCon t <*> fromCon (SPi l o)
fromCon (SIPi [ITele (SVar (AIdent e)) t] o) = IIPi e <$> fromCon t <*> fromCon o
fromCon (SIPi (ITele (SVar (AIdent e)) t : l) o) = IIPi e <$> fromCon t <*> fromCon (SIPi l o)
fromCon (SId a b) = IId <$> fromCon a <*> fromCon b
fromCon (SIota (PTele (SVar (AIdent e)) t) b) = IIota e <$> fromCon t <*> fromCon b
fromCon SU = return IStar
fromCon _ = proofError "Parsing Error"

{- Convert Concrete Syntax into Abstract Syntax -}
convert :: Exp -> Proof ATerm
convert e = fromCon e >>= fromInter . index "" 0
