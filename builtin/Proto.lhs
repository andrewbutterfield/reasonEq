\section{Prototype}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Proto (
  protoName
, protoTheory
) where

import Data.Maybe 
import qualified Data.Map as M
import qualified Data.Set as S

import Symbols

import YesBut
import Utilities
import LexBase
import Variables
import Types
import AST
import SideCond
import VarData
import Substitution
import Assertions
import Laws
import Proofs
import Theories

import StdTypeSignature
import StdSignature
import TestRendering

import Debugger
\end{code}

\subsection{Introduction}

This is an isolated theory for prototyping stuff

\subsubsection{Known Variables}

\begin{code}
--variables
atermIntro  =  mkConsIntro (jId "aterm") bool
atermfIntro =  mkConsIntro (jId "atermf") boolf_1
var'AIntro = mkKnownVar (Vbl (jId "a") ObsV Before) (GivenType $ jId "N")
varA'Intro = mkKnownVar (Vbl (jId "a") ObsV After) (GivenType $ jId "N")
molIntro = mkKnownConst (Vbl (jId "mol") ExprV Static) (Val int $ Integer 42)
prodIntro =  mkConsIntro (jId "prodt") 
                          (TypeCons (jId "Prod") [(GivenType $ jId "A"),bool])
sumIntro = mkConsIntro (jId "sumt")
  ( AlgType (jId "Sum")
      [ ((jId "Sum1"),[])
      , ((jId "Sum2"),[(GivenType $ jId "B")])
      , ((jId "Sum3"),[boolf_1,(GivenType $ jId "A"),bool])
      ] 
  )
genvar = Vbl (jId "gen") ExprV Static
genVarIntro = fromJust . addGenericVar genvar
instvar = Vbl (jId "inst") ExprV Static
instVarIntro = fromJust . addInstanceVar instvar genvar

--static list variables
klLVar0 = LVbl (Vbl (jId "klist0") ObsV Static) [] []
klist0Intro = fromJust . addKnownLListVar klLVar0 []

klLVar1 = LVbl (Vbl (jId "klist1") ObsV Static) [] []
klist1Intro = fromJust . addKnownLListVar klLVar1 
                   [StdVar $ Vbl (jId "x") ObsV Static]
klLVar2 = LVbl (Vbl (jId "klist2") ObsV Static) [] []
klist2Intro = fromJust . addKnownLListVar klLVar2 
                   [StdVar $ Vbl (jId "x") ObsV Static
                   ,StdVar $ Vbl (jId "y") ObsV Static]

ksLVar = LVbl (Vbl (jId "set") ObsV Static) [] []
ksetIntro = fromJust . addKnownSListVar ksLVar S.empty
kabsSetIntro = mkAbsSetVar (Vbl (jId "aset") ObsV Static)
kabsListIntro = mkAbsListVar (Vbl (jId "alist") ObsV Static)

xIntro = mkConsIntro (jId "x") bool
yIntro = mkConsIntro (jId "y") bool


--dynamic list variables

dlLVar = LVbl (Vbl (jId "list") ObsV Before) [] []
dlistIntro = fromJust . addKnownLListVar dlLVar []
dsLVar = LVbl (Vbl (jId "set") ObsV After) [] []
dsetIntro = fromJust . addKnownSListVar dsLVar S.empty
dabsSetIntro = mkAbsSetVar (Vbl (jId "aset") ObsV Before)
dabsListIntro = mkAbsListVar (Vbl (jId "alist") ObsV After)
\end{code}

\begin{code}
protoKnown :: VarTable
protoKnown 
  = atermIntro $
    atermfIntro $
    var'AIntro $
    varA'Intro $
    molIntro $
    prodIntro $
    sumIntro $
    instVarIntro $
    genVarIntro $ 

    ksetIntro $
    klist2Intro $
    klist0Intro $
    klist1Intro $
    xIntro $ yIntro $
    kabsListIntro $
    kabsSetIntro $
 
    dlistIntro $
    dsetIntro $
    dabsListIntro $
    dabsSetIntro $
    newNamedVarTable protoName
\end{code}

\newpage

\subsubsection{Axioms}


We now collect all of the above as our axiom set:
\begin{code}
protoAxioms :: [Law]
protoAxioms
  = map (labelAsAxiom . mkNmdAsn)
      [ 
      ]
\end{code}

\subsection{Conjectures}

\begin{code}
tmConj name term = ( name, ( term, scTrue ))

-- Values

tmTrue = tmConj "true" (Val arbpred (Boolean True))
tmFalse = tmConj "false" (Val arbpred (Boolean False))

fortytwo = Val arbpred (Integer 42)
tmNumPos = tmConj "fortytwo" fortytwo
tmNumNeg = tmConj "neg99" (Val arbpred (Integer (-99)))

-- Variables 

mkV nm vc vw = jVar arbpred $ Vbl (jId nm) vc vw

tmVarOS = tmConj ("obs"-.-"static") (mkV "Vo" ObsV Static)
tmVar'OS = tmConj ("obs"-.-"before") (mkV "Vo" ObsV Before)
tmVarOS' = tmConj ("obs"-.-"after") (mkV "Vo" ObsV After)
tmVarOS'd = tmConj ("obs"-.-"during") (mkV "Vo" ObsV (During "d"))

tmVarES = tmConj ("expr"-.-"static") (mkV "Ve" ExprV Static)
tmVar'ES = tmConj ("expr"-.-"before") (mkV "Ve" ExprV Before)
tmVarES' = tmConj ("expr"-.-"after") (mkV "Ve" ExprV After)
tmVarES'd = tmConj ("expr"-.-"during") (mkV "Ve" ExprV (During "d"))

tmVarPS = tmConj ("pred"-.-"static") (mkV "Vp" PredV Static)
tmVar'PS = tmConj ("pred"-.-"before") (mkV "Vp" PredV Before)
tmVarPS' = tmConj ("pred"-.-"after") (mkV "Vp" PredV After)
tmVarPS'd = tmConj ("pred"-.-"during") (mkV "Vp" PredV (During "d"))

-- Constructions

cs = True ; ns = False -- Subable
vT = mkV "T" PredV Static
mkCons nm subable ts = Cons arbpred subable (jId nm) ts



tmConsS0 = tmConj ("cons"-.-"S"-.-"zero") (mkCons "cs0" cs [])
tmConsS1 = tmConj ("cons"-.-"S"-.-"one")  (mkCons "cs1" cs [vT])
tmConsS2 = tmConj ("cons"-.-"S"-.-"two")  (mkCons "cs2" cs [vT,vT])

tmConsN0 = tmConj ("cons"-.-"N"-.-"zero") (mkCons "ns0" ns [])
tmConsN1 = tmConj ("cons"-.-"N"-.-"one")  (mkCons "ns1" ns [vT])
consN2 = mkCons "ns2" ns [vT,vT]
tmConsN2 = tmConj ("cons"-.-"N"-.-"two")  consN2

tmConsNest = tmConj ("cons"-.-"nesting")
              (mkCons "nest" cs [ mkCons "sub1" cs []
                                , mkCons "sub2" cs [vT] 
                                , mkCons "sub3" cs [] 
                                ])

-- Quantifiers

mkVs nm vc vw = (v,gv,lv,glv)
 where v  = Vbl (jId nm) vc vw ; gv = StdVar v
       lv = LVbl v [] [] ; glv = LstVar lv

(va,gva,lva,glva) = mkVs "a" ObsV Before
(va',gva',lva',glva') = mkVs "a" ObsV After


mkBody = mkV "body" PredV Static
mkQ str vl body = jBnd ArbType (jId str) (S.fromList vl) body

tmForall0 = tmConj ("forall"-.-"zero")
            (mkQ "forall" [] mkBody)
exists1 = mkQ "exists" [gva] (mkCons "csQ" cs [vT,vT])
tmExists1 = tmConj ("exists"-.-"one") exists1
forall2 = mkQ "forall" [gva,gva'] mkBody
tmForall2 = tmConj ("forall"-.-"two") forall2
tmExists3 = tmConj ("exists"-.-"three")
            (mkQ "exists" [gva,gva',glva] mkBody)
tmForall4 = tmConj ("forall"-.-"four")
            (mkQ "forall" [gva,gva',glva,glva'] mkBody)

mkL str vl body = jLam ArbType (jId str) vl body

tmLambda0 = tmConj ("lambda"-.-"zero")
            (mkL "lambda" [] mkBody)
tmLambda1 = tmConj ("lambda"-.-"one")
            (mkL "lambda" [gva] (mkCons "csQ" cs [vT,vT]))
tmLambda2 = tmConj ("lambda"-.-"two")
            (mkL "lambda" [gva,gva'] mkBody)
tmLambda3 = tmConj ("lambda"-.-"three")
            (mkL "lambda" [gva,gva',glva] mkBody)
tmLambda4 = tmConj ("lambda"-.-"four")
            (mkL "lambda" [gva,gva',glva,glva'] mkBody)

-- Closures

universe = "universal"
existence = "existential"

tmUniversal1 = tmConj ("univ"-.-"closure") (Cls (jId universe) mkBody)
tmUniversal2 = tmConj ("univ"-.-"closure") (Cls (jId universe) forall2)
tmExistential1 = tmConj ("exist"-.-"closure") (Cls (jId existence) mkBody)
tmExistential2 = tmConj ("exist"-.-"closure") (Cls (jId existence) exists1)

-- Substitution

simpleSub term vs lvlvs =  Sub ArbType term $ jSubstn (zip vs (repeat mkBody)) lvlvs

mkS term vts lvlvs = Sub (termtype term) term $ jSubstn vts lvlvs

(va'd,gva'd,lva'd,glva'd) = mkVs "a" ObsV (During "d")
(vb,gvb,lvb,glvb) = mkVs "b" ObsV Before
(vb',gvb',lvb',glvb') = mkVs "b" ObsV After
(vb'd,gvb'd,lvb'd,glvb'd) = mkVs "b" ObsV (During "d")


tmSub00 = tmConj ("sub"-.-"none"-.-"none") (simpleSub mkBody [] [])
tmSub10 = tmConj ("sub"-.-"one"-.-"none") (simpleSub mkBody [va] [])
tmSub01 = tmConj ("sub"-.-"none"-.-"one") (simpleSub mkBody [] [(lva',lva'd)])
tmSub11 = tmConj ("sub"-.-"one"-.-"none") (simpleSub mkBody [va] [(lva',lva'd)])
tmSub22 = tmConj ("sub"-.-"two"-.-"two") 
     (mkS mkBody [(va,fortytwo),(vb,consN2)] [(lva',lva'd),(lvb,lvb')])

-- Assignment

p1 = arbpred
i_asg        =  assignmentId
p_asg        =  jVar p1 $ Vbl i_asg PredV Textual

simassign :: [(Variable,Term)] -> [(ListVar,ListVar)] -> Term
simassign vts lvlvs  =  Sub p1 p_asg $ xSubstn vts lvlvs

vv = Vbl (jId "v") ObsV Before
ve = jVar int $ Vbl (jId "e") ExprV Before
tmVbecomesE = tmConj ("v"-.-"becomes"-.-"e")
                  (mkS p_asg [(vv,ve)] [])

-- Side Conditions

mkSC :: String -> SideCond -> (String,(Term,SideCond))
mkSC name sc = ( "sc"-.-name, ( mkBody, sc ))

mkvsc name vsc = mkSC name ([vsc],S.empty)

vP = Vbl (jId "P") PredV Static ; gvP = StdVar vP
just_a = S.singleton gva

tmSCtrue = mkSC "true" scTrue
tmSCfree1 = mkSC ("free"-.-"a") ([],S.singleton gva)
tmSCvarDisj = mkvsc ("P"-.-"disj"-.-"a") (gvP `disjfrom` just_a)
tmSCvarCov = mkvsc ("P"-.-"cov"-.-"a") (gvP `coveredby` just_a)
tmSCvarDCov = mkvsc ("P"-.-"dyncov"-.-"a") (gvP `dyncovered` just_a)
tmSCmixed = mkSC ("mixed") ([gvP `disjfrom` just_a],S.singleton gva)
\end{code}


gv `disjfrom`   vs  =  VSC gv (The vs) covByNA  covByNA
gv `coveredby`  vs  =  VSC gv disjNA   (The vs) covByNA
gv `dyncovered` vs  =  VSC gv disjNA   cov


Collected\dots
\begin{code}
protoConjs :: [NmdAssertion]
protoConjs = map mkNmdAsn 
  [ tmTrue, tmFalse
  , tmSCtrue
  , tmSCfree1
  , tmSCvarDisj, tmSCvarCov, tmSCvarDCov
  , tmSCmixed
  , tmVbecomesE
  , tmUniversal1, tmExistential1, tmUniversal2, tmExistential2
  , tmSub00, tmSub10, tmSub01, tmSub11, tmSub22
  , tmForall0, tmExists1, tmForall2, tmExists3, tmForall4
  , tmLambda0, tmLambda1, tmLambda2, tmLambda3, tmLambda4
  , tmNumPos, tmNumNeg 
  , tmVarES, tmVar'ES, tmVarES', tmVarES'd
  , tmVarPS, tmVar'PS, tmVarPS', tmVarPS'd
  , tmConsS0, tmConsS1, tmConsS2
  , tmConsN0, tmConsN2, tmConsN2, tmConsNest
  ]
\end{code}

\subsection{The Prototype Theory}

\begin{code}
protoName :: String
protoName = "Proto"
protoTheory :: Theory
protoTheory
  =  nullTheory { thName  =  protoName
                , known   =  protoKnown
                , laws    =  protoAxioms
                , conjs   =  protoConjs
                }
\end{code}
