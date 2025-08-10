\chapter{UTP Designs}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module UTP.Designs (
  tok, tok' 
, i_design, design
, i_h1, i_h2, i_h3, i_h4
, designConjs, designName, designTheory
) where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import Symbols

import Utilities
import LexBase
import Variables
import Types
import AST
import SideCond
import VarData
import Laws
import Proofs
import Substitution
import Theories

import StdTypeSignature
import StdSignature
import Equivalence
import Negation
import Disjunction
import Conjunction
import AndOrInvert
import Implication
import Equality
import ForAll
import Exists
import Closure
import StdTypeSignature
import UTP.Reading
import UTP.Observations
import UTP.Base
import UTP.While.Common -- need seq-comp
import TestRendering

import Debugger
\end{code}


\section{Introduction}

Here we define the UTP concept of Designs,
along with the relevant observables, 
constructors,
healthiness conditions,
and related theorems.

\section{Design Signature}

\subsection{Observables}

We have two Design-specific observables\cite[Defn 3.0.1, p75]{UTP-book}:
$$ 
  ok, ok' : \Bool
$$

\begin{code}
ok = jId "ok"  ;  vok = PreVar ok ; vok' = PostVar ok
tok = jVar bool vok  ;  tok' = jVar bool vok'
\end{code}


\subsection{Constructors}

Given a pre-relation $P$ and post-relation $Q$ 
over an alphabet that does not mention $ok$ or $ok'$,
we define a constructor that produces a health predicate that does include them:
$$ P \design Q $$
\begin{code}
i_design    =  jId "design"
v_design    =  Vbl i_design ObsV Static
designIntro = mkConsIntro i_design boolf_2
\end{code}

\subsection{Healthiness}

We have four healthiness conditions: \H{H1-4}.

\begin{code}
i_h1 = jId "H1" ; vH1 = StaticVar i_h1
i_h2 = jId "H2" ; vH2 = StaticVar i_h2
i_h3 = jId "H3" ; vH3 = StaticVar i_h3
i_h4 = jId "H4" ; vH4 = StaticVar i_h4
\end{code}

We need side-conditions that note that $ok \in O$ and $ok' \in O$:
\begin{code}
designSCs :: VarList -> SideCond
designSCs gPs 
  =  areUTPDynObs gPs .: isUTPCond (StdVar vok) .: isUTPCond' (StdVar vok')
\end{code}


\section{Design Semantics}



\subsection{Design Constructor}

\subsubsection{Design Definition}

\begin{code}
design :: Term -> Term -> Term
design p q  =  Cons arbpred False i_design [p, q]
\end{code}

From: \cite[Defn 3.1.1, p76]{UTP-book}:
$$
  \begin{array}{lll}
     P \design Q ~\defs~ ok \land P \implies ok' \land Q &
     & \QNAME{$\design$-def}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
(axDsgDef,alDsgDef) 
  = bookdef ("design" -.- "def") "defd3.1.1p76"
            (design p q === (tok /\ p ==> tok' /\ q))
            scTrue
\end{code}

\subsubsection{Design Laws}

From: \cite[Thm 3.1.2,p77]{UTP-book}:
$$
[(P_1 \design Q_1) \implies (P_2 \design Q_2)] 
~~\mathbf{iff}~~
[P_2 \implies P_1]
~~\mathbf{and}~~
[(P_2 \land Q_2)\implies Q_2]
$$

P77:
$$
 [(P \design Q) \equiv (P \design P \land Q)]
 ~~\text{and}~~
 [(P \design Q) \equiv (P \design P \implies Q)]
$$

$$
[(P \design Q) \equiv (P \design R)] 
~~\mathbf{iff}~~
[(P \land Q) \implies R]
~~\text{and}~~
[R \implies (P \implies Q)]
$$

From \cite[\textbf{L1},p78]{UTP-book}:
$$
  \begin{array}{lll}
     \true ; (P \design Q) = \true
     && \QNAME{design-$;$-lzero}
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
cjDesignLZero 
  = preddef ("design" -.- "sqcmp" -.- "lzero")
            (mkSeq trueP (design p q) === trueP)
            ( designSCs [gP,gQ] )
\end{code}

\section*{Healthiness}

Code to support UTP Healthiness Conditions.

\begin{code}
applyH :: Identifier -> Term -> Term
applyH hname p  = Cons bool False hname [p]
\end{code}

All up to {\Large\textbf{Healthiness}} should be in a seperate module once everything has settled.


\newpage
\subsection{Healthiness \H{H1}}

\begin{eqnarray*}
   \H{mkH1}(R) &\defs& ok \implies R
\\ P \refines Q &\implies& \H{mkH1}(P) \refines \H{mkH1}(Q)
\\ \H{mkH1}(\H{mkH1}(R)) &=& \H{mkH1}(R)
\\ \H{isH1}(R) &\defs& R = (ok \implies R)
\\ \H{isH1}(R) &\equiv& (\true;R = \true) \land (\Skip;R = R)
\end{eqnarray*}
We need to show that \H{mkH1} is monotonic and idempotent.
\begin{code}
mkH1 r =  tok ==> r
isH1 r =  r `isEqualTo` mkH1 r
mkh1 = jId "mkH1"
h1 = jId "H1"
\end{code}


\subsubsection{\H{H1} Definitions}


$$
\begin{array}{ll}
   \H{H1} & R = (ok \implies R)
\end{array}
$$
\begin{code}
(axMkH1Def,alMkH1Def) 
  = bookdef ("mkH1" -.- "def") "defd3.2.1_1p82"
            (applyH mkh1 r  === mkH1 r)
            scTrue
\end{code}

\begin{code}
(axH1Def,alH1Def) 
  = bookdef ("H1" -.- "def") "defd3.2.1_1p82"
            (applyH h1 r  === r `isEqualTo` mkH1 r)
            scTrue
\end{code}


\subsubsection{\H{H1} Laws}

\begin{eqnarray*}
   P \refines Q &\implies& \H{mkH1}(P) \refines \H{mkH1}(Q)
\\ \H{mkH1}(\H{mkH1}(R)) &=& \H{mkH1}(R)
\end{eqnarray*}
\begin{code}
cjMkH1Monotonic 
  = preddef ("mkH1" -.- "mono")
            ( (p `refines` q) ==> ( mkH1 p `refines` mkH1 q ) ) 
            ( scTrue )

cjMkH1Idempotent 
  = preddef ("mkH1" -.- "idem")
            ( mkH1 (mkH1 r) `isEqualTo` mkH1 r ) 
            ( scTrue )
\end{code}


From \cite[\textbf{Thm 3.2.2},p83]{UTP-book}:
A predicate is \H{H1} ~~\IFF~~ it satisfies left-zero and left-unit
$$
\H{isH1}(R) \equiv (\true;R = \true) \land (\Skip;R = R)
$$
\begin{code}
cjH1satLZeroRUnit 
  = preddef ("H1" -.- "sat" -.- "lzero"-.-"lunit")
            ( applyH h1 r 
              === 
              ( (mkSeq trueP r `isEqualTo` trueP) 
              /\ 
              (mkSeq skip r `isEqualTo` r) ) 
            )
            ( designSCs [gR] )
\end{code}



\subsection{Healthiness \H{H2}}


\begin{eqnarray*}
   \H{isH2}(R) &\defs& [R[false/ok']\implies R[true/ok']]
\end{eqnarray*}
\begin{code}
setOk' r b =  Sub bool r $ jSubstn [(vok',Val bool b)] []
isH2 r =  setOk' r (Boolean False) `refines` setOk' r (Boolean True)
h2 = jId "H2"
\end{code}



\subsubsection{\H{H2} Definition}

$$
\begin{array}{ll}
   \H{H2} & [R[false/ok']\implies R[true/ok']]
\end{array}
$$
\begin{code}
(axH2Def,alH2Def) 
  = bookdef ("H2" -.- "def") "defd3.2.1_2p82"
            ( applyH h2 r === isH2 r )
            scTrue
\end{code}


\subsubsection{\H{H2} Laws}

From \cite[\textbf{Thm 3.2.3},p83]{UTP-book}:
A predicate is \H{H1} and \H{H2}~~\IFF~~ it is a design.
$$
\H{H1} \land \H{H2} \equiv \text{isDesign}
$$


\subsection{Healthiness \H{H3}}

\begin{eqnarray*}
   \H{isH3}(R) &\defs& R = R ; \Skip
\\ \H{isH3}(P \design Q) &\equiv& \fv(P)\subseteq O
\\ \H{mkH3}(R) &\defs& R ; \Skip
\end{eqnarray*}
We need to show that \H{mkH3} is monotonic and idempotent.
\begin{code}
isH3 r =  mkSeq r skip
h3 = jId "H3"
\end{code}

\subsubsection{\H{H3} Definition}

$$
\begin{array}{ll}
   \H{H3} & R = R ; \Skip
\end{array}
$$
\begin{code}
(axH3Def,alH3Def) 
  = bookdef ("H3" -.- "def") "defd3.2.1_3p82"
            ( applyH h3 r === isH3 r )
            scTrue
\end{code}

\subsubsection{\H{H3} Laws}

From \cite[\textbf{Thm 3.2.4},p84]{UTP-book}:
A design is \H{H3} if its assumption $P$ can be expressed as a condition $p$.
$$
(p\design Q) = (p\design Q);\Skip
$$
Being \H{H3} allows us to simplify Thm 3.1.4(3) to
$$
(p_1\design Q_1);(p_2 \design Q)
         =
         ( p_1 \land \lnot(Q_1;\lnot p_2)
           \design 
           Q_1 ;Q_2 )
$$


\subsection{Healthiness \H{H4}}

\begin{eqnarray*}
   \H{isH4}(R) &\defs& R ; \true = \true
\\ \H{isH4}(R) &\defs& [\exists O' \bullet R]
\end{eqnarray*}
\begin{code}
isH4 r =  mkSeq r trueP
h4 = jId "H4"
\end{code}


\subsubsection{\H{H4} Definition}

$$
\begin{array}{ll}
   \H{H4} & R ; \true = true
\end{array}
$$
\begin{code}
(axH4Def,alH4Def) 
  = bookdef ("H4" -.- "def") "defd3.2.1_4p82"
            ( applyH h4 r === isH4 r )
            scTrue
\end{code}


\subsubsection{\H{H4} Laws}

From \cite[\textbf{Thm 3.2.5},p85]{UTP-book}:

$P\design Q$ satisfies \H{H4} ~~\IFF~~ $[\exists ok',x',\dots,z'\bullet (P\design  Q)]$.




\section{Designs Theory}

Known:
\begin{code}
designKnown :: VarTable
designKnown =  mkKnownVar vok bool $
               mkKnownVar vok' bool $
               mkKnownVar v_design boolf_2 $
               mkKnownVar vH1 boolf_1 $
               mkKnownVar vH2 boolf_1 $
               mkKnownVar vH3 boolf_1 $
               mkKnownVar vH4 boolf_1 $
               newNamedVarTable designName
\end{code}

Axioms:
\begin{code}
designAxioms :: [Law]
designAxioms  
  =  map labelAsAxiom [ axDsgDef 
                      , axMkH1Def, axH1Def
                      , axH2Def
                      , axH3Def
                      , axH4Def ]
\end{code}

Conjectures:
\begin{code}
designConjs :: [NmdAssertion]
designConjs
  = [ cjDesignLZero
    , cjH1satLZeroRUnit
    , cjMkH1Idempotent, cjMkH1Monotonic
    ]
\end{code}


\begin{code}
designName :: String
designName = "Designs"
designTheory :: Theory
designTheory
  = nullTheory  { thName  =  designName
                , thDeps  = [ utpWC_Name
                            , utpBase_Name
                            , aoiName
                            , conjName
                            , disjName
                            , notName
                            , equivName ]
                , known   =  designKnown
                , laws    =  designAxioms
                , conjs   =  designConjs
                }
\end{code}

\section{Designs Infrastructure}


\begin{code}
vP = Vbl (jId "P") PredV Static ; p = fromJust $ pVar ArbType vP ; gP = StdVar vP
vQ = Vbl (jId "Q") PredV Static ; q = fromJust $ pVar ArbType vQ ; gQ = StdVar vQ
vR = Vbl (jId "R") PredV Static ; r = fromJust $ pVar ArbType vR ; gR = StdVar vR
\end{code}
