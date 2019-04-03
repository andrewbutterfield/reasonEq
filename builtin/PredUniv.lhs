\section{Universal Closure}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2019

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module PredUniv (
  predUnivConjs, predUnivName, predUnivTheory
) where

import Data.Maybe
import qualified Data.Set as S

import NiceSymbols

import Utilities
import LexBase
import Variables
import AST
import SideCond
import VarData
import Laws
import Proofs
import Theories

import PropAxioms
import PropSubst
import PropEquiv
import PropNot
import PropDisj
import PropConj
import PropMixOne
import PropImpl
import Equality
import PredAxioms
\end{code}


\newpage
\subsection{Introduction}


Here we present a hard-coded implementation of
predicate equational reasoning, as inspired by Gries \& Schneider\cite{gries.93},
Tourlakis \cite{journals/logcom/Tourlakis01}
and described in \cite{DBLP:conf/utp/Butterfield12}.
However we adopt here a formulation closer to that of Gries\&Schneider,
as the Tourlakis form has useful laws such as the one-point rules
derived from his axioms by meta-proofs
\emph{that use non-equational reasoning}.
$$
\AXUNIVCLOSE
$$
$$
\CJUNIVCLOSE
$$


\subsection{Predicate Infrastructure}

We need to build some infrastructure here.
This consists of the predicate variables $P$, $Q$ and $R$,
expression variable $e$,
the constants $\forall$, $\exists$, $[]$,
and a useful collection of generic binder variables: $x,y,\lst x,\lst y$.

\subsubsection{Predicate and Expression Variables}

\begin{code}
vP = Vbl (fromJust $ ident "P") PredV Static
gvP = StdVar vP
p = fromJust $ pVar vP
q = fromJust $ pVar $ Vbl (fromJust $ ident "Q") PredV Static
-- r = fromJust $ pVar $ Vbl (fromJust $ ident "R") PredV Static
-- ve = Vbl (fromJust $ ident "e") ExprV Static
-- lves = LVbl ve [] []
-- gves = LstVar lves
-- e = fromJust $ eVar ArbType ve
\end{code}

\subsubsection{Generic Variables}

\begin{code}
vx = Vbl (fromJust $ ident "x") ObsV Static ; x = StdVar vx
--tx = fromJust $ eVar ArbType vx
lvxs = LVbl vx [] [] ; xs = LstVar lvxs
-- vy = Vbl (fromJust $ ident "y") ObsV Static ; y = StdVar vy
-- lvys = LVbl vy [] [] ; ys = LstVar lvys
\end{code}

\newpage
\subsection{Universal Axioms}

% \begin{array}{lll}
%    \AXUnivDef & \AXUnivDefS & \AXUnivDefN
% \\ \AXPEqDef  & \AXPEqDefS  & \AXPEqDefN
% \end{array}

$$
  \begin{array}{lll}
     \AXUnivDef & \AXUnivDefS & \AXUnivDefN
  \end{array}
$$\par\vspace{-8pt}
\begin{code}
axUnivDef = preddef ("[]" -.- "def")
                    (univ p === forall [xs] p)
                    ([xs] `covers` gvP)
\end{code}


\newpage
\subsection{Universal Conjectures}

% \begin{array}{lll}
%    \CJUnivIdem & \CJUnivIdemS & \CJUnivIdemN
% \\ \CJandUnivDistr & \CJandUnivDistrS & \CJandUnivDistrN
% \\ \CJtrueUniv & \CJtrueUnivS & \CJtrueUnivN
% \\ \CJfalseUniv & \CJfalseUnivS & \CJfalseUnivN
% \\ \CJallUnivClosed & \CJallUnivClosedS & \CJallUnivClosedN
% \\ \CJanyUnivClosed & \CJanyUnivClosedS & \CJanyUnivClosedN
% \end{array}


% %% TEMPLATE
% $$
%   \begin{array}{lll}
%      law & sc & name
%   \end{array}
% $$\par\vspace{-8pt}
% \begin{code}
% axXXX = preddef ("law" -.- "name")
%   p
%   scTrue
% \end{code}

We now collect all of the above as our axiom set:
\begin{code}
predUnivAxioms :: [Law]
predUnivAxioms
  = map labelAsAxiom
      [ axUnivDef ]
\end{code}


We now collect all of the above as our conjecture set:
\begin{code}
predUnivConjs :: [NmdAssertion]
predUnivConjs
  = [ ]
\end{code}


\subsection{The Predicate Theory}

\begin{code}
predUnivName :: String
predUnivName = "PredUniv"
predUnivTheory :: Theory
predUnivTheory
  =  Theory { thName  =  predUnivName
            , thDeps  =  [ predAxiomName
                         , equalityName
                         , propSubstName
                         , propImplName
                         , propMixOneName
                         , propConjName
                         , propDisjName
                         , propNotName
                         , propEquivName
                         , propAxiomName
                         ]
            , known   =  newVarTable
            , laws    =  predUnivAxioms
            , proofs  =  []
            , conjs   =  predUnivConjs
            }
\end{code}
