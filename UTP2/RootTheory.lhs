\section{Root Theory}

\begin{code}
module RootTheory where
import Tables
import Datatypes
import DataText
import Heuristics
import Laws
import Proof
import Theories
import DSL
import Data.List

import Text.ParserCombinators.Parsec.Expr
\end{code}

Here we define the ``root theory'' that is always
present, which gives the syntax data for the logic,
(precedences, associativity, etc)
and the axioms. The axioms are inspired by
the work of Gries\&Schneider \cite{gries.93},
and adapted from the work of Tourlakis \cite{journals/logcom/Tourlakis01}.
We also define some conjectures to proven as theorems
from these axioms. Here we do not follow the pattern of \cite{gries.93},
but instead a more classical view, with an emphasis on dual properties,
distributions and properties of implication.

\subsection{Useful definitions}

\begin{code}
rootProvenance = FromSOURCE "ROOT"
mkRootLaw = mklaw rootProvenance
freeRootLaw = freelaw rootProvenance
\end{code}


\subsection{Propositional Axioms}

The propositional axioms are:
$$
\AXPROP
$$
We now treat each of these individually.

\newpage
\subsubsection{Axiom \AXeqvAssocN}
$$\AXeqvAssoc$$
\begin{code}
pred_Ax_eqvAssoc  =  ((pP === pQ) === pR)
                     ===
                     (pP === (pQ === pR))
law_Ax_eqvAssoc = freeRootLaw "Ax-==-assoc" pred_Ax_eqvAssoc
\end{code}

\subsubsection{Axiom \AXeqvSymmN}
$$\AXeqvSymm$$
\begin{code}
pred_Ax_eqvSymm  =  (pP === pQ) === (pQ === pP)
law_Ax_eqvSymm = freeRootLaw "Ax-==-symm" pred_Ax_eqvSymm
\end{code}

\subsubsection{Axiom \AXeqvIdN}
$$\AXeqvId$$
\begin{code}
pred_Ax_eqvId  =  TRUE === (pQ === pQ)
law_Ax_eqvId = freeRootLaw "Ax-==-id" pred_Ax_eqvId
\end{code}
Related Conjectures:
\begin{eqnarray*}
   \textit{true} && \LNAME{TRUE}
\\ P \equiv P && \LNAME{$\equiv$-refl}
\end{eqnarray*}
\begin{code}
pred_Cj_TRUE  =  TRUE
conj_TRUE     =  ("TRUE",(pred_Cj_TRUE,SCtrue))
pred_Cj_eqvRefl  =  pP === pP
conj_eqvRefl  =  ("==-refl",(pred_Cj_eqvRefl,SCtrue))
\end{code}

\newpage
\subsubsection{Axiom \AXfalseDefN}
$$\AXfalseDef$$
\begin{code}
pred_Ax_falseDef  =  FALSE === Not TRUE
law_Ax_falseDef = freeRootLaw "Ax-FALSE-def" pred_Ax_falseDef
\end{code}

\subsubsection{Axiom \AXnotEqvDistrN}
$$\AXnotEqvDistr$$
\begin{code}
pred_Ax_notEqvDistr  =  Not (pP === pQ) === (Not pP === pQ)
law_Ax_notEqvDistr = freeRootLaw "Ax-~-==-distr" pred_Ax_notEqvDistr
\end{code}
Related Conjectures:
\begin{eqnarray*}
\end{eqnarray*}

\subsubsection{Axiom \AXorSymmN}
$$\AXorSymm$$
\begin{code}
pred_Ax_orSymm  =  pP \/ pQ === pQ \/ pP
law_Ax_orSymm = freeRootLaw "Ax-\\/-symm" pred_Ax_orSymm
\end{code}

\subsubsection{Axiom \AXorAssocN}
$$\AXorAssoc$$
\begin{code}
pred_Ax_orAssoc  =  (pP \/ pQ) \/ pR === pP \/ (pQ \/ pR)
law_Ax_orAssoc = freeRootLaw "Ax-\\/-assoc" pred_Ax_orAssoc
\end{code}

\subsubsection{Axiom \AXorIdemN}
$$\AXorIdem$$
\begin{code}
pred_Ax_orIdem  =  pP \/ pP === pP
law_Ax_orIdem = freeRootLaw "Ax-\\/-idem" pred_Ax_orIdem
\end{code}

\subsubsection{Axiom \AXorEqvDistrN}
$$\AXorEqvDistr$$
\begin{code}
pred_Ax_orEqvDistr  =  (pP \/ (pQ === pR))
                       ===
                       (pP \/ pQ === pP \/ pR)
law_Ax_orEqvDistr = freeRootLaw "Ax-\\/-==-distr" pred_Ax_orEqvDistr
\end{code}

\subsubsection{Axiom \AXexclMdlN}
$$\AXexclMdl$$
\begin{code}
pred_Ax_exclMdl  =  pP \/ Not pP
law_Ax_exclMdl = freeRootLaw "Ax-Excl-Mdl" pred_Ax_exclMdl
\end{code}

\subsubsection{Axiom \AXgoldRuleN}
$$\AXgoldRule$$
We prefer the version that associates to the right,
so it looks like a definition of $\land$.
\begin{code}
pred_Ax_goldRule  =  (pP /\ pQ)
                     ===
                     ( (pP === pQ)
                       ===
                      (pP \/ pQ) )
law_Ax_goldRule = freeRootLaw "Ax-Golden-Rule" pred_Ax_goldRule
\end{code}

\subsubsection{Axiom \AXimplDefN}
$$\AXimplDef$$
\begin{code}
pred_Ax_implDef  =  (pP ==> pQ)
                    ===
                    (pP \/ pQ === pQ)
law_Ax_implDef = freeRootLaw "Ax-=>-def" pred_Ax_implDef
\end{code}



\subsection{Putting Propositional Axioms together}
\begin{code}
rootPropAxioms
 = law_Ax_eqvAssoc
   ++ law_Ax_eqvSymm
   ++ law_Ax_eqvId
   ++ law_Ax_falseDef
   ++ law_Ax_notEqvDistr
   ++ law_Ax_orSymm
   ++ law_Ax_orAssoc
   ++ law_Ax_orIdem
   ++ law_Ax_orEqvDistr
   ++ law_Ax_exclMdl
   ++ law_Ax_goldRule
   ++ law_Ax_implDef
\end{code}


\subsection{Non-Propositional Axioms}

The non-propositional axioms are:
$$
\AXNONPROP
$$

%\AXAllOScope & \AXAllOScopeN
%  \\ \AXAllEScope & \AXAllEScopeN
%  \\ \AXAllPScope & \AXAllPScopeN

\newpage
\subsubsection{Axiom \protect\AXAllOScopeN}
$$\AXAllOScope$$
\begin{code}
pred_Ax_AllOScope
 =  mkAll qxsys pP === mkAll qys pP

sc_Ax_AllOScope = vxs `notPfree` nP

law_Ax_AllOScope = mkRootLaw "Ax-all-x-scope" pred_Ax_AllOScope sc_Ax_AllOScope
\end{code}

\subsubsection{Axiom \protect\AXAllEScopeN}
$$\AXAllEScope$$
\begin{code}
pred_Ax_AllEScope = Pvar (Std "ExprQuantNotSupported") ==> TRUE

sc_Ax_AllEScope = SCtrue

law_Ax_AllEScope = mkRootLaw "Ax-all-E-scope" pred_Ax_AllEScope sc_Ax_AllEScope
\end{code}

\subsubsection{Axiom \protect\AXAllPScopeN}
$$\AXAllPScope$$
\begin{code}
pred_Ax_AllPScope
 =   Pforall qPsQs pP === Pforall qPs pP

sc_Ax_AllPScope = vPs `notPfree` nP

law_Ax_AllPScope = mkRootLaw "Ax-all-P-scope" pred_Ax_AllPScope sc_Ax_AllPScope
\end{code}


\newpage
\subsubsection{Axiom \protect\AXorAllOScopeN}
$$\AXorAllOScope$$
\begin{code}
pred_Ax_orAllOScope
 = pP \/ mkAll qxsys pQ
   ===
   mkAll qxs (pP \/ mkAll qys pQ)

sc_Ax_orAllOScope = vxs `notPfree` nP

law_Ax_orAllOScope = mkRootLaw "Ax-\\/-all-x-scope" pred_Ax_orAllOScope sc_Ax_orAllOScope
\end{code}

\subsubsection{Axiom \protect\AXorAllEScopeN}
$$\AXorAllEScope$$
\begin{code}
pred_Ax_orAllEScope = Pvar (Std "ExprQuantNotSupported") ==> TRUE

sc_Ax_orAllEScope = SCtrue

law_Ax_orAllEScope = mkRootLaw "Ax-\\/-all-E-scope" pred_Ax_orAllEScope sc_Ax_orAllEScope
\end{code}

\subsubsection{Axiom \protect\AXorAllPScopeN}
$$\AXorAllPScope$$
\begin{code}
pred_Ax_orAllPScope
 = pP \/ Pforall qPsQs pQ
   ===
   Pforall qPs (pP \/ Pforall qPs pQ)

sc_Ax_orAllPScope = vPs `notPfree` nP

law_Ax_orAllPScope = mkRootLaw "Ax-\\/-all-P-scope" pred_Ax_orAllPScope sc_Ax_orAllPScope
\end{code}

\subsubsection{Axiom \protect\AXallODistrN}
$$\AXallODistr$$
\begin{code}
pred_Ax_allODistr
 = mkAll qxs (pP /\ pQ)
   ===
   (mkAll qxs pP) /\ (mkAll qxs pQ)

law_Ax_allODistr = freeRootLaw "Ax-all-O-distr" pred_Ax_allODistr
\end{code}

\subsubsection{Axiom \protect\AXallEDistrN}
$$\AXallODistr$$
\begin{code}
pred_Ax_allEDistr
 = Pvar (Std "ExprQuantNotSupported") ==> TRUE

law_Ax_allEDistr = freeRootLaw "Ax-all-E-distr" pred_Ax_allEDistr
\end{code}

\subsubsection{Axiom \protect\AXallPDistrN}
$$\AXallPDistr$$
\begin{code}
pred_Ax_allPDistr
 = Pforall qPs (pP /\ pQ)
   ===
   (Pforall qPs pP) /\ (Pforall qPs pQ)

law_Ax_allPDistr = freeRootLaw "Ax-all-P-distr" pred_Ax_allPDistr
\end{code}



\subsubsection{Axiom \protect\AXallOInstN}
$$\AXallOInst$$
\begin{code}
pred_Ax_allOInst
 = Forall 0 qxxs pP
   ==>
   Forall 0 qxs (Sub pP $ Substn [(vx,e)])

law_Ax_allOInst = freeRootLaw "Ax-all-x-inst" pred_Ax_allOInst
\end{code}

\subsubsection{Axiom \protect\AXallEInstN}
$$\AXallEInst$$
\begin{code}
pred_Ax_allEInst = Pvar (Std "ExprQuantNotSupported") ==> TRUE
law_Ax_allEInst = freeRootLaw "Ax-all-E-inst" pred_Ax_allEInst
\end{code}

\subsubsection{Axiom \protect\AXallPInstN}
$$\AXallPInst$$
\begin{code}
pred_Ax_allPInst
 = Pforall qPPs pQ
   ==>
   Pforall qPs (Psub pQ $ Substn [(Std nP,pR)])

law_Ax_allPInst = freeRootLaw "Ax-all-P-inst" pred_Ax_allPInst
\end{code}

\newpage
\subsubsection{Axiom \protect\AXallORngN}
$$\AXallORng$$
This is not implemented, but is supported implicitly by the pretty-printer
and parser.


\subsubsection{Axiom \protect\AXanyODefN}
$$\AXanyODef$$
\begin{code}
pred_Ax_anyODef
 = Exists 0 qxs pP
   ===
   (Not $ Forall 0 qxs $ Not pP)

law_Ax_anyODef = freeRootLaw "Ax-any-x-def" pred_Ax_anyODef
\end{code}

\subsubsection{Axiom \protect\AXanyEDefN}
$$\AXanyEDef$$
\begin{code}
pred_Ax_anyEDef = Pvar (Std "ExprQuantNotSupported") ==> TRUE
law_Ax_anyEDef = freeRootLaw "Ax-any-E-def" pred_Ax_anyEDef
\end{code}

\newpage
\subsubsection{Axiom \protect\AXanyPDefN}
$$\AXanyPDef$$
\begin{code}
pred_Ax_anyPDef
 = Pexists qPs pP
   ===
   (Not $ Pforall qPs $ Not pP)

law_Ax_anyPDef = freeRootLaw "Ax-any-P-def" pred_Ax_anyPDef
\end{code}

\subsubsection{Axiom \protect\AXunivClosureN}
$$\AXunivClosure$$
\begin{code}
pred_Ax_univClosure
 = Univ 0 pP
   === Forall 0 qxs pP

sc_Ax_univClosure = [vxs] `coverFreeOfP` nP

law_Ax_univClosure = mkRootLaw "Ax-[[-]]-def" pred_Ax_univClosure sc_Ax_univClosure
\end{code}

\subsubsection{Axiom \protect\AXanyORngN}
$$\AXanyORng$$
This is not implemented, but is supported implicitly by the pretty-printer
and parser.

\subsubsection{Axiom \protect\AXoneODefN}
$$
\AXoneODef
$$
CODE TO COME

\subsubsection{Axiom \protect\AXoneORngN}
$$
\AXoneORng
$$
CODE TO COME

\newpage
\subsubsection{Axiom \protect\AXeqReflN}
$$\AXeqRefl$$
\begin{code}
pred_Ax_eqRefl = e `equal` e

law_Ax_eqRefl = freeRootLaw "Ax-=-refl" pred_Ax_eqRefl
\end{code}

\subsubsection{Axiom \protect\AXtheDefN}
$$\AXtheDef$$
\begin{code}
pred_Ax_theDef
 = e `equal` (The 0 vx pP)
   ===
   Sub pP sube
   /\
   (Forall 0 qy (Sub pP suby ==> (eqy `equal` e)))
 where
   sube = Substn [(vx, e)]
   suby = Substn [(vx,evy)]

sc_Ax_theDef = vx `notEfree` n_e

law_Ax_theDef = mkRootLaw "Ax-the-def" pred_Ax_theDef sc_Ax_theDef
\end{code}

\subsubsection{Axiom \protect\AXtheRngN}
$$\AXtheRng$$
This is not implemented, but is supported implicitly by the pretty-printer
and parser.


\newpage
\subsubsection{Axioms \protect{\AXObetaRedN,\AXEbetaRedN,\AXPbetaRedN}}
$$\AXObetaRed$$
$$\AXEbetaRed$$
$$\AXPbetaRed$$
These axioms are implemented (in one direction, left-to-right, only)
by the do-substitution built-in commands
(\S\ref{Manip.Expr.Subst},p\pageref{Manip.Expr.Subst},
\S\ref{Manip.Pred.Subst},p\pageref{Manip.Pred.Subst}).
We also provide them as matchable laws that apply when
we have explicit substitutions.
\begin{code}
pred_Ax_betaORed
 = Pvar (Std "ExprLambdaApplicationNotSupported") ==> TRUE

law_Ax_betaORed = freeRootLaw "Ax_betaORed" pred_Ax_betaORed

pred_Ax_betaERed
 = Papp (Peabs (Q [ve,ves]) pQ) $ Obs e
   ===
   Sub (Peabs (Q [ves]) pQ) (Substn [(ve,e)])
 where
   e  = Evar $ preVar "e"
   ve = preVar "E"
   ves = lstVar "E"

law_Ax_betaERed = freeRootLaw "Ax_betaERed" pred_Ax_betaERed

pred_Ax_betaPRed
 = Papp (Ppabs (Q [p,ps]) pQ) pR
   ===
   Psub (Ppabs (Q [ps]) pQ) (Substn [(varGenRoot ps,pR)])
 where
   p = preVar "P"
   ps = lstVar "P"

law_Ax_betaPRed = freeRootLaw "Ax_betaPRed" pred_Ax_betaPRed
\end{code}

\newpage
\subsubsection{Axiom \protect\AXLeibnizN}
$$\AXLeibniz$$
or (\AXLLeibnizN):
$$\AXLLeibniz$$
The implementation relies on the fact that a pattern
of the form $\lst x=\lst e$, where $\lst x$ is a vector list-variable,
matches against conjunctions of such patterns,
i.e., $x_1=e_1 \land x_2 = e_2 \land \ldots \land x_n=e_n$,
for any $n >0$.
\begin{code}
pred_Ax_Leibniz
 = (xvec `equal` evec)
   ==>
   (pP === Sub pP (Substn [(vxs,evec)]))
 where
   xvec = Var $ vxs
   evec = Var $ lstVar n_e

law_Ax_Leibniz = freeRootLaw "Ax-Leibniz" pred_Ax_Leibniz
\end{code}

\subsubsection{Axioms \protect{\AXOSubstN,\AXESubstN,\AXPSubstN}}
$$\AXOSubst$$
$$\AXESubst$$
$$\AXPSubst$$
These axioms are implemented (in one direction, left-to-right, only)
by the do-substitution built-in commands
((\S\ref{Manip.Expr.Subst},p\pageref{Manip.Expr.Subst},
\S\ref{Manip.Pred.Subst},p\pageref{Manip.Pred.Subst})).
A right-to-left implementation (extracting out a substitution)
would be very hard to implement in general.

\newpage
\subsubsection{Axioms \protect{\AXTrueOSubN,\ldots,\AXFalsePSubN}}

\begin{mathpar}
\AXTrueOSub
\and \AXTrueESub
\and \AXTruePSub
\\ \AXFalseOSub
\and \AXFalseESub
\and \AXFalsePSub
\end{mathpar}
\begin{code}
pred_Ax_TRUE_OSubst
 = (Sub TRUE $ Substn [(vxs,Var $ lstVar "e")]) === TRUE
law_Ax_TRUE_OSubst = freeRootLaw "Ax-TRUE-xSubst" pred_Ax_TRUE_OSubst

pred_Ax_TRUE_ESubst = Pvar (Std "TRUEESubstNotSupported") ==> TRUE
law_Ax_TRUE_ESubst = freeRootLaw "Ax-TRUE-ESubst" pred_Ax_TRUE_ESubst

pred_Ax_TRUE_PSubst
 = (Psub TRUE $ Substn [(Std nPs,Pvar $ Std nQs)]) === TRUE
law_Ax_TRUE_PSubst = freeRootLaw "Ax-TRUE-PSubst" pred_Ax_TRUE_PSubst

pred_Ax_FALSE_OSubst
 = (Sub FALSE $ Substn [(vxs,Var $ lstVar "e")]) === FALSE
law_Ax_FALSE_OSubst = freeRootLaw "Ax-FALSE-xSubst" pred_Ax_FALSE_OSubst

pred_Ax_FALSE_ESubst = Pvar (Std "FALSEESubstNotSupported") ==> FALSE
law_Ax_FALSE_ESubst = freeRootLaw "Ax-FALSE-ESubst" pred_Ax_FALSE_ESubst

pred_Ax_FALSE_PSubst
 = (Psub FALSE $ Substn [(Std nPs,Pvar $ Std nQs)]) === FALSE
law_Ax_FALSE_PSubst = freeRootLaw "Ax-FALSE-PSubst" pred_Ax_FALSE_PSubst
\end{code}


\newpage
\subsection{Putting non-Propositional Axioms together}
\begin{code}
rootNonPropAxioms
 = law_Ax_AllOScope
   -- ++ law_Ax_AllEScope -- not supported
   ++ law_Ax_AllPScope
   ++ law_Ax_orAllOScope
   -- ++ law_Ax_orAllEScope -- not supported
   ++ law_Ax_orAllPScope
   ++ law_Ax_allODistr
   -- ++ law_Ax_allEDistr -- not supported
   ++ law_Ax_allPDistr
   ++ law_Ax_allOInst
   -- ++ law_Ax_allEInst -- not supported
   ++ law_Ax_allPInst
   ++ law_Ax_anyODef
   -- ++ law_Ax_anyEDef -- not supported
   ++ law_Ax_anyPDef
   ++ law_Ax_univClosure
   ++ law_Ax_eqRefl
   ++ law_Ax_theDef
   ++ law_Ax_Leibniz
   ++ law_Ax_TRUE_OSubst
   ++ law_Ax_TRUE_PSubst
   ++ law_Ax_FALSE_OSubst
   ++ law_Ax_FALSE_PSubst
\end{code}

\subsection{The ``root'' theory}

We define a ``root'' theory that simply (at present)
contains the precedence data for parsing standard binary logical connectives,
equality,
and both the propositional and non-propositional axioms.
\begin{code}
rootName =  sptName "ROOT"

rootTheory
  = (nmdNullPrfCtxt rootName)
    { precs = precsLogic `tmerge` precsEquality
    , types = boolOpTypes
    , laws = rootPropAxioms ++ rootNonPropAxioms
    }

rootRDAG = rdROOT rootName
\end{code}
