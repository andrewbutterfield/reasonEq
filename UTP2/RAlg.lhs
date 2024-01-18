\section{Reactive Algebra}

A (parameterisable) proof-context for Reactive Algebra

\begin{code}
module RAlg where
import Tables
import Datatypes
import DataText
import MatchTypes
--import Heuristics
import Laws
import Proof
import Theories
import DSL
--import Builtin
import Utilities
\end{code}

\subsection{Useful definitions}

\begin{code}
ralgProvenance = FromSOURCE "RAlg"
mkRAlgLaw = mklaw ralgProvenance
freeRAlgLaw = freelaw ralgProvenance
\end{code}


\subsection{The Algebra}

The only thing defined here is a series of conjectures
about named predicates, whose definitions are \emph{not} given here,
except for those that are derived from others in a standard way (like $DIV$).
Thus this proof context has limited value without another that
does have \texttt{pred}-table entries for the names used here.

We introduce each predicate, one-by-one.
For each which gives the laws it satisfies, both by itself,
and in concert with all previously introduced predicates.
We will start with those predicates common to all reactive theories,
and only later introduce those specific to ``slotted'' theories.
\begin{code}
alphaRAlg = Q (lnorm [ok,ok',wait,wait',obsList,obsList'])
raNAME name =  Pvar $ Std name
\end{code}


%=========================================================================
\newpage

\subsubsection{Predicate $GROW$}

$GROW$ asserts that the event history can only be extended.
\begin{code}

rGROW = raNAME "GROW"
gendefGROW = (rGROW,rGROW)

\end{code}
Laws:
\begin{eqnarray*}
  \elabel{GG:eq:G} && GROW ; GROW \equiv GROW
\end{eqnarray*}
\begin{code}

axiomsGROW
 = [("GG:eq:G",rGROW >>> rGROW === rGROW)
   ]

\end{code}

%=========================================================================

\newpage
\subsubsection{Predicate $DIV$}

$DIV$ asserts that if started unstably, all we can assert is $GROW$
\begin{eqnarray*}
  \elabel{DIV:def} && DIV \defs \lnot ok \land GROW
\end{eqnarray*}
\begin{code}

rDIV = raNAME "DIV"
gendefDIV = (rDIV,Not ok /\ rGROW)

\end{code}
Laws:
\begin{eqnarray*}
  \elabel{DD:eq:D} && DIV ; DIV \equiv DIV
\\\elabel{D:imp:G} && DIV \implies GROW
\\\elabel{DG:eq:D} && DIV; GROW \equiv DIV
\\\elabel{GD:eq:G} && GROW; DIV \equiv GROW
\end{eqnarray*}
We also add the following ``axiom'' for temporary testing purposes: $GROW;GROW \equiv GROW;DIV$
\begin{code}

axiomsDIV
 =  [("DD:eq:D",rDIV >>> rDIV === rDIV)
    ,("D:imp:G",rDIV ==> rGROW)
    ,("DG:eq:D",rDIV >>> rGROW === rDIV)
    ,("GD:eq:G",rGROW >>> rDIV === rGROW)
    ,("GD:eq:GG",rGROW >>> rGROW === rGROW >>> rDIV )
    ]

\end{code}

%=========================================================================
\newpage

\subsubsection{Predicate $RSTET$}

$RSTET$ asserts that all observational variables are unchanged,
except for $ok$ and any to do with
program variable state.

\begin{code}

rRSTET = raNAME "RSTET"
gendefRSTET = (rRSTET,rRSTET)

\end{code}
Laws:
\begin{eqnarray*}
  \elabel{RS-P:eq:P} && RSTET;P \equiv P, \qquad in\alpha(P) \subseteq \alpha(RSTET)
\\\elabel{P-RS:eq:P} && P;RSTET \equiv P, \qquad out\alpha(P) \subseteq \alpha(RSTET)
\\\elabel{RS:imp:G}  && RSTET \implies GROW
\end{eqnarray*}
As $GROW$ satisfies the side-condition throughout, and $DIV$ does for the second law above,
we get:
\begin{eqnarray*}
  \elabel{RS-RS:eq:RS} && RSTET;RSTET \equiv RSTET
\\\elabel{RS-G:eq:G}   && RSTET;GROW \equiv GROW
\\\elabel{G-RS:eq:G}   && GROW;RSTET \equiv GROW
\\\elabel{D-RS:eq:D}   && DIV;RSTET  \equiv DIV
\end{eqnarray*}

\begin{code}

axiomsRSTET
 =  [("RS:imp:G",rRSTET ==> rGROW)
    ,("RS-RS:eq:RS",rRSTET >>> rRSTET === rRSTET)
    ,("RS-G:eq:G",rRSTET >>> rGROW === rGROW)
    ,("G-RS:eq:G",rGROW >>> rRSTET === rGROW)
    ,("D-RS:eq:D",rDIV >>> rRSTET === rDIV)
    ]

\end{code}




%=========================================================================
\newpage

\subsubsection{Predicate $STET$}

$STET$ asserts that all observational variables are unchanged,
except for $ok$, and so is slightly stronger than $RSTET$.
In a theory with no state, such as that mainly discussed in \cite[Chp.~8]{UTP-book},
then $RSTET$ and $STET$ are equivalent.

\begin{code}

rSTET = raNAME "STET"
gendefSTET = (rSTET,rSTET)

\end{code}
Laws:
\begin{eqnarray*}
  \elabel{SP:eq:P}  && STET;P \equiv P, \qquad in\alpha(P) \subseteq \alpha(STET)
\\\elabel{PS:eq:P}  && P;STET \equiv P, \qquad out\alpha(P) \subseteq \alpha(STET)
\\\elabel{S:imp:G}  && STET \implies GROW
\\\elabel{S:imp:RS} && STET \implies RSTET
\end{eqnarray*}
As $GROW$ satisfies the side-condition throughout, and $DIV$ does for the second law above,
we get:
\begin{eqnarray*}
  \elabel{SS:eq:S} && STET;STET \equiv STET
\\\elabel{SG:eq:G}   && STET;GROW \equiv GROW
\\\elabel{GS:eq:G}   && GROW;STET \equiv GROW
\\\elabel{DS:eq:D}   && DIV;STET  \equiv DIV
\end{eqnarray*}

\begin{code}

axiomsSTET
 =  [("S:imp:G",rSTET ==> rGROW)
    ,("S:imp:RS",rSTET ==> rRSTET)
    ,("SS:eq:S",rSTET >>> rSTET === rSTET)
    ,("SG:eq:G",rSTET >>> rGROW === rGROW)
    ,("GS:eq:G",rGROW >>> rSTET === rGROW)
    ,("DS:eq:D",rDIV >>> rSTET === rDIV)
    ]

\end{code}


%=========================================================================
\newpage

\subsubsection{Predicate $\Skip$}

$\Skip$ extends $STET$ to handle key values of $ok$ and $ok'$
in a healthy manner:
\begin{eqnarray*}
  \elabel{II:def} && \Skip \defs DIV \lor ok' \land STET
\end{eqnarray*}

\begin{code}

rII = raNAME "II"
gendefII = (rII,rDIV \/ ok' /\ rSTET)

\end{code}
Laws:
\begin{eqnarray*}
  \elabel{IIII:eq:II}  && \Skip;\Skip \equiv \Skip
\\\elabel{II:imp:G} && \Skip \implies GROW
\end{eqnarray*}

\begin{code}

axiomsII
 =  [("IIII:eq:II",rII >>> rII  === rII)
    ,("II:imp:G",rII ==> rGROW)
    ]

\end{code}

Theorems provable in the algebra?:
\begin{eqnarray*}
  \elabel{nok-II:eq:DIV} && \lnot ok \land \Skip \equiv DIV
\\\elabel{"DIV;II:eq:DIV} && DIV ; \Skip \equiv DIV
\\\elabel{"II;DIV:eq:DIV} && \Skip ; DIV  \equiv DIV
\end{eqnarray*}

\begin{code}

theoremsII
 = [("nok-II:eq:DIV",Not ok /\ rII === rDIV)
   ,("DIV;II:eq:DIV",rDIV >>> rII === rDIV)
   ,("II;DIV:eq:DIV",rII >>> rDIV === rDIV)
   ]

\end{code}


%=========================================================================
\newpage

\subsection{The Reactive Algebra Axiomatic Proof-Context}

\begin{code}

rAlgAxPreds
 = plupdate tnil
    [ gendefGROW
    , gendefDIV
    , gendefRSTET
    , gendefSTET
    , gendefII
    ]


rAlgAxLaws
  = foldl1 (~:~) (map (uncurry freeRAlgLaw)
     (  axiomsGROW
     ++ axiomsDIV
     ++ axiomsRSTET
     ++ axiomsSTET
     ++ axiomsII
     ))

rAlgAxConjectures
  = foldl1 tmerge  (map (lupdate tnil)
     [ theoremsII
     ])

rAlgAxProofContext
  = (buildLangDefinitions .markTheoryDeps)
      ((nmdNullPrfCtxt "RAlgAxioms")
                      { preds = rAlgAxPreds
                      , laws = rAlgAxLaws
                      , conjectures = tmap trivSC rAlgAxConjectures
                      })

\end{code}

\subsection{The Reactive Algebra Conjecture Proof-Context}

\begin{code}

rAlgCjPreds
 = plupdate tnil
    [
    ]


rAlgCjLaws
  = []

rAlgCjConjectures
  = foldl1 tmerge (map (lupdate tnil)
     [ axiomsGROW
     ++axiomsDIV
     ++axiomsRSTET
     ++axiomsSTET
     ++axiomsII
     ++theoremsII
     ])

rAlgCjProofContext
  = (buildLangDefinitions . markTheoryDeps)
       ((nmdNullPrfCtxt "RAlgConjs")
                       { preds = rAlgCjPreds
                       , laws = rAlgCjLaws
                       , conjectures = tmap trivSC rAlgCjConjectures
                       })

\end{code}
