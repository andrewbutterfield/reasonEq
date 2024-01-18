\section{Reactive Systems}

Experimenting with Reactive Systems

\begin{code}
module R where
import Tables
import Datatypes
import Heuristics
import DataText
import Laws
import Proof
import Theories
import DSL hiding (ii)
import RootTheory
import Builtin
import UTP
import RAlg
import Utilities
\end{code}

\begin{code}
rProvenance = FromSOURCE "RAlg"
mkRLaw = mklaw rProvenance
freeRLaw = freelaw rProvenance
\end{code}


We shall build a table of key predicates:
\begin{code}
predR0 :: Trie Pred
predR0 = tnil
\end{code}



We build some useful types:
\begin{code}
rTyDefTable :: Trie Type
rTyDefTable = lbuild [("Event",tEvent)]

rObsTable :: Trie ObsKind
rObsTable
  = lbuild
     [ (ok,(ok,Model,B)),(ok',(ok,Model,B))
     , (wait,(wait,Model,B)),(wait',(wait',Model,B))
     , (state,(state,Model,Tenv)),(state',(state',Model,Tenv))
     , (tr,(tr,Model,tTrace)),(tr',(tr',Model,tTrace))
     , (ref,(ref,Model,tRef)),(ref',(ref',Model,tRef))
     ]


r_obs = lnorm [ok,wait,state,tr,ref]
r_obs' = lnorm [ok',wait',state',tr',ref']
r_alpha = Q (mrgnorm r_obs r_obs')

eqo t o1 o2 = Obs (o1 `Equal` o2)
eqbool (Obs v1) (Obs v2) = Obs (v1 `Equal` v2)

rComp n p q
 = mkAny (Q obsmid) (And [p',q'])
 where
   obs = [ok,wait,state,tr,ref]
   addn v = v ++ ntxt
   ntxt = show n
   obsmid = map (decorVar $ Subscript ntxt) obs
   p' = Sub p pre_sub
   q' = Sub q post_sub
   mides = map Var obsmid
   pre_sub = mkQsubst mides (map (decorVar Post) obs)
   post_sub = mkQsubst mides obs
\end{code}

\subsection{Healthiness Conditions}

\subsubsection{R1}

\begin{eqnarray*}
   GROW &\defs& tr \le tr'
\\ \RR1(P) &\defs& P \land GROW
\end{eqnarray*}
\begin{code}
alphaGROW = Q (lnorm [tr,tr'])
defGROW = Obs (tr `pfx` tr')
grow = Pvar $ Std "GROW"
defR1 = Ppabs qP ((Pvar $ Std "P") /\ grow)
r1 = Pvar $ Std "R1"

predR1
 = plupdate predR0
    [(grow,defGROW)
    ,(r1,defR1)
    ]
\end{code}

\subsubsection{R2}

\begin{eqnarray*}
   r2_s &\defs& [s,s\cat(tr'-tr)/tr,tr']
\\ \RR2(P) &\defs& \exists s @ P[r2_s]
\end{eqnarray*}
\begin{code}
trdiff = tr' `ssub` tr
r2sub v = Substn [(tr,Var v),(tr',(Var v) `cat` trdiff)]
defR2 v = Ppabs qP (mkAny (Q [v]) (Sub (Pvar $ Std "P") (r2sub v)))
r2 = Pvar $ Std "R2"

predR2
 = plupdate predR1
    [(r2,defR2 $ subVar "0" tr)
    ]
\end{code}

\subsubsection{R3}

\begin{eqnarray*}
   DIV &\defs& \lnot ok \land GROW
\\ RSTET &\defs& wait'=wait \land tr'=tr \land ref'=ref
\\ STET &\defs& RSTET \land state'=state
\\ \Skip &\defs& DIV \lor ok' \land STET
\\ \RR3(P) &\defs& \Skip \cond{wait} P
\end{eqnarray*}
\begin{code}
eqState = eqo Tenv
eqTrace = eqo tTrace
eqRef   = eqo tRef

defDIV = Not ok /\ grow
alphaDIV = Q (lnorm [ok,tr,tr'])
divg = Pvar $ Std "DIV"
eqw = wait' `eqbool` wait
eqt = tr' `eqTrace` tr
eqr = ref' `eqRef` ref
eqs = state' `eqState` state
defRSTET = And [eqw,eqt,eqr]
alphaRSTET = Q (lnorm [wait,wait',tr,tr',ref,ref'])
rstet = Pvar $ Std "RSTET"
defSTET = rstet /\ eqs
alphaSTET = Q (lnorm [wait,wait',state,state',tr,tr',ref,ref'])
stet = Pvar $ Std "STET"
defII = divg \/ ok' /\ stet
ii = Pvar $ Std "II"
defR3 = Ppabs qP (If wait ii (Pvar $ Std "P"))
r3 = Pvar $ Std "R3"

predR3
 = plupdate predR2
    [(divg,defDIV)
    ,(rstet,defRSTET)
    ,(stet,defSTET)
    ,(ii,defII)
    ,(r3,defR3)
    ]
\end{code}

\subsubsection{R}
\begin{eqnarray*}
    \RR{} &\defs& \RR3 \circ \RR2 \circ \RR1
\end{eqnarray*}

\begin{code}
defR = Ppabs qP (Papp r3 (Papp r2 (Papp r1 (Pvar $ Std "P"))))
rr = Pvar $ Std "RR"

predR3'
 = plupdate predR3
    [(rr,defR)
    ]
\end{code}


\subsubsection{CSP1}

\begin{eqnarray*}
   \CSP1(P) &\defs& P \lor DIV
\end{eqnarray*}
\begin{code}
defCSP1 = Ppabs qP (Pvar (Std "P") \/ divg)
csp1 = Pvar $ Std "CSP1"

predR4
 = plupdate predR3'
    [(csp1,defCSP1)
    ]
\end{code}

\subsubsection{CSP2}

\begin{eqnarray*}
   J &\defs& ok \implies ok' \land STET
\\ \CSP2(P) &\defs& P;J
\end{eqnarray*}
\begin{code}

defJ = (ok ==> ok') /\ stet
j = Pvar $ Std "JAY"
defCSP2 = Ppabs qP (Pvar (Std "P") >>> j)
csp2 = Pvar $ Std "CSP2"

predR5
 = plupdate predR4
    [(j,defJ)
    ,(csp2,defCSP2)
    ]
\end{code}


\subsection{Healthiness Properties}

\subsubsection{Idempotency}

\begin{eqnarray*}
   \H(\H(P)) &\equiv& \H(P)
\end{eqnarray*}
\begin{code}
assertIdem h
 = Papp h (Papp h p) === Papp h p
 where p = Pvar $ Std "P"
\end{code}

\subsubsection{Commutativity}

\begin{eqnarray*}
   \H_1(\H_2(P)) &\equiv& \H_2(\H_1(P))
\end{eqnarray*}
\begin{code}
assertComm h1 h2
 = Papp h1 (Papp h2 p) === Papp h2 (Papp h1 p)
 where p = Pvar $ Std "P"
\end{code}

\subsection{Semantics}

\subsubsection{$CHAOS$}

\begin{eqnarray*}
  CHAOS &\defs& \RR{}(True)
\end{eqnarray*}
\begin{code}
defCHAOS = Papp r TRUE
chaos = Pvar $ Std "CHAOS"

predR6
 = plupdate predR5
    [(chaos,defCHAOS)
    ]
\end{code}


\subsubsection{$STOP$}

\begin{eqnarray*}
  \delta &\defs& \RR3(tr'=tr \land wait')
\\ STOP &\defs& \CSP1(ok' \land \delta)
\\      &\equiv& \RR{}(wait := true)
\end{eqnarray*}
\begin{code}
defDELTA = Papp r3 (eqt /\ wait')
delta = Pvar $ Std "DELTA"
defSTOP = Papp csp1 (ok' /\ delta)
stop = Pvar $ Std "STOP"

predR7
 = plupdate predR6
    [(delta,defDELTA)
    ,(stop,defSTOP)
    ]
\end{code}

\subsubsection{$SKIP$}

\begin{eqnarray*}
   SKIP &\defs& \RR{}(\exists ref @ \Skip)
\end{eqnarray*}
\begin{code}
defSKIP = Papp r (mkAny (Q [ref]) ii)
skip = Pvar $ Std "SKIP"

predR8
 = plupdate predR7
    [(skip,defSKIP)
    ]
\end{code}

\subsubsection{$a \then SKIP$}

\begin{eqnarray*}
   B &\defs& tr'=tr \cond{wait'} \lor tr < tr'
\\ \Phi &\defs& \RR{} \circ and_B
\\      &\equiv& and_B \circ \RR{}
\\ do_A(a) &\defs& \Phi(a \not\in ref' \cond{wait'} tr'=tr\cat\seqof a)
\\ a \then SKIP &\defs& \CSP1(ok' \land do_A(a))
\end{eqnarray*}
\begin{code}
defINCR = Obs ( tr `spfx` tr')
incr = Pvar $ Std "INCR"
defB = If wait' eqt incr
bb = Pvar $ Std "BEE"
defPHI = Ppabs qP (Papp r (bb /\ Pvar (Std "P")))
phi = Pvar $ Std "PHI"
single a = Seq [a]
defDOA a
 = Peabs (Q [a]) (Papp phi
               (If wait'
                  (Not (Obs (vara `mof` ref')))
                  (Obs (tr' `Equal` (tr `cat` single vara))) ))
  where vara = Var a; tRefMember = Tprod [tEvent,tRef]
doA = Pvar $ Std "DOA"
defDOTHEN a = Peabs (Q [a]) (Papp csp1 (ok' /\ (Papp doA (Obs (Var a)))))
dothen = Pvar $ Std "DOTHEN"

predR9
 = plupdate predR8
    [(incr,defINCR)
    ,(bb,defB)
    ,(phi,defPHI)
    ,(doA,defDOA $ preVar "a")
    ,(dothen,defDOTHEN $ preVar "a")
    ]
\end{code}


\subsubsection{$stuff$}


\subsection{And the Theory is \ldots}

\begin{code}
reactiveName = "Reactive"


rtt = predR9

reactivePredTable = rtt
reactiveByName = tlookup reactivePredTable
reactiveByPvar = pVarLookup reactivePredTable
\end{code}

\subsubsection{R-specific laws}


\begin{code}
rCompDef
  = (p >>> q) === (rComp 0 p q)
  where
    p = Pvar $ Std " P"
    q = Pvar $ Std " Q"

rLawTable
   =   freeRLaw "DEF-R-;" rCompDef
\end{code}

\subsection{Reactive Conjectures}

We include here conjectures that are relevant to the
specific Reactive theory of \cite[Chp.~8]{UTP-book}.
General conjectures that apply to the Reactive theory, Circus
and slotted-Circus are in the Reactive-Algebra \texttt{Theory} (\texttt{RAlg}).

\begin{code}
reactiveConjectures
 = lupdate tnil
    [("tr0-existence"
      ,(mkAny qtr0 ((Obs (tr `pfx` vtr0)) /\ (Obs (vtr0 `pfx` tr')))) === defGROW)
    ,("R1-idem",Papp r1 (Papp r1 p) === Papp r1 p)
    ,("tr-offset",Obs (Equal (strdiff `ssub` sv) trdiff))
    ,("offset-pfx",sv `ppfx` strdiff === tr `ppfx` tr')
    ,("r2-sub-sub",(Sub (Sub (Pvar $ Std "P") (r2sub t)) (r2sub s)) === (Sub (Pvar $ Std "P") (r2sub t)))
    ,("R2-idem",Papp r2 (Papp r2 p) === Papp r2 p)
    ,("R1-R2-comm",(Papp r1 (Papp r2 p)) === (Papp r2 (Papp r1 p)))
    ,("R1-R3-comm",(Papp r1 (Papp r3 p)) === (Papp r3 (Papp r1 p)))
    ,("R2-R3-comm",(Papp r2 (Papp r3 p)) === (Papp r3 (Papp r2 p)))
    ,("gstop-P:eq:gstop",(Papp r3 gstop) >>> (Papp r3 p) === (Papp r3 gstop))
    ,("R3-;-close",((Papp r3 p) >>> (Papp r3 q )) === (Papp r3 (p >>> (Papp r3 q ))))
    ]
 where tr0 = subVar "0" tr ; qtr0 = Q [tr0] ; vtr0 = Var tr0
       p = Pvar $ Std "P"
       s = preVar "s" ; t = preVar "t"
       gstop = And [q,ok',wait'] ; q = Pvar $ Std "Q"
       sv = Var s; strdiff = sv `cat` trdiff
\end{code}

\begin{code}
rProofContext
  = (buildLangDefinitions . markTheoryDeps)
        ((nmdNullPrfCtxt "R")
                      { syntaxDeps
                          = [ rootName
                            , equalityName
                            , arithmeticName
                            , setsName
                            , listsName
                            , utpName
                            ]
                      , obs = rObsTable
                      , typedefs = rTyDefTable
                      , preds = reactivePredTable
                      , laws = rLawTable
                      , conjectures = tmap trivSC reactiveConjectures
                      })
\end{code}
