\newpage
\subsection{Ensuring \texttt{VarTable} Acyclicity}

\textbf{
THE FOLLOWING IS NOW NOT REQUIRED.
BY REQUIRING ANY VARIABLE OR LIST-VARIABLE TO ONLY POINT
AT KNOWN VARIABLES WE AUTOMATICALLY ENSURE ACYCLICITY.
}

We have an invariant that there are no cycles in any \texttt{VarTable}.
Simplifying, we can imagine we have a relation between variables
expressed as a set-valued partial, finite map.
\begin{equation}
  \mu  \in Rel = V \fun \Set V
\end{equation}
So if  $\mu$ represents relation $R$,
then we say that if $u R v$, then $v \in \mu(u)$.

There are many ways to check for acyclicity.
The most well-known computes $R^+$,
the transitive closure of the relation,
and then checks for all $u \in \dom R$ that $\lnot(uR^+u)$.
Another, based on MMA's thesis%
\footnote{
  M\'iche\'al Mac An Airchinnigh, Conceptual Modelling
, University of Dublin, 1990.
}
uses a annihilator, an operator that removes all tuples $(u,v)$ from a relation,
where $v$ does not itself appear in the lhs of a relation tuple.
Repeated application of the annihilator will reduce any relation
down to just its cycles, or the empty relation, if there are no cycles.

Another technique is to ensure acyclicity from the outset,
by checking a new maplet against the map to see if it will introduce a cycle.
Given a map $\mu$, and a set of variables $V$,
its \emph{relational image} w.r.t. $V$, denoted by $\mu(V)$ is
the union of all the $\mu(v)$ obtained for each $v \in V$.
The \emph{reflexive transitive image closure}
$\mu^*(V) = V \cup \mu(V) \cup \mu(\mu(V)) \cup \dots$.
When inserting a mapping from $u$ to $V$ into $\mu$,
we simply compute $\mu^*(V)$ and check that $u$ does not occur in it.

Tests in \texttt{proto/Acyclic.hs} show that
the annihilator approach to after-insertion acyclicity checking
is two-and-a-half times faster,
approximately,
than the transitive closure approach.
However,
the insert-time check based on image closure is almost an
order of magnitude faster than either acyclic check.
So here we decide to use the insert-time check
to ensure that we are not about to create such cycles.

We have two mappings, but can consider them seperately.
The standard variable mapping is of the form \texttt{Variable -> Variable},
and so any cycles must remain within in it.
The list-variable mapping has form \texttt{ListVar -> Set GenVar},
which can include \texttt{Variable}.
However any pointers to \texttt{StdVar} will jump over
to the standard variable mapping and stay there.
Only pointers to \texttt{LstVar} have the potential to lead to cycles.

\subsubsection{Standard Variable Reflexive-Transitive Image}

Reflexive, transitive relational image:
\begin{code}
rtStdImage :: Map Variable VarMatchRole -> Set Variable
           -> Set Variable
rtStdImage vtable vs = untilEq (rrStdImage vtable) vs
\end{code}

Reflexive relation image:
\begin{code}
rrStdImage :: Map Variable VarMatchRole -> Set Variable
           -> Set Variable
rrStdImage vtable vs = S.unions (vs:map (stdVVlkp vtable) (S.toList vs))
\end{code}

Looking up the \texttt{Variable -> Variable} fragment of a \texttt{VarTable}:
\begin{code}
stdVVlkp vtable v
 = case M.lookup v vtable of
    Just (KC (Var _ v'))  ->  S.singleton v'
    _                     ->  S.empty
\end{code}

\newpage
\subsubsection{List-Variable Reflexive-Transitive Image}

There is an additional invariant which states
that if we have a relational chain of list-variables,
then either they all map to variable-lists, or variable-sets,
but not both.
So $\{ lu \mapsto \seqof{lv}, lv \mapsto \seqof{lw} \}$
and $\{ lu \mapsto \setof{lv}, lv \mapsto \setof{lw} \}$
are ``uniform'', hence OK,
while $\{ lu \mapsto \seqof{lv}, lv \mapsto \setof{lw} \}$
or $\{ lu \mapsto \setof{lv}, lv \mapsto \seqof{lw} \}$
are ``mixed'', and therefore not OK.
\begin{code}
data CT = CTunknown | CTset | CTlist | CTmixed  deriving (Eq, Show)

mix CTunknown ct = ct
mix ct CTunknown = ct
mix CTmixed _ = CTmixed
mix _ CTmixed = CTmixed
mix ct1 ct2
 | ct1 == ct2  =  ct1
 | otherwise   =  CTmixed

mixes = foldl mix CTunknown
\end{code}
We keep track of chain types when computing relation images (next).


\paragraph{Static Relational Chains}
~

Reflexive, transitive relational image:
\begin{code}
rtLstImage :: Map Variable LstVarMatchRole -> CT -> Set Variable
           -> ( CT, Set Variable )
rtLstImage stable ct lvs = untilEq (rrLstImage stable) (ct, lvs)
\end{code}

Reflexive relation image:
\begin{code}
rrLstImage :: Map Variable LstVarMatchRole -> ( CT, Set Variable )
           -> ( CT, Set Variable )
rrLstImage stable (ct, lvs)
   = ( mixes (ct:cts), S.unions (lvs:imgs) )
  where
    ( cts, imgs) = unzip $ map (lstVVlkp stable) (S.toList lvs)
\end{code}

Looking up the \texttt{ListVar -> VarList} fragment of a \texttt{VarTable}:
\begin{code}
lstVVlkp stable lv
 = case M.lookup lv stable of
    Just (KL gvl _ _)  ->  ( CTlist, S.fromList $ map varOf $ listVarsOf gvl )
    Just (KS gvs _ _)  ->  ( CTset,  S.map varOf $ listVarSetOf gvs )
    _                  ->  ( CTunknown, S.empty )
\end{code}


\paragraph{Dynamic Relational Chains}
~

Reflexive, transitive relational image:
\begin{code}
rtDynImage :: Map IdAndClass DynamicLstVarRole -> CT -> Set IdAndClass
           -> ( CT, Set IdAndClass )
rtDynImage dtable ct iacs = untilEq (rrDynImage dtable) (ct, iacs)
\end{code}

Reflexive relation image:
\begin{code}
rrDynImage :: Map IdAndClass DynamicLstVarRole -> ( CT, Set IdAndClass )
           -> ( CT, Set IdAndClass )
rrDynImage dtable (ct, iacs)
   = ( mixes (ct:cts), S.unions (iacs:imgs) )
  where
    ( cts, imgs) = unzip $ map (dynIIlkp dtable) (S.toList iacs)
\end{code}

Looking up the \texttt{IdAndClass -> ([Identifier],[Identifier])}
fragment of a \texttt{VarTable}.
We are conservative here, treating $x$ and $\lst x$ as the same.
\begin{code}
dynIIlkp dtable iac@(i,vc)
 = case M.lookup iac dtable of
    Just (DL il jl _ _)  ->  ( CTlist, S.fromList $ zip (il++jl) vcOmega )
    Just (DS is js _ _)  ->  ( CTset,  S.map add_vc (is `S.union` js) )
    _                    ->  ( CTunknown, S.empty )
 where
   vcOmega = vc:vcOmega
   add_vc i = (i,vc)
\end{code}
