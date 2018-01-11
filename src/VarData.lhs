\section{Variable Data}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module VarData ( VarMatchRole
               , pattern KnownConst, pattern KnownVar, pattern UnknownVar
               , isKnownConst, isKnownVar, isUnknownVar
               , vmrConst, vmrType
               , LstVarMatchRole
               , pattern KnownVarList, pattern KnownVarSet
               , pattern AbstractList, pattern AbstractSet
               , pattern UnknownListVar
               , VarTable
               , vtList, stList, dtList
               , newVarTable
               , addKnownConst
               , addKnownVar
               , addKnownVarList , addKnownVarSet
               , lookupVarTable, lookupVarTables
               , lookupLVarTable, lookupLVarTables
               ) where
--import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (nub)

import Utilities
import LexBase
import Variables
import AST

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

\subsection{Variable Matching Categories}

Variables,
whether of static, or any dynamic flavour,
can belong to one of three categories as regards matching:
\begin{description}
  \item[Known Constant]
    The variable is static,
    and is a shorthand for a known fixed value.
    It can only match itself, or that known value.
    The value can be basic like a number,
    or it could denote something somewhat higher-order,
    such as a function or predicate.
    If the value is denoted by a term then any free variables
    present must aslo be known.
  \item[Known Variable]~\\
    \begin{enumerate}
      \item
        The variable is an static or dynamic (before/after) observation
        and can take many possible values from a defined type.
        it has a predefined interpretation in some intended semantic model,
        and can only match itself.
     \item
        The variable denotes expressions or predicates of a particular type.
    \end{enumerate}
  \item[Unknown]
    Nothing specific is known about the variable.
    It can match anything of the appropriate ``flavour''.
\end{description}
We refer, simply,
to variables in the first two categories above as ``known'',
while those in the third category are simply ``unknown''.
\begin{code}
data VarMatchRole -- Variable Matching Role
  =  KC Term  -- Known Constant ! any free vars in term must also be known
  |  KV Type  -- Known Variable
  |  UV       -- Unknown Variable
  deriving (Eq, Ord, Show, Read)

pattern KnownConst trm = KC trm
pattern KnownVar typ   = KV typ
pattern UnknownVar     = UV

isKnownConst, isKnownVar, isUnknownVar :: VarMatchRole -> Bool
isKnownConst (KC _) = True
isKnownConst _ = False
isKnownVar (KV _) = True
isKnownVar _= False
isUnknownVar UV = True
isUnknownVar _ = False

vmrConst :: VarMatchRole -> Term
vmrConst (KC trm)  =  trm
vmrConst (KV _)    =  error "vmrCont: var. match role is KnownVar"
vmrConst UV        =  error "vmrCont: var. match role is UnknownVar"

vmrType :: VarMatchRole -> Type
vmrType (KV typ)  =  typ
vmrType (KC _)    =  error "vmrType: var. match role is KnownConst"
vmrType UV        =  error "vmrType: var. match role is UnknownVar"
\end{code}

\newpage
\subsection{List-Variable Matching Categories}

List-variables can match either any list or set of variables,
of the same class,
or can also be ``known'',
as a name for a specific list or set of variables,
themselves also ``known''.
A known list-variables can only match itself,
or any expansion of what is known about its associated variable-list.
We also allow list variables to be abstract,
in that they can be instantiated later on to specific known variables.
An abstract list-variable can only match itself.

A concrete list-variable ultimately resolves dowwn
to a set or list of known variables.
The contents and size of that collection are important,
so we store this information explicilty here,
to avoind the need for matching algorithms to continually
re-compute this.

Static list-variables can match any variable list or set.
\begin{code}
data LstVarMatchRole -- ListVar Matching Roles
 = KL VarList        -- Known Variable-List, all of which are themselves known
      [Variable]     -- full expansion
      Int            -- length of full expansion
 | KS VarSet         -- Known Variable-Set, all of which are themselves known
      (Set Variable) -- full expansion
      Int            -- size of full expansion
 | AL                -- Abstract Known Variable-List
 | AS                -- Abstract Known Variable-Set
 | UL                -- Unknown List-Variable
 deriving (Eq, Ord, Show, Read)

pattern KnownVarList vl vars len  =  KL vl vars len
pattern KnownVarSet  vs vars siz  =  KS vs vars siz
pattern AbstractList              =  AL
pattern AbstractSet               =  AS
pattern UnknownListVar            =  UL
\end{code}

Dynamic before/after variables can only match
other dynamic ones in a consistent way regarding temporality
---
if a ``before'' list-variable matches a list/set of (``before'') variables,
then the corresponding ``after'' list-variable
must match the same list/set of (``after'') variables.
\begin{code}
type IdAndClass = (Identifier, VarClass)

data DynamicLstVarRole -- Dynamic ListVar Matching Roles
 = DL [Identifier]      -- Known-list, Variable identifiers
      [Identifier]      -- Known-list, List-Variable identifiers
      [Identifier]      -- full expansion
      Int               -- length of full expansion
 | DS (Set Identifier)  -- Known-set, Variable identifiers
      (Set Identifier)  -- Known-set, List-Variable identifiers
      (Set Identifier)  -- full expnasion
      Int               -- size of full expansion
 | DAL                  -- Abstract Known List
 | DAS                  -- Abstract Known Set
 | UD         -- Unknown Dynamic List-Variable
 deriving (Eq, Ord, Show, Read)
\end{code}

We will want to convert
a \texttt{DynamicLstVarRole} into a \texttt{LstVarMatchRole}
when results are returned.
This can be done by providing a variable class and temporality:
\begin{code}
mapDLVRtoLVMR :: VarClass -> VarWhen -> DynamicLstVarRole -> LstVarMatchRole
mapDLVRtoLVMR vc vw (DL is js xs n)
  =  KL (map (id2gvar vc vw) is ++ map (id2glvar vc vw) js)
        (map (id2var vc vw) xs) n
mapDLVRtoLVMR vc vw (DS is js xs n)
  =  KS (S.map (id2gvar vc vw) is `S.union` S.map (id2glvar vc vw) js)
        (S.map (id2var vc vw) xs)n
mapDLVRtoLVMR _ _ DAL  =  AL
mapDLVRtoLVMR _ _ DAS  =  AS
mapDLVRtoLVMR _ _ UD   =  UL

id2var   vc vw i  =                 Vbl i vc vw
id2gvar  vc vw i  =  StdVar       $ Vbl i vc vw
id2glvar vc vw j  =  LstVar $ LVbl (Vbl j vc vw) [] []
\end{code}

\newpage
\subsection{Variable Tables}

We define simple lookup tables,
into which we can insert entries for known variables and list-variables.
We use a newtype so we can control access.

We have a key invariant regarding variable temporality (\texttt{VarWhen}).
A variable or list-variable can only be mapped to variables and list-variables
of the same temporality.
Variables or list-variables that are \texttt{Static} can map to anything.
\begin{code}
newtype VarTable
  = VD ( Map Variable   VarMatchRole
       , Map ListVar    LstVarMatchRole
       , Map IdAndClass DynamicLstVarRole
       )
  deriving (Eq, Show, Read)
\end{code}


We will want to inspect tables.
\begin{code}
vtList :: VarTable -> [(Variable,VarMatchRole)]
vtList (VD (vtable, _, _)) = M.toList vtable
stList :: VarTable -> [(ListVar,LstVarMatchRole)]
stList (VD (_, stable, _)) = M.toList stable
dtList :: VarTable -> [(ListVar,LstVarMatchRole)]
dtList (VD (_, _, dtable)) = map dtMap $ M.toList dtable

dtMap ((i,vc),dlvr) = ( LVbl (Vbl i vc Before) [] []
                      , mapDLVRtoLVMR vc Before dlvr )
\end{code}


\subsubsection{Creating New Table}

\begin{code}
newVarTable :: VarTable
newVarTable = VD (M.empty, M.empty, M.empty)
\end{code}


\newpage
\subsection{Inserting into Tables}

We place restrictions on which entries can be updated.
One important one is that all free variables in a term
must already be known.
\begin{code}
inside :: Term -> VarTable -> Bool
t `inside` vt  =  all (found vt) $ freeVars t

found vt (StdVar v)   =  lookupVarTable vt v /= UV
found vt (LstVar lv)  =  lookupLVarTable vt lv /= UL

knownIn :: VarList -> VarTable -> Bool
vl `knownIn` vt = all (found vt) vl
\end{code}


\subsubsection{Inserting Known Constant}

\begin{code}
addKnownConst :: Monad m => Variable -> Term -> VarTable -> m VarTable
\end{code}
We can only update mappings to unknown variables.

Only static variables may name a constant,
and we must check that we won't introduce any cycles.
\begin{code}
addKnownConst var@(Vbl _ _ Static) trm vt@(VD (vtable,stable,dtable))
  = case M.lookup var vtable of
      Nothing | trm `inside` vt
        -> return $ VD ( M.insert var (KC trm) vtable,stable,dtable )
      Just UV | trm `inside` vt
        -> return $ VD ( M.insert var (KC trm) vtable,stable,dtable )
      _ -> fail "addKnownConst: trying to update, or unknown vars in term."

addKnownConst _ _ _ = fail "addKnownConst: not for Dynamic Variables."
\end{code}

\subsubsection{Inserting Known Variable}

\begin{code}
addKnownVar :: Monad m => Variable -> Type -> VarTable -> m VarTable
\end{code}

Only static, textual and before/after variables can
range over values of a given type.
\begin{code}
addKnownVar (ObsVar _ (During _)) _ _
  =  fail "addKnownVar: not for During Variables."

addKnownVar var typ (VD (vtable,stable,dtable))
  =  return $ VD ( M.insert var (KV typ) vtable,stable,dtable )
\end{code}

\newpage
\subsubsection{Inserting Known Variable-List}

\begin{code}
addKnownVarList :: Monad m => ListVar -> VarList -> VarTable -> m VarTable
\end{code}

Static List variables match lists of known variables
of the same class as themselves.
\begin{code}
addKnownVarList lv@(LVbl (Vbl _ _ Static) _ _) vl vt@(VD (vtable,stable,dtable))
 | mixed          =  fail "addKnownVarList: inconsistent classifications."
 | ct == CTmixed  =  fail "addKnownVarList(Static): some map to sets."
 | lv `S.member` img
     = fail "addKnownVarSet(Static): list-variable cycle."
 | otherwise
   = case M.lookup lv stable of
      Nothing | vl `knownIn` vt
                   -> return $ VD ( vtable, M.insert lv (KL vl [] 0) stable, dtable )
      Just UL | vl `knownIn` vt
                   -> return $ VD ( vtable, M.insert lv (KL vl [] 0) stable, dtable )
      Just AL | vl `knownIn` vt
                   -> return $ VD ( vtable, M.insert lv (KL vl [] 0) stable, dtable )
      _ -> fail "addKnownVarList(Static): trying to update, or unknown vars in list."
 where
  mixed       =  checkLVarListMap lv vl
  ( ct, img ) =  rtLstImage stable CTlist (S.fromList $ listVarsOf vl)
\end{code}

Dynamic list-variables
can only be defined as equal to a list of general variables,
with the same class and appropriate temporality.
We also need to check to avoid cycles, or a crossover to variable-sets.
\begin{code}
addKnownVarList lv@(LVbl (Vbl i vc vw) _ _) vl vt@(VD (vtable,stable,dtable))
 | mixed = fail  "addKnownVarList (dynamic): inconsistent classifications."
 | ct == CTmixed
     = fail "addKnownVarList(dynamic): some map to sets."
 | (i,vc) `S.member` img
      = fail "addKnownVarList(dynamic): list-variable cycle."
 | otherwise
   = case M.lookup (i,vc) dtable of
      Nothing | vl `knownIn` vt
        -> return $ VD (vtable, stable, M.insert (i,vc) (DL is js [] 0) dtable)
      Just UD | vl `knownIn` vt
        -> return $ VD (vtable, stable, M.insert (i,vc) (DL is js [] 0) dtable)
      Just DAL | vl `knownIn` vt
        -> return $ VD (vtable, stable, M.insert (i,vc) (DL is js [] 0) dtable)
      _ -> fail "addKnownVarList(dynamic): trying to update, or unknown vars in list."
 where
  mixed       =  checkLVarListMap lv vl
  ( ct, img ) =  rtDynImage dtable CTlist (iacOf vl)
  (is,js)     =  idsOf vl
\end{code}


A list-variable can only map to variables with the same \texttt{VarWhat} value,
and, if not \texttt{Static}, the same \texttt{VarWhen} value:
\begin{code}
checkLVarListMap lv [] = False
checkLVarListMap lv vl
  = [whatLVar lv] /= nub (map whatGVar vl)
      || (vtime /= Static && [vtime] /= nub (map timeGVar vl))
  where vtime = timeLVar lv
\end{code}

\begin{code}
iacOf vl  =  iacOf' [] [] vl
 where
  iacOf' si sj [] =  S.fromList (si++sj)
  iacOf' si sj ((StdVar       (Vbl i vc _)     ):vl)  =  iacOf' ((i,vc):si) sj vl
  iacOf' si sj ((LstVar (LVbl (Vbl j vc _) _ _)):vl)  =  iacOf' si ((j,vc):sj) vl
\end{code}

\newpage
\subsubsection{Inserting Known Variable-Set}

\begin{code}
addKnownVarSet :: Monad m => ListVar -> VarSet -> VarTable -> m VarTable
\end{code}
See Variable-List insertion above.

\begin{code}
addKnownVarSet lv@(LVbl (Vbl i vc Static) _ _) vs vt@(VD (vtable,stable,dtable))
 | mixed = fail "addKnownVarSet(static): inconsistent classifications."
 | ct == CTmixed
     = fail "addKnownVarSet(Static): some map to lists."
 | lv `S.member` img
     = fail "addKnownVarSet(Static): list-variable cycle."
 | otherwise
   = case M.lookup lv stable of
      Nothing | vl `knownIn` vt
        -> return $ VD (vtable, M.insert lv (KS vs S.empty 0) stable, dtable)
      Just UL | vl `knownIn` vt
        -> return $ VD (vtable, M.insert lv (KS vs S.empty 0) stable, dtable)
      Just AL | vl `knownIn` vt
        -> return $ VD (vtable, M.insert lv (KS vs S.empty 0) stable, dtable)
      _ -> fail "addKnownVarSet(Static): trying to update, or unknown vars in list."
 where
   mixed        =  checkLVarSetMap lv vs
   ( ct, img )  =  rtLstImage stable CTset (listVarSetOf vs)
   vl = S.toList vs
\end{code}

\begin{code}
addKnownVarSet lv@(LVbl (Vbl i vc vw) _ _) vs vt@(VD (vtable,stable,dtable))
  | mixed = fail "addKnownVarSet (dynamic): inconsistent classifications."
  | ct == CTmixed
      = fail $ unlines
          [ "addKnownVarSet(dynamic): some map to lists."
          , "vs = "++show vs
          , "dtable:", show dtable ]
  | (i,vc) `S.member` img
      = fail "addKnownVarSet(dynamic): list-variable cycle."
  | otherwise
   = case M.lookup (i,vc) dtable of
      Nothing | vl `knownIn` vt
       -> return $ VD ( vtable, stable
                      , M.insert (i,vc)
                                 (DS (S.fromList is) (S.fromList js) S.empty 0)
                                 dtable )
      Just UD | vl `knownIn` vt
       -> return $ VD ( vtable, stable
                      , M.insert (i,vc)
                                 (DS (S.fromList is) (S.fromList js) S.empty 0)
                                 dtable )
      Just DAS | vl `knownIn` vt
       -> return $ VD ( vtable, stable
                      , M.insert (i,vc)
                                 (DS (S.fromList is) (S.fromList js) S.empty 0)
                                 dtable )
      _ -> fail "addKnownVarSet(dynamic): trying to update, or unknown vars in list."
  where
   mixed       =  checkLVarSetMap lv vs
   ( ct, img ) =  rtDynImage dtable CTset (iacOf $ S.toList vs)
   vl          =  S.toList vs
   (is,js)     =  idsOf $ S.toList vs
\end{code}

\begin{code}
checkLVarSetMap lv vs
  = not (S.null vs)
    && ( (S.singleton $ whatLVar lv) /= S.map whatGVar vs
         ||
         (vtime /= Static && (S.singleton $ vtime) /= S.map timeGVar vs) )
  where vtime = timeLVar lv
\end{code}

\newpage
\subsection{Table Lookup}


\subsubsection{Variable Lookup}

Variable lookup is total, returning \texttt{UV} if the variable is not present.
\begin{code}
lookupVarTable :: VarTable -> Variable -> VarMatchRole
lookupVarTable (VD (vtable, _, _)) var
 = case M.lookup var vtable of
     Nothing   ->  UV
     Just vmr  ->  vmr
\end{code}


\subsubsection{List-Variable Lookup}


For list-variables we need to distinguish between
those whose temporality is \texttt{During},
and the others.
\begin{code}
lookupLVarTable :: VarTable -> ListVar -> LstVarMatchRole

lookupLVarTable (VD (_,stable,_)) lvar@(LVbl (Vbl _ _ Static) _ _)
 = case M.lookup lvar stable of
     Nothing    ->  UL
     Just lvmr  ->  lvmr

lookupLVarTable (VD (_,_,dtable)) lvar@(LVbl (Vbl i vc vw) _ _)
 = case M.lookup (i,vc) dtable of
     Nothing    ->  UL
     Just dlvr  ->  mapDLVRtoLVMR vc vw dlvr
\end{code}

\subsubsection{Searching Lists of Tables}

We also have a version that searches a list of tables:
\begin{code}
lookupVarTables :: [VarTable] -> Variable -> VarMatchRole
lookupVarTables [] _ = UV
lookupVarTables (vt:vts) v
 = case lookupVarTable vt v of
     UV   ->  lookupVarTables vts v
     vmr  ->  vmr
\end{code}


Again, we want to be able to search lists of tables.
\begin{code}
lookupLVarTables :: [VarTable] -> ListVar -> LstVarMatchRole
lookupLVarTables [] _ = UL
lookupLVarTables (vt:vts) lv
 = case lookupLVarTable vt lv of
     UL    ->  lookupLVarTables vts lv
     lvmr  ->  lvmr
\end{code}

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
uses a annihilator, an operator that removes all tuples $(u,v)$
from a relation, where $v$ does not itself appear in the lhs of a relation tuple.
Repeated application of the annihilator will reduce any relation down to just its cycles, or the empty relation, if there are no cycles.

Another technique is ensure acyclicity from the outset,
by checking a new maplet against the map to see if it will introduce a cycle.
Given a map $\mu$, and a set of variables $V$,
its \emph{relational image} w.r.t. $V$, denoted by $\mu(V)$ is
the union of all the $\mu(v)$ obtained for each $v \in V$.
The \emph{reflexive transitive image closure}
$\mu^*(V) = V \cup \mu(V) \cup \mu(\mu(V)) \cup \dots$.
When inserting a mapping from $u$ to $V$ into $\mu$,
we simply compute $\mu^*(V)$ and check that $u$ does not occur in it.

Tests in \texttt{proto/Acyclic.hs} show that the annihilator approach to
after-insertion acyclicity checking
is two-and-a-half times faster, approximately, than the transitive closure approach.
However, the insert-time check based on image closure is almost an
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
rtLstImage :: Map ListVar LstVarMatchRole -> CT -> Set ListVar
           -> ( CT, Set ListVar )
rtLstImage stable ct lvs = untilEq (rrLstImage stable) (ct, lvs)
\end{code}

Reflexive relation image:
\begin{code}
rrLstImage :: Map ListVar LstVarMatchRole -> ( CT, Set ListVar )
           -> ( CT, Set ListVar )
rrLstImage stable (ct, lvs)
   = ( mixes (ct:cts), S.unions (lvs:imgs) )
  where
    ( cts, imgs) = unzip $ map (lstVVlkp stable) (S.toList lvs)
\end{code}

Looking up the \texttt{ListVar -> VarList} fragment of a \texttt{VarTable}:
\begin{code}
lstVVlkp stable lv
 = case M.lookup lv stable of
    Just (KL gvl _ _)  ->  ( CTlist, S.fromList $ listVarsOf gvl )
    Just (KS gvs _ _)  ->  ( CTset,  listVarSetOf gvs )
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
