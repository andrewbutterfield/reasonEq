\section{Variable Data}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module VarData ( VarMatchRole
               , pattern KnownConst, pattern KnownVar
               , pattern GenericVar, pattern InstanceVar, pattern UnknownVar
               , isKnownConst, isKnownVar, isGenericVar, isInstanceVar
               , isUnknownVar
               , vmrConst, vmrType, vmrInst
               , LstVarMatchRole
               , pattern KnownVarList, pattern KnownVarSet
               , pattern AbstractList, pattern AbstractSet
               , pattern UnknownListVar
               , VarTable
               , vtList, stList, dtList
               , newVarTable
               , addKnownConst, addKnownVar
               , addGenericVar, addInstanceVar
               , addKnownVarList , addKnownVarSet
               , addAbstractVarList, addAbstractVarSet
               , lookupVarTable, lookupVarTables
               , lookupLVarTable, lookupLVarTables
               , isUnknownStdVar, isUnknownLstVar, isUnknownGVar
               , dEq, dvEq, dlEq, dgEq
               , insideS                    -- member modulo During
               , withinS                    -- subset modulo During
               , delS, delSl, delL          -- delete modulo During
               , removeS, removeSl, removeL -- remove modulo During
               , intsctS, intsctSl          -- intersection modulo During
               , KnownExpansion
               , expandKnown
               , genExpandToList
               , genExpandToSet
               ) where
--import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (nub, deleteBy, deleteFirstsBy, intersectBy, (\\))

import Utilities
import LexBase
import Variables
import AST
import FreeVars

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

\newpage
\subsection{Variable Matching Categories}

Variables,
whether of static, or any dynamic flavour,
can belong to one of the following categories as regards matching:
\begin{description}
  \item[Known Constant]
    The variable is static,
    and is a shorthand for a known fixed value.
    It can only match itself, or that known value.
    The value can be basic like a number,
    or it could denote something somewhat higher-order,
    such as a function or predicate.
    If the value is denoted by a term then any free variables
    present must also be known.
  \item[Known Variable]~\\
    Either (i) the variable is an static or dynamic (before/after) observation
        and can take many possible values from a defined type.
        it has a predefined interpretation in some intended semantic model,
        and can only match itself;
     \\or (ii) the variable denotes expressions or predicates of a particular type.
  \item[Generic Variable]~\\
    This is a variable used to define some generic properties,
    via appropriate axioms.
    It will match only itself,
    or instance variables that have been defined as one of its instances
    (see next entry).
  \item[Instance Variable]~\\
    A variable declared to be an instance of a generic variable.
    It only matches itself.
  \item[Unknown]
    Nothing specific is known about the variable.
    It can match anything of the appropriate ``flavour''.
\end{description}
We refer, simply,
to variables in the all but the last categories above, as ``known'',
while those in the last category are simply ``unknown''.
\begin{code}
data VarMatchRole -- Variable Matching Role
  =  KC Term     -- Known Constant ! any free vars in term must also be known
  |  KV Type     -- Known Variable
  |  KG          -- Generic Variable
  |  KI Variable -- Instance Variable ! variable must be known as generic
  |  UV          -- Unknown Variable
  deriving (Eq, Ord, Show, Read)

pattern KnownConst trm = KC trm
pattern KnownVar typ   = KV typ
pattern GenericVar     = KG
pattern InstanceVar v  = KI v
pattern UnknownVar     = UV
\end{code}

\newpage
Useful predicates and destructors:
\begin{code}
isKnownConst (KC _)  = True
isKnownConst _       = False
isKnownVar (KV _)    = True
isKnownVar _         = False
isGenericVar KG      = True
isGenericVar _       = False
isInstanceVar (KI _) = True
isInstanceVar _      = False
isUnknownVar UV      = True
isUnknownVar _       = False

vmrConst :: VarMatchRole -> Term
vmrConst (KC trm) =  trm
vmrConst _        =  error "vmrConst: not known constant"

vmrType :: VarMatchRole -> Type
vmrType (KV typ) =  typ
vmrType _        =  error "vmrType: not known variable"

vmrInst :: VarMatchRole -> Variable
vmrInst (KI v)  =  v
vmrInst _       =  error "vmrInst: not generic instance"
\end{code}

\newpage
\subsection{List-Variable Matching Categories}

List-variables can match either any list or set of variables,
of the same class,
or can also be ``known'',
as a name for a specific list or set of variables,
themselves also ``known''.
A known list-variable can only match itself,
or any expansion of what is known about its associated variable-list.
We also allow list variables to be abstract,
in that they can be instantiated later on to specific known variables.
An abstract list-variable can only match itself.

A concrete list-variable ultimately resolves down
to a set or list of known variables.
The contents and size of that collection are important,
so we store this information explicilty here,
to avoid the need for matching algorithms to continually
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
We note that the subtracted-identifier lists in list-variables
are irrelevant here, so use a variable as the map domain
element in each case.

We have a key invariant regarding variable temporality (\texttt{VarWhen}).
A dynamic variable or list-variable can only be mapped to variables and list-variables
of the same temporality.
Variables or list-variables that are \texttt{Static} can map to anything.
This means that for dynamic variables,
we use domain and range types that do not mention temporality.
\begin{code}
newtype VarTable
  = VD ( Map Variable   VarMatchRole
       , Map Variable   LstVarMatchRole
       , Map IdAndClass DynamicLstVarRole
       )
  deriving (Eq, Show, Read)
\end{code}


We will want to inspect tables.
\begin{code}
vtList :: VarTable -> [(Variable,VarMatchRole)]
vtList (VD (vtable, _, _)) = M.toList vtable
stList :: VarTable -> [(Variable,LstVarMatchRole)]
stList (VD (_, stable, _)) = M.toList stable
dtList :: VarTable -> [(Variable,LstVarMatchRole)]
dtList (VD (_, _, dtable)) = map dtMap $ M.toList dtable

dtMap ((i,vc),dlvr) = ( Vbl i vc Before, mapDLVRtoLVMR vc Before dlvr )
\end{code}


\subsubsection{Creating New Table}

\begin{code}
newVarTable :: VarTable
newVarTable = VD (M.empty, M.empty, M.empty)
\end{code}

As a general principle,
we only support the addition of new entries for now.
Updating in general involves more complicated checks
and will be added if required.

\newpage
\subsection{Inserting Variable Entries}


\subsubsection{Inserting Known Constants}

\begin{code}
addKnownConst :: Monad m => Variable -> Term -> VarTable -> m VarTable
\end{code}

When adding a term entry
we require that all free variables in a term
must already be ``known'' in the table.
\begin{code}
absent vt (StdVar v)             =  lookupVarTable vt v == UV
absent vt (LstVar (LVbl v _ _))  =  lookupLVarTable vt v == UL
\end{code}

Only static variables may name a constant,
and we must check that we won't introduce any cycles.
\begin{code}
addKnownConst var@(Vbl _ _ Static) trm vt@(VD (vtable,stable,dtable))
  | StdVar var `S.member` freev  =  fail "addKnownConst: variable in term."
  | any (absent vt) freev        =  fail "addKnownConst: term has unknowns."
  | otherwise
    = case M.lookup var vtable of
        Nothing  ->  return $ VD ( M.insert var (KC trm) vtable,stable,dtable )
        Just UV  ->  return $ VD ( M.insert var (KC trm) vtable,stable,dtable )
        _ -> fail "addKnownConst: cannot update."
  where
     freev = freeVars trm

addKnownConst _ _ _ = fail "addKnownConst: not for Dynamic Variables."
\end{code}


\subsubsection{Inserting Known Variables}

\begin{code}
addKnownVar :: Monad m => Variable -> Type -> VarTable -> m VarTable
\end{code}

Only static, textual and before/after variables can
range over values of a given type.
We also note that just because a textual, before or after variable
is added,
this does not mean that we automatically induce its temporal counterparts.
So adding $x:T$ (before) does not mean that we have also added $x':T$.
This is in contrast to the treatment of list-variables,
where such treatment always occurs.
\begin{code}
addKnownVar (ObsVar _ (During _)) _ _
  =  fail "addKnownVar: not for During Variables."

-- we allow updating here as it does not effect table integrity.
addKnownVar var typ (VD (vtable,stable,dtable))
  =  return $ VD ( M.insert var (KV typ) vtable,stable,dtable )
\end{code}

\newpage
\subsubsection{Inserting Generic Variables}

\begin{code}
addGenericVar :: Monad m => Variable -> VarTable -> m VarTable
\end{code}

For now we do not place any restrictions,
except that the variable cannot already be present in the table
but might limit these to static term variables in the future.
\begin{code}
addGenericVar var vt@(VD (vtable,stable,dtable))
  = case M.lookup var vtable of
      Just _ -> fail "addGenericVar: variable already present"
      Nothing -> return $ VD (M.insert var KG vtable, stable, dtable )
\end{code}

\subsubsection{Inserting Instance Variables}

\begin{code}
addInstanceVar :: Monad m => Variable -> Variable -> VarTable -> m VarTable
\end{code}

We require that the variable we are inserting is not already present,
and that the variable we are linking to is present as generic.
For now we expect both variables to have the same class and temporality.
\begin{code}
addInstanceVar ivar gvar vt@(VD (vtable,stable,dtable))
 | whatVar ivar /= whatVar gvar = fail "addInstanceVar: class mismatch."
 | timeVar ivar /= timeVar gvar = fail "addInstanceVar: temporality mismatch."
 | otherwise
     = case M.lookup ivar vtable of
         Just _ -> fail "addInstanceVar: variable already present"
         Nothing
          -> case M.lookup gvar vtable of
               Just KG
                -> return $ VD (M.insert ivar (KI gvar) vtable, stable, dtable )
               _ -> fail "addInstanceVar: no such generic variable"
\end{code}

\newpage
\subsection{Inserting List-Variable Entries}

List-variables entries can be concrete or abstract.
Abstract entries mean the corresponding list-variable is to be treated as known,
but currently is not associated with a specific variable-list.
This is useful for very general theories that introduce key concepts
that have a common definition across a wide range of more specific theories.
The most obvious example of this is sequential composition.

Concrete entries are those where the list-variable is
defined to be equivalent to a given variable-list.
Concrete list variable entries can only refer to (general) variables that are
already known and are themselves concrete,
i.e., already present in the tables.

All variable entries (known or constant) are considered to be concrete.

\subsubsection{Checking Variable Container Contents}

We need to check a proposed variable-container (set/list)
to see that it satisfies the requirements given above.
We also need to ensure, if the list-variable is dynamic,
that all the container variables have the same temporality
as that list-variable.
If a list-variable is to be defined as a list of variables,
then none of the list-variables in that last can denote a variable-set.
This is because there is no really good way to convert a
set of variables into a list.
There is no similar constraint for the converse case,
where a proposed set of variables contains those that define lists,
as there is a unique canonical way to convert a list to a set.

We define a function to check all of the above
that works with lists, preserving order.

\begin{code}
checkVariableList
  :: Monad m
  => VarTable  -- the table
  -> Variable -- the variable component of the list-variable about to be defined
  -> Bool     -- true if set-valued list-variables are allowed
  -> VarList
  -> m ( [Variable] -- the full expansion
       , Int )      -- length of full expansion

checkVariableList vt lv@(Vbl i vc0 vw0) setsOK vl
 = case vw0 of
     Static  ->  chkVL (const False)   [] 0 vl
     _       ->  chkVL (not . dEq vw0) [] 0 vl
 where

  chkVL invalid srav len [] = return (reverse srav, len)

  chkVL invalid srav len (StdVar v@(Vbl _ vc vw):vl)
    | vc /= vc0   =  fail "checkVariableList: class mismatch"
    | invalid vw  =  fail "checkVariableList: temporality mismatch"
    | otherwise
       = case lookupVarTable vt v of
           UV  ->  fail "checkVariableList: unknown variable"
           _   ->  chkVL invalid (v:srav) (len+1) vl

  chkVL invalid srav len (LstVar (LVbl v@(Vbl _ vc vw) _ _):vl)
    | vc /= vc0   =  fail "checkVariableList: class mismatch"
    | invalid vw  =  fail "checkVariableList: temporality mismatch"
    | otherwise
       = case lookupLVarTable vt v of
           UL  ->  fail "checkVariableList: unknown list-variable"
           KL _ kvl klen  ->  chkVL invalid (reverse kvl++srav) (len+klen) vl
           AL             ->  chkVL invalid (v:srav)            (len+1)    vl
           KS _ kvs ksize | setsOK
                        ->  chkVL invalid (S.toList kvs++srav) (len+ksize) vl
           AS | setsOK  ->  chkVL invalid (v:srav)             (len+1)     vl
           _ -> fail "checkVariableList: sets not permitted."
\end{code}

\subsubsection{Inserting Known Variable-List}

\begin{code}
addKnownVarList :: Monad m => Variable -> VarList -> VarTable -> m VarTable
\end{code}

Static List variables match lists of known variables
of the same class as themselves.
\begin{code}
addKnownVarList lv@(Vbl _ _ Static) vl vt@(VD (vtable,stable,dtable))
 = case M.lookup lv stable of
    Nothing  ->  newSKVL lv vl vt
    Just UL  ->  newSKVL lv vl vt
    _        ->  fail "addKnownVarList(Static): trying to update."
 where
   newSKVL lv vl vt@(VD (vtable,stable,dtable))
    = do ( expanse, size ) <- checkVariableList vt lv False vl
         return $ VD (vtable, M.insert lv (KL vl expanse size) stable, dtable)
\end{code}

Dynamic list-variables
can only be defined as equal to a list of general variables,
with the same class and appropriate temporality.
We also need to check to avoid cycles, or a crossover to variable-sets.
\begin{code}
addKnownVarList lv@(Vbl i vc vw) vl vt@(VD (vtable,stable,dtable))
 = case M.lookup iac dtable of
    Nothing  ->  newDKVL lv vl vt
    Just UD  ->  newDKVL lv vl vt
    _        ->  fail "addKnownVarList(dynamic): trying to update."
 where
   iac = (i,vc)
   newDKVL lv vl vt@(VD (vtable,stable,dtable))
    = do ( expanse, size ) <- checkVariableList vt lv False vl
         let (is,js) = idsOf vl
         let xis = map varId expanse
         return $ VD (vtable, stable, M.insert iac (DL is js xis size) dtable)
\end{code}


A list-variable can only map to variables with the same \texttt{VarClass} value,
and, if not \texttt{Static}, the same \texttt{VarWhen} value:
\begin{code}
checkLVarListMap v [] = False
checkLVarListMap v vl
  = [whatVar v] /= nub (map whatGVar vl)
      || (vtime /= Static && [vtime] /= nub (map timeGVar vl))
  where vtime = timeVar v
\end{code}

\newpage
\subsubsection{Inserting Known Variable-Set}

\begin{code}
addKnownVarSet :: Monad m => Variable -> VarSet -> VarTable -> m VarTable
\end{code}
See Variable-List insertion above.

\begin{code}
addKnownVarSet lv@(Vbl i vc Static) vs vt@(VD (vtable,stable,dtable))
 = case M.lookup lv stable of
    Nothing  ->  newSKVS lv vs vt
    Just UL  ->  newSKVS lv vs vt
    _        ->  fail "addKnownVarSet(Static): trying to update."
 where
   newSKVS lv vs vt@(VD (vtable,stable,dtable))
    = do ( expanse, size ) <- checkVariableList vt lv True $ S.toList vs
         let expS = S.fromList expanse
         return $ VD (vtable, M.insert lv (KS vs expS size) stable, dtable)
\end{code}

\begin{code}
addKnownVarSet lv@(Vbl i vc vw) vs vt@(VD (vtable,stable,dtable))
 = case M.lookup iac dtable of
    Nothing  ->  newDKVS lv vs vt
    Just UD  ->  newDKVS lv vs vt
    _        ->  fail "addKnownVarSet(dynamic): trying to update."
 where
   iac = (i,vc)
   vl = S.toList vs
   newDKVS lv vs vt@(VD (vtable,stable,dtable))
    = do ( expanse, size ) <- checkVariableList vt lv True vl
         let (is,js) = idsOf vl
         let iS = S.fromList is
         let jS = S.fromList js
         let xiS = S.fromList $ map varId expanse
         return $ VD (vtable, stable, M.insert iac (DS iS jS xiS size) dtable)
\end{code}

\subsubsection{Inserting Abstract Variable-List}

\begin{code}
addAbstractVarList :: Monad m => Variable -> VarTable -> m VarTable

addAbstractVarList lv@(Vbl _ _ Static) (VD (vtable,stable,dtable))
 = case M.lookup lv stable of
     Nothing -> return $ VD(vtable,M.insert lv AL stable,dtable)
     _ -> fail "addAbstractVarList(Static): already present"

addAbstractVarList lv@(Vbl i vc vw) (VD (vtable,stable,dtable))
 = case M.lookup (i,vc) dtable of
     Nothing -> return $ VD(vtable,stable,M.insert (i,vc) DAL dtable)
     _ -> fail "addAbstractVarList(dynamic): already present"
\end{code}

\subsubsection{Inserting Abstract Variable-Set}

\begin{code}
addAbstractVarSet :: Monad m => Variable -> VarTable -> m VarTable

addAbstractVarSet lv@(Vbl _ _ Static) (VD (vtable,stable,dtable))
 = case M.lookup lv stable of
     Nothing -> return $ VD(vtable,M.insert lv AS stable,dtable)
     _ -> fail "addAbstractVarSet(Static): already present"

addAbstractVarSe lv@(Vbl i vc vw) (VD (vtable,stable,dtable))
 = case M.lookup (i,vc) dtable of
     Nothing -> return $ VD(vtable,stable,M.insert (i,vc) DAS dtable)
     _ -> fail "addAbstractVarSet(dynamic): already present"
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
lookupLVarTable :: VarTable -> Variable -> LstVarMatchRole

lookupLVarTable (VD (_,stable,_)) lvar@(Vbl _ _ Static)
 = case M.lookup lvar stable of
     Nothing    ->  UL
     Just lvmr  ->  lvmr

lookupLVarTable (VD (_,_,dtable)) lvar@(Vbl i vc vw)
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
lookupLVarTables :: [VarTable] -> Variable -> LstVarMatchRole
lookupLVarTables [] _ = UL
lookupLVarTables (vt:vts) lv
 = case lookupLVarTable vt lv of
     UL    ->  lookupLVarTables vts lv
     lvmr  ->  lvmr
\end{code}

We also want to determine if a variable is not known:
\begin{code}
isUnknownStdVar :: [VarTable] -> GenVar -> Bool
isUnknownStdVar vts (StdVar v)  =  lookupVarTables  vts v == UV
isUnknownStdVar vts _           =  False

isUnknownLstVar :: [VarTable] -> GenVar  -> Bool
isUnknownLstVar vts (LstVar (LVbl v _ _))  =  lookupLVarTables vts v == UL
isUnknownLstVar vts _                          =  False

isUnknownGVar   :: [VarTable] -> GenVar   -> Bool
isUnknownGVar   vts (StdVar v)  =  lookupVarTables  vts v == UV
isUnknownGVar   vts (LstVar (LVbl v _ _))  =  lookupLVarTables vts v == UL
\end{code}

\newpage
\subsection{Operations ``modulo \texttt{During}''}

When matching variable lists and sets,
we often need to do equality comparisons
that ignore \texttt{During} subscript values.
\begin{code}
dEq :: VarWhen -> VarWhen -> Bool
(During _) `dEq` (During _)  =  True
vw1        `dEq` vw2         =  vw1 == vw2

dvEq :: Variable -> Variable -> Bool
(Vbl i1 vc1 vw1) `dvEq` (Vbl i2 vc2 vw2)
 = i1 == i2 && vc1 == vc2 && vw1 `dEq` vw2

dlEq :: ListVar -> ListVar -> Bool
(LVbl v1 is1 js1) `dlEq` (LVbl v2 is2 js2)
 = v1 `dvEq` v2 && is1 == is2 && js1 == js2

dgEq :: GenVar -> GenVar -> Bool
(StdVar v1)  `dgEq` (StdVar v2)   =  v1 `dvEq` v2
(LstVar lv1) `dgEq` (LstVar lv2)  =  lv1 `dlEq` lv2
_            `dgEq` _             =  False
\end{code}

We need to various relations and operators
to work with the above ``subscript-blind'' comparisons.

\subsubsection{Membership/Subset Relation ``modulo \texttt{During}''}

\begin{code}
insideS :: GenVar -> VarSet -> Bool
insideS gv vs = insideL (S.toList vs) gv

insideL :: VarList -> GenVar -> Bool
insideL []       gv0  =  False
insideL (gv:gvs) gv0
 | gv `dgEq` gv0     =  True
 | otherwise         =  insideL gvs gv0

withinS :: VarSet -> VarSet -> Bool
vs1 `withinS` vs2 = (S.toList vs1) `withinL` (S.toList vs2)

withinL :: VarList -> VarList -> Bool
vl1 `withinL` vl2 -- for all v in vl1, v in vl2 (mod. During-subscripts)
 = all (insideL vl2) vl1
\end{code}

\subsubsection{Delete/Difference Operation ``modulo \texttt{During}''}

\begin{code}
delS :: GenVar -> VarSet -> VarSet
delS gv vs = S.fromList $ delSl gv vs

delSl :: GenVar -> VarSet -> VarList
delSl gv vs = delL gv $ S.toList vs

delL gv lv = deleteBy dgEq gv lv

removeS  :: VarSet -> VarSet -> VarSet
vs1 `removeS` vs2 = S.fromList (vs1 `removeSl` vs2)

removeSl  :: VarSet -> VarSet -> VarList
vs1 `removeSl` vs2 = S.toList vs1 `removeL` S.toList vs2

removeL :: VarList -> VarList -> VarList
vl1 `removeL` vl2 = deleteFirstsBy dgEq vl1 vl2
\end{code}

\subsubsection{Intersect Operation ``modulo \texttt{During}''}

Note that order is important here.
All the intersection values will come from the first argument.
\begin{code}
intsctS  :: VarSet -> VarSet -> VarSet
vs1 `intsctS` vs2 = S.fromList (vs1 `intsctSl` vs2)

intsctSl  :: VarSet -> VarSet -> VarList
vs1 `intsctSl` vs2 = S.toList vs1 `intsctL` S.toList vs2

intsctL :: VarList -> VarList -> VarList
vl1 `intsctL` vl2 = intersectBy dgEq vl1 vl2
\end{code}


\newpage
\subsection{Evaluating Known List-Variables}

If a list variable $\lst K$ is ``known'' in a \texttt{VarTable},
then we can obtain it's complete pure variable expansion.
Given one with associated subtracted identifiers ($\lst K\less{is;js}$)
we can derive some further information
regarding what part of that expansion remains:
\begin{description}
  \item[Subtracted variables ($is$)]
    If known, then they can be removed from the complete expansion.
    Otherwise, we know that one (arbitrary?) variable can be removed
    from that expansion.
  \item[Subtracted list-variables ($js$)]
     If known, their expansions can be removed.
     Otherwise, zero or more variables can be removed from the expansion
     of $\lst K$.
\end{description}
\begin{code}
type KnownExpansion
 = ( LstVarMatchRole -- fully expanded results with knowns subtracted
   , [Identifier]   -- remaining unknown is components
   , [Identifier] ) -- remaining unknown js components
\end{code}
Here, we treat a list-variable,
that has variables subtracted from it that are not part of its expansion,
as being erroneous.
\begin{code}
expandKnown :: Monad m => [VarTable] -> ListVar -> m KnownExpansion

expandKnown vts lv@(LVbl v@(Vbl i vc vw) is js)
 = case lookupLVarTables vts v of
     KL kvl expL eLen -> listRemove kvl expL eLen (expandLess vts vc vw is js)
     KS kvs expS eSiz -> setRemove  kvs expS eSiz (expandLess vts vc vw is js)
     AL               -> return (AL, is, js)
     AS               -> return (AS, is, js)
     _ -> fail "expandKnown: not known."
\end{code}

We return an integer and three lists: the known variables to be removed,
plus the $is$ and $js$ that are not known.
The integer is the length of the known variables list.
\begin{code}
expandLess :: [VarTable] -> VarClass -> VarWhen
           -> [Identifier] -> [Identifier]
           -> ( Int            -- no. of known vars
              , [Variable]     -- known vars
              , [Identifier]   -- unknown vars
              , [Identifier] ) -- unknown list-vars
expandLess vts vc vw is js
 = expIS 0 [] [] is
 where

   expIS n kvs uis [] = expJS n kvs uis [] js
   expIS n kvs uis (i:is)
    = case lookupVarTables vts v of
       UV  ->  expIS n kvs (i:uis) is
       _   ->  expIS (n+1) (v:kvs) uis is
    where v = Vbl i vc vw

   expJS n kvs uis ujs [] = (n, reverse kvs, reverse uis, reverse ujs)
   expJS n kvs uis ujs (j:js)
    = case lookupLVarTables vts lv of
       KL _ vs m  ->  expJS (n+m) (reverse vs++kvs)  uis ujs js
       KS _ vs m  ->  expJS (n+m) (S.toList vs++kvs) uis ujs js
       _ -> expJS n kvs uis (j:ujs) js
    where lv = Vbl j vc vw
\end{code}

\newpage
Given the result of \texttt{expandLess},
we can now update the \texttt{LstVarMatchRole}
to take account for the known subtracted variables.
This will fail if we are subtracting too much,
or the wrong things.
\begin{code}
listRemove :: Monad m
           => VarList -> [Variable] -> Int
           -> ( Int            -- no. of known vars
              , [Variable]     -- known vars
              , [Identifier]   -- unknown vars
              , [Identifier] ) -- unknown list-vars
           -> m ( LstVarMatchRole
                 , [Identifier]   -- remaining unknown is components
                 , [Identifier] ) -- remaining unknown js components
listRemove kvl expL eLen (n,kvr,uis,ujs)
  | eLen < n + luis = fail "expandKnown(listings): extra subtracted variables."
  | null (kvr \\ expL)
     = return ( KL kvl (expL \\ kvr) (eLen - n), uis, ujs)
  | otherwise  =  fail "expandKnown(List): irrelevant subtracted variables."
  where
    luis = length uis
\end{code}

Doing it again, with sets
\begin{code}
setRemove  :: Monad m
           => VarSet -> (Set Variable) -> Int
           -> ( Int            -- no. of known vars
              , [Variable]     -- known vars
              , [Identifier]   -- unknown vars
              , [Identifier] ) -- unknown list-vars
           -> m ( LstVarMatchRole
                 , [Identifier]   -- remaining unknown is components
                 , [Identifier] ) -- remaining unknown js components
setRemove  kvs expS eSiz (n,kvr,uis,ujs)
  | eSiz < n + luis  =  fail "expandKnown(Set): extra subtracted variables"
  | kvrS `S.isSubsetOf` expS
     = return ( KS kvs (expS S.\\ kvrS) (eSiz - n), uis, ujs)
  | otherwise  =  fail "expandKnown(Set): irrelevant subtracted variables"
  where
    luis = length uis
    kvrS = S.fromList kvr
\end{code}

Sometimes we expect very specific expansion results.

\begin{code}
genExpandToList vts (StdVar v) = return ([v],[],[])
genExpandToList vts (LstVar lv)
 = case expandKnown vts lv of
     Just ((KnownVarList _ expL _), uis, ujs)  ->  return (expL,uis,ujs)
     _ -> fail "vlExpandMatch: unknown lvar, or set-valued."
\end{code}

\begin{code}
genExpandToSet vts (StdVar v) = return (S.singleton v,[],[])
genExpandToSet vts (LstVar lv)
 = case expandKnown vts lv of
     Just ((KnownVarSet _ expS _), uis, ujs) -> return (expS,uis,ujs)
     _ -> fail "vlExpandMatch: unknown lvar, or list-valued."
\end{code}
