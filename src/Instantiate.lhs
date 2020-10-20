\section{Instantiate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Instantiate
( instantiate
, instVarSet
, instantiateASC
, instantiateSC
, findUnboundVars, termLVarPairings
, mkEquivClasses -- should be elsewhere
, mkFloatingBinding, autoInstantiate
) where
import Data.Maybe
-- import Data.Either (lefts,rights)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List

import Utilities
import LexBase
import Variables
import AST
import SideCond
import Binding
import FreeVars
import VarData
import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
pdbg nm x = dbg ('@':nm++":\n") x
\end{code}

\subsection{Introduction}

We take a pattern term and a binding
and produce a re-constructed candidate term,
provided every variable in the pattern is also in the binding.

\newpage
\subsubsection{Instantiating Term with a Binding}

We require every free variable in the term to be also in the binding.
\begin{code}
instantiate :: Monad m => Binding -> Term -> m Term

instantiate binding val@(Val _ _) = return val

instantiate binding vt@(Var tk v)
  = case lookupVarBind binding v of
      Just (BindVar v')   ->  var tk v'
      Just (BindTerm t')  ->  return t'
      Nothing             ->  fail $ unlines
                                     [ "instantiate: variable not found"
                                     , "var = " ++ trVar v
                                     , "bind = " ++ trBinding binding
                                     ]

instantiate binding (Cons tk n ts)
  = fmap (Cons tk n) $ sequence $ map (instantiate binding) ts

instantiate binding (Bnd tk n vs tm)
  = do vs' <- instVarSet binding vs
       tm' <- instantiate binding tm
       bnd tk n vs' tm'

instantiate binding (Lam tk n vl tm)
  = do vl' <- instVarList binding vl
       tm' <- instantiate binding tm
       lam tk n vl' tm'

instantiate binding (Cls n tm)
  = do tm' <- instantiate binding tm
       return $ Cls n tm'

instantiate binding (Sub tk tm s)
  = do tm' <- instantiate binding tm
       s' <- instSub binding s
       return $ Sub tk tm' s'

instantiate binding (Iter tk na ni lvs)
  = do lvtss <- instIterLVS binding lvs
       -- all have same non-zero length
       -- have the same kind of object (list-var/term)
       case lvtss of
         [lvts]  ->  return $ mkI lvts
         _       ->  return $ Cons tk na $ map mkI lvtss
  where
    mkI :: [LVarOrTerm] -> Term
    mkI lvts@(Right _:_) = Cons tk ni    $ tmsOf lvts
    mkI lvts@(Left  _:_) = Iter tk na ni $ lvsOf lvts
\end{code}

\newpage

We expect the substitution target and replacement list-variables
to be bound to variable-lists, and not sets.
These lists should themselves only contain list-variables,
and for any target/replacement pair these lists will be of the same length.
\begin{code}
instSub :: Monad m => Binding -> Substn -> m Substn
instSub binding (Substn ts lvs)
  = do ts'  <- instZip (instVar binding)  (instantiate binding) (S.toList ts)
       lvss' <- instZip (instLLVar binding) (instLLVar binding) (S.toList lvs)
       let (lvts,lvrs) = unzip lvss'
       let lvs' = zip (concat lvts) (concat lvrs)
       substn ts' lvs'
\end{code}


\begin{code}
instZip inst1 inst2 pairs
  = sequence $ map (instPair inst1 inst2) pairs
  where
    instPair inst1 inst2 (thing1,thing2)
      = do thing1' <- inst1 thing1
           thing2' <- inst2 thing2
           return (thing1',thing2')
\end{code}

\begin{code}
instVarSet :: Monad m => Binding -> VarSet -> m VarSet
instVarSet binding vs
  = fmap S.unions $ sequence $ map (instSGVar binding) $ S.toList vs
\end{code}

\begin{code}
instVarList :: Monad m => Binding -> VarList -> m VarList
instVarList binding vl
  = fmap concat $ sequence $ map (instLGVar binding) vl
\end{code}

\begin{code}
instLLVar :: Monad m => Binding -> ListVar -> m [ListVar]
instLLVar binding lv
  = case lookupLstBind binding lv of
      Just (BindList vl')  ->  fromGVarToLVar vl'
      Just (BindSet  vs')  ->  fromGVarToLVar $ S.toList vs'
      Just (BindTLVs tlvs)
        | null ts          ->  return lvs
        | otherwise        ->  fail $ unlines
                                     [ "instLLVar: l-var bound to terms"
                                     , "l-var = " ++ trLVar lv
                                     , "bind = " ++ trBinding binding
                                     ]
        where (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
      Nothing              ->  fail $ unlines
                                     [ "instLLVar: l-var not found"
                                     , "l-var = " ++ trLVar lv
                                     , "bind = " ++ trBinding binding
                                     ]
\end{code}

\begin{code}
fromGVarToLVar :: Monad m => VarList -> m [ListVar]
fromGVarToLVar [] = return []
fromGVarToLVar (StdVar v:vl)
 = fail ("fromGVarToLVar: Std variable found - " ++ show v)
fromGVarToLVar (LstVar lv:vl)
  = do lvs <- fromGVarToLVar vl
       return (lv:lvs)
\end{code}

\newpage
\begin{code}
instSGVar :: Monad m => Binding -> GenVar -> m VarSet
instSGVar binding (StdVar v)
  =  fmap (S.singleton . StdVar) $ instVar binding v
instSGVar binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return $ S.singleton gv  -- maps to self !
      Just (BindList vl')  ->  return $ S.fromList vl'
      Just (BindSet  vs')  ->  return vs'
      Just (BindTLVs tlvs)
        | null ts          ->  return $ S.fromList $ map LstVar lvs
        | otherwise        ->  fail "instSGVar: bound to terms."
        where (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
\end{code}

\begin{code}
instLGVar :: Monad m => Binding -> GenVar -> m VarList
instLGVar binding (StdVar v)
  =  fmap ((\x -> [x]) . StdVar) $ instVar binding v
instLGVar binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return [gv]  -- maps to self !
      Just (BindList vl')  ->  return vl'
      _ -> fail "instLGVar: bound to sets or terms."
\end{code}

\begin{code}
instTLGVar :: Monad m => Binding -> GenVar -> m [LVarOrTerm]
instTLGVar binding (StdVar v)
  =  fmap ((\t -> [t]) . injV) $ instVar binding v
instTLGVar binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return $ [injLV lv]  -- maps to self !
      Just (BindList vl')  ->  return $ map injGV vl'
      Just (BindTLVs tlvs) ->  return tlvs
      _ -> fail "instTLGVar: bound to sets."

injV :: Variable -> LVarOrTerm
injV = injTM . var2term
injGV :: GenVar -> LVarOrTerm
injGV (StdVar v)   =  injV v
injGV (LstVar lv)  =  injLV lv
\end{code}

% \begin{code}
% instGVar :: Monad m => Binding -> GenVar -> m GenVar
% instGVar binding (StdVar v)  = do iv <- instVar binding v
%                                   return $ StdVar iv
% instGVar binding (LstVar lv) = do ilv <- instLVar binding lv
%                                   return $ LstVar ilv
% \end{code}
%

\begin{code}
instVar :: Monad m => Binding -> Variable -> m Variable
instVar binding v
  = case lookupVarBind binding v of
      Nothing             ->  return v  -- maps to self !
      Just (BindVar v')   ->  return v'
      _  ->  fail "instVar: bound to term."
\end{code}

\newpage


Given $\bigoplus(p)\seqof{\lst l^1,\dots,\lst l^a}$, where $a > 1$%
\footnote{
Not sure there is a use-case for $a=1$.
There is definitely no case for $a=0$.
}.

Assume, w.l.o.g., $\beta
         = \setof{ \lst l^1
                   \mapsto
                   \seqof{g^1_1,\dots,g^1_n}
                 , \dots
                 , \lst l^a
                   \mapsto
                   \seqof{g^a_1,\dots, g^a_n}
                 }$

Note that all lists must be of the same length,
and at any list position $i$, the general variables $g^1_i, \dots, g^a_i$
are of the same type (std/list).

The instantiation is:
$$
 I\seqof{g^1_1,\dots,g^a_1}
 \oplus
 \dots
 \oplus
 I\seqof{g^1_i,\dots,g^a_i}
 \oplus
 \dots
 \oplus
 I\seqof{g^1_n,\dots,g^a_n}
$$
where
\begin{eqnarray*}
   I\seqof{v^1_i,\dots,v^a_i} &=& p(v^1_i,\dots,v^a_i)
\\ I\seqof{\lst l^1_i,\dots,\lst l^a_i} &=& \bigoplus(p)\seqof{\lst l^1_i,\dots,\lst l^a_i}
\end{eqnarray*}


So, here, we want to return
$$
\seqof{
 \seqof{g^1_1,\dots,g^a_1}
 ,
 \dots
 ,
 \seqof{g^1_i,\dots,g^a_i}
 ,
 \dots
 ,
 \seqof{g^1_n,\dots,g^a_n}
}
$$

\begin{code}
instIterLVS :: Monad m => Binding -> [ListVar] -> m [[LVarOrTerm]]
instIterLVS binding lvs
  = do lvtss <- sequence $ map (instTLGVar binding . LstVar) lvs
       let lvtss' = transpose lvtss
       checkAndGroup arity [] lvtss'
       -- fail "instIterLVS NYI"
  where
    arity = length lvs

checkAndGroup :: Monad m => Int -> [[LVarOrTerm]] -> [[LVarOrTerm]]
              -> m [[LVarOrTerm]]
checkAndGroup a sstvl [] = return $ reverse sstvl
checkAndGroup a sstvl (lvts:lvtss)
 | length lvts /= a  =  fail $ unlines
                        [ "instIterLVS: wrong arity, expected "++show a
                        , "lvts = " ++ trLstLVarOrTerm lvts
                        ]
 | null lvs  =  checkAndGroup a (map injTM ts:sstvl)  lvtss
 | null ts   =  checkAndGroup a (map injLV lvs:sstvl) lvtss
 | otherwise  =  fail $ unlines
                  [ "instIterLVS: mixed var types"
                  , "lvts = " ++ trLstLVarOrTerm lvts
                  ]
 where
   (lvs,ts) = lvtmSplit lvts
\end{code}


\newpage
\subsection{Side-Condition Instantiation}

Doing it again, with side-conditions.
\begin{code}
instantiateSC :: Monad m => Binding -> SideCond -> m SideCond
instantiateSC bind (ascs,fvs)
  = do ascss' <- sequence $ map (instantiateASC bind) ascs
       fvs' <- instVarSet bind fvs
       mkSideCond (concat ascss') fvs'
\end{code}

\begin{code}
instantiateASC :: Monad m => Binding -> AtmSideCond -> m [AtmSideCond]
\end{code}

\paragraph{Is a Pre-condition}~

\begin{code}
instantiateASC bind asc@(IsPre _)  =  instantiateASCvs bind S.empty asc
\end{code}

\paragraph{Has Variable-Set}~

\begin{code}
instantiateASC bind asc
  = case instVarSet bind $ fromJust $ ascVSet asc of
      But msgs -> fail $ unlines $ msgs
      Yes (vs') -> instantiateASCvs bind vs' asc
\end{code}

\paragraph{Has General Variable}~

\begin{code}
instantiateASCvs bind vs' asc
  = case ascGVar asc of
      StdVar v  -> instantiateASCvsv  bind vs' v  asc
      LstVar lv -> instantiateASCvslv bind vs' lv asc
\end{code}

\paragraph{Has Standard Variable}~

\begin{code}
instantiateASCvsv bind vs' v (Disjoint _ _)
  = instantiateDisjoint vs' $ instantiateVar bind v
instantiateASCvsv bind vs' v (Covers _ _)
  = instantiateCovers vs' $ instantiateVar bind v
instantiateASCvsv bind vs' v (IsPre _)
  = fail "instantiateASC IsPre NYI"
\end{code}

\paragraph{Has List-Variable}~

\begin{code}
instantiateASCvslv bind vs' lv (Disjoint _ _)
  = instantiateDisjoint vs' $ instantiateLstVar bind lv
instantiateASCvslv bind vs' lv (Covers _ _)
  = fail "instantiateASCvslv Covers NYI"
\end{code}
Next,
Dealing with each condition, now that everything is instantiated.
Assume below that
$\setof{x,y}$ are distinct identifiers for observation variables
and $\setof{S,T}$ are distinct identifiers for term-valued variables.

\subsubsection{Disjointedness}

\textbf{Wrong: trying to discharge the side-condition!}
\textit{
See examples below
}

\begin{eqnarray*}
  S \disj T_1 \cup T2 &=& S \disj T_1 \land S \disj T_2
\\ S_1 \cup S_2 \disj T &=& S_1 \disj T \land S_2 \disj T
\end{eqnarray*}

\begin{eqnarray*}
   \setof{x,S} \disj \setof{y,T} &?&
\\ \setof{x,S} \disj \setof{x,T} &&  \false
\\ \setof{x,S} \disj \setof{y,S} &\text{if}&  S=\emptyset
\\ \setof{x,S} \disj \setof{y,T}
   &\text{if}&
   S \disj \setof{y,T} ; T \disj \setof{x,S}
\\&=& y \notin S \land x \notin T \land S \disj T
\\ \setof{\lst x,S} \disj \setof{\lst x,T}
   &\text{if}&
   \lst x = \emptyset \land S \disj T
\\ \setof{x,\lst S} \disj \setof{y,\lst S} &\text{if}&  \lst S = \emptyset
\end{eqnarray*}
\begin{code}
instantiateDisjoint :: Monad m => VarSet -> VarSet -> m [AtmSideCond]
instantiateDisjoint dvs fvs
 | freeObs `disjoint` dvs = return $ map (mkD dvs) $ S.toList freeTVar
 | otherwise  =  fail $ unlines
                   [ "Obs. free-vars not disjoint"
                   , "dvs = " ++ trVSet dvs
                   , "fvs = " ++ trVSet fvs
                   ]
 where
   (freeObs,freeTVar) = S.partition isObsGVar fvs
   mkD vs gv = Disjoint gv vs
\end{code}

\newpage
\subsubsection{Covering}

\begin{eqnarray*}
   S \supseteq T_1 \cup T2 &=& S \supseteq T_1 \land S \supseteq T_2
\\ S_1 \cup S_2 \supseteq T &\neq& S_1 \supseteq T \land S_2 \supseteq T
\end{eqnarray*}


\begin{eqnarray*}
   \setof{x,S} \supseteq \setof{y,T} &?&
\\ \setof{x,S} \supseteq \setof{x,T} &\text{if}&  \setof{x,S} \supseteq T
\\ \setof{x,S} \supseteq \setof{y,S} &\text{if}&  y \in S
\\ \setof{x,S} \supseteq \setof{y,T}
   &\text{if}&
   y \in S \and \setof{x,S} \supseteq T
\\ \setof{\lst x,S} \supseteq \setof{\lst x,T}
   &\text{if}&
   \setof{\lst x,S} \supseteq T
\\ \setof{x,\lst S} \supseteq \setof{y,\lst S} &\text{if}& y \in \lst S
\end{eqnarray*}
\begin{code}
instantiateCovers :: Monad m => VarSet -> VarSet -> m [AtmSideCond]
instantiateCovers cvs fvs
 | freeObs `S.isSubsetOf` cvs = return $ map (mkC cvs) $ S.toList freeTVar
 | otherwise  =  fail $ unlines
                   [ "Obs. free-vars not covered"
                   , "cvs = " ++ trVSet cvs
                   , "fvs = " ++ trVSet fvs
                   ]
 where
   (freeObs,freeTVar) = S.partition isObsGVar fvs
   mkC vs gv = Covers gv vs
\end{code}


\subsubsection{Pre-Condition}

Not yet covered


\subsubsection{Side-condition Variable Instantiation}

Instantiate a (std./list)-variable either according to the binding,
or by itself if not bound:
\begin{code}
instantiateVar :: Binding -> Variable -> VarSet
instantiateVar bind v
  = case lookupVarBind bind v of
        Nothing            ->  S.singleton $ StdVar v
        Just (BindVar v)   ->  S.singleton $ StdVar v
        Just (BindTerm t)  ->  freeVars t

instantiateLstVar :: Binding -> ListVar -> VarSet
instantiateLstVar bind lv
  = case lookupLstBind bind lv of
      Nothing             ->  S.singleton $ LstVar lv
      Just (BindList vl)  ->  S.fromList vl
      Just (BindSet  vs)  ->  vs
      Just (BindTLVs tlvs)
       -> let (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
          in  (S.unions $ map freeVars ts)
              `S.union`
              (S.fromList $ map LstVar lvs)
\end{code}

\newpage
\subsubsection{Finding Unbound Replacement Variables}

\begin{code}
findUnboundVars :: Binding -> Term -> VarSet
findUnboundVars bind trm = mentionedVars trm  S.\\  mappedVars bind
\end{code}


\subsubsection{Collect Substitution List-Variable Pairings}

\begin{code}
termLVarPairings :: Term -> [(ListVar,ListVar)]
termLVarPairings (Sub _ tm s)     =  nub ( termLVarPairings tm
                                           ++ substLVarPairings s )
termLVarPairings (Cons _ _ ts)    =  nub $ concat $ map termLVarPairings ts
termLVarPairings (Bnd _ _ _ tm)  =  termLVarPairings tm
termLVarPairings (Lam _ _ _ tm)   =  termLVarPairings tm
termLVarPairings (Cls _ tm)       =  termLVarPairings tm
termLVarPairings _                =  []

substLVarPairings :: Substn -> [(ListVar,ListVar)]
substLVarPairings (LVarSub lvs) = S.toList lvs
\end{code}

Given that we can have substitutions of the form
$P[\lst y/\lst x][\lst e/\lst y]$
what we want is an relation saying
that $\setof{\lst e,\lst x,\lst y}$ are equivalent.
We can represent such a relation as a set of list-variable
sets.

\newpage
The following code is very general and should live elsewhere
\begin{code}
addToEquivClass :: Eq a => (a,a) -> [[a]] -> [[a]]
-- invariant, given eqvcs = [eqvc1,eqvc2,...]
--  z `elem` eqcvi ==> not( z `elem` eqcvj), for any j /= i
addToEquivClass (x,y) [] =  [nub[x,y]]
addToEquivClass (x,y) eqvcs
  = ([x,y] `union` hasX `union` hasY):noXY
  where
    (hasX,hasY,noXY) = findEquivClasses x y [] [] [] eqvcs

findEquivClasses
  :: Eq a  =>  a -> a       -- x and y
           ->  [a] -> [a]   -- accumulators for hasX, hasY
           ->  [[a]]        -- accumulator for noXY
           ->  [[a]]        -- equivalence classes under consideration
           ->  ([a],[a],[[a]])
findEquivClasses _ _ hasX hasY noXY [] = (hasX,hasY,noXY)
findEquivClasses x y hasX hasY noXY (eqvc:eqvcs)
  = checkX hasX hasY noXY
  where
    checkX hasX hasY noXY
      | x `elem` eqvc  =  checkY eqvc hasY noXY True
      | otherwise      =  checkY hasX hasY noXY False
    checkY hasX hasY noXY hadX
      | y `elem` eqvc  =  findEquivClasses x y hasX eqvc noXY eqvcs
      | hadX           =  findEquivClasses x y hasX hasY noXY eqvcs
      | otherwise      =  findEquivClasses x y hasX hasY (eqvc:noXY) eqvcs
\end{code}

Given a list of tuples, construct the equivalence classes:
\begin{code}
mkEquivClasses :: Eq a => [(a,a)] -> [[a]]
mkEquivClasses [] = []
mkEquivClasses (p:ps) = addToEquivClass p $ mkEquivClasses ps
\end{code}

Given equivalence classes,
which one, if any, does a value belong to?
\begin{code}
lookupEquivClasses :: Eq a => a -> [[a]] -> [a]
lookupEquivClasses x []  =  []
lookupEquivClasses x (eqvc:eqvcs)
 | x `elem` eqvc         =  eqvc \\ [x]
 | otherwise             =  lookupEquivClasses x eqvcs
\end{code}

\newpage


\textbf{
Function \texttt{mkFloatingBinding} needs
details regarding all substitution list-variable pairs
in order to produce valid bindings.
In particular, if an unbound substitution list-variable
is paired with a bound one, then the unknown one must be bound
to something of the same size as its bound partner, otherwise instantiation will
fail when it calls \texttt{substn}.
}
\begin{code}
mkFloatingBinding :: [VarTable] -> Binding -> [[ListVar]] -> VarSet -> Binding
mkFloatingBinding vts bind substEqv vs
  = qB emptyBinding $ S.toList vs
  where

    qB bind [] = bind
    qB bind ((StdVar v) :vl)  =  qB (qVB bind v)   vl
    qB bind ((LstVar lv):vl)  =  qB (qLVB bind lv) vl

    qVB bind v@(Vbl i vc vw)
      = case lookupVarTables vts v of
          UnknownVar  ->  fromJust $ bindVarToVar v (Vbl (fI i) vc vw) bind
          _           ->  fromJust $ bindVarToVar v v                  bind
      where qi = fI i

    qLVB bind lv@(LVbl v _ _)
      = case lookupLVarTables vts v of
          UnknownListVar  ->  qLVB' bind lv
          _               ->  fromJust $ bindLVarToSSelf lv bind

    qLVB' bind lv@(LVbl (Vbl i _ _) _ _)
      | null lvEquivs
          = fromJust
              $ bindLVarToVList lv [floatingLV lv i] bind
      | otherwise
         = case bindSizes of
             [] -> fromJust
                      $ bindLVarToVList lv
                          [floatingLV lv i] bind
             [0] -> fromJust $ bindLVarToVList lv [] bind
             [1] -> fromJust
                      $ bindLVarToVList lv
                          [floatingLV lv i] bind
             [n] -> fromJust
                      $ bindLVarToVList lv
                          (map (floatingLV lv . fIn i) [1..n]) bind
             bs -> error $ unlines
                    ["mkFloatingBinding : equiv class has multiple sizes"
                    ,"bs="++show bs
                    ,"lv="++show lv
                    ]
      where
        lvEquivs = lookupEquivClasses lv substEqv
        bindSizes = equivBindingsSizes bind lvEquivs
        floatingLV lv@(LVbl (Vbl _ vc vw) is js) i
                 = LstVar (LVbl (Vbl (fI i) vc vw) is js)
\end{code}

Look up cardinalities of bindings of equivalences.
\textbf{Issue: what if their cardinality varies?}
\begin{code}
equivBindingsSizes :: Binding -> [ListVar] -> [Int]
equivBindingsSizes bind [] = []
equivBindingsSizes bind (lv:lvs)
  = case lookupLstBind bind lv of
       Nothing  ->  equivBindingsSizes bind lvs
       Just (BindList vl)  ->  nub (length vl : equivBindingsSizes bind lvs)
       Just (BindSet vs)   ->  nub (S.size vs : equivBindingsSizes bind lvs)
       Just (BindTLVs tlvl)
         | null tl    ->  nub (length vl : equivBindingsSizes bind lvs)
         | otherwise  ->  error $ unlines
                           ["equivBindingsSizes: cannot handle BX with terms"
                           ,"tlvl="++show tlvl
                           ,"bind="++trBinding bind
                           ]
         where (tl,vl) = (tmsOf tlvl, lvsOf tlvl)
\end{code}
Another issue, what if some are unbound? Ignore for now.

\subsubsection{Floating Instantiation}

\begin{code}
autoInstantiate :: Monad m => [VarTable] -> Binding -> Term -> m (Binding,Term)
autoInstantiate vts bind trm
 = do trm' <- instantiate abind trm
      return (abind, trm')
 where
   unbound  =  findUnboundVars bind trm
   lvpairs  =  termLVarPairings trm
   substEquiv = mkEquivClasses lvpairs
   qbind    =  mkFloatingBinding vts bind substEquiv unbound
   abind    =  mergeBindings bind qbind
\end{code}
