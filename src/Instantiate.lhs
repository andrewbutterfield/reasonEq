\chapter{Instantiate}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Instantiate
( InsContext(..), mkInsCtxt
, instantiate
, instVarSet
, instTVSC
, instantiateSC
) where
import Data.Maybe
-- import Data.Either (lefts,rights)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M
import Data.List

import Utilities
import Control
import LexBase
import Variables
import AST
import SideCond
import Binding
import Matching
import FreeVars
import VarData
import TestRendering

import Debugger
\end{code}

\section{Introduction}

We take a pattern term and a binding,
along with relevant context information,
and produce a re-constructed candidate term,
provided every variable in the pattern is also in the binding.
If $\beta$ is a binding, and $t$ is a term,
we use $\beta.t$ to denote the result of this instantiation.
Given a variable $v$ we use $\beta(v)$ to denote a binding lookup.

\begin{eqnarray*}
   \beta.\kk k &=& \kk k
\\ \beta.(\vv v) &=& \beta(v)
\\ \beta.(\cc n {ts}) &=& \cc n {(\beta^*.ts)}
\\ \beta.(\bb n {v^+} t) &=& \bb n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ll n {v^+} t) &=& \ll n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ss t {v^n} {t^n}) &=& \ss {\beta.t} {\beta^*(v^n)} {\beta^*.t^n}
\\ \beta.(\xx n t) &=& \xx {n} {\beta.t}
\\ \beta.(\tt \tau) &=& \tt \tau
\\ \beta.(\bigoplus(p)\seqof{\lst l^1,\dots,\lst l^a})
   &=& I\seqof{g^1_1,\dots,g^a_1}
       \oplus\dots\oplus
       I\seqof{g^1_i,\dots,g^a_i}
       \oplus\dots\oplus
       I\seqof{g^1_n,\dots,g^a_n}
\\ \where
\\ \beta &=& \beta' \oplus
             \setof{ \lst l^1 \mapsto \seqof{g^1_1,\dots,g^1_n}
                   , \dots
                   , \lst l^a \mapsto \seqof{g^a_1,\dots, g^a_n}
                   }
\\ I\seqof{v^1_i,\dots,v^a_i} &=& p(v^1_i,\dots,v^a_i)
\\ I\seqof{\lst l^1_i,\dots,\lst l^a_i}
   &=& \bigoplus(p)\seqof{\lst l^1_i,\dots,\lst l^a_i}
\end{eqnarray*}

\subsection{Instantiation Contexts}

All instantiations need a context argument that describes the following
aspects of the current state of a proof:
\begin{itemize}
  \item Set of known dynamic observables
  \item Side-Conditions
\end{itemize}
\begin{code}
data InsContext
  =  ICtxt  { icDV :: VarSet
            , icSC :: SideCond
            }
  deriving Show  

mkInsCtxt :: [VarTable] -> SideCond -> InsContext
mkInsCtxt vts sc = ICtxt (getDynamicObservables vts) sc
\end{code}



\newpage
\section{Instantiating Term with a (Total) Binding}

Here we require every free variable in the term to be also in the binding.
\begin{code}
instantiate :: MonadFail m => InsContext -> Binding -> Term -> m Term
\end{code}

\subsection{Instantiating Values and Types}

\begin{eqnarray*}
   \beta.\kk k &=& \kk k
\\ \beta.\tt \tau &=& \tt \tau
\end{eqnarray*}
\begin{code}
instantiate _ binding v@(Val _ _)  =  return v
instantiate _ binding t@(Typ _)    =  return t
\end{code}

\subsection{Instantiating Variables}

\begin{eqnarray*}
   \beta.(\vv v) &=& \beta(v)
\end{eqnarray*}
Here we do not expect any bindings to list-variables.
\begin{code}
instantiate insctxt binding vt@(Var tk v)
  = case lookupVarBind binding v of
      Just (BindVar v')   ->  var tk v'
      Just (BindTerm t')  ->  return t'
      Just (BindLVar lv)  ->  fail $ unlines
                                     [ "instantiate: naked list-variable!"]
      Nothing             ->  fail $ unlines
                                     [ "instantiate: variable not found"
                                     , "var = " ++ trVar v
                                     , "bind = " ++ trBinding binding
                                     ]
\end{code}

\newpage

\subsection{Instantiating Cons}

With Cons nodes we have two possibilities.
The first is the general case where we have a list of terms as usual:
\begin{eqnarray*}
   \beta.(\cc n {ts}) &=& \cc n {(\beta^*.ts)}
\end{eqnarray*}
The second is where all the terms are variables,
all of them are mapped by $\beta$ to list-variables,
and there is a binding from \itop\ to a variable.
This results in a one-place iteration:
\begin{eqnarray*}
   \beta.(\cc n {vs}) &=& \ii {\beta(\itop)} n {(\beta^*.vs)}
   \quad \text{ provided }  \itop \in \beta \land \forall_i \cdot \beta.v_i = \lst x_i, 
\end{eqnarray*}
\begin{code}
instantiate insctxt binding (Cons tk sb n ts)
  | all isVar ts && all isBLVar bts && have_itop
      = return $ (Iter tk sb (jId "and") sb n) $ map theBLVar bts
  | otherwise 
      = fmap (Cons tk sb n) $ sequence $ map (instantiate insctxt binding) ts
  where 
    bts = catMaybes $ map (lookupVarBind binding . theVar) ts
    isBLVar (BindLVar _) = True
    isBLVar _            = False
    theBLVar (BindLVar lv)  =  lv
    itopv = Vbl itop ObsV Static
    mbitop = lookupVarBind binding itopv
    (have_itop,the_itop) = get_itop mbitop
    get_itop (Just (BindVar (Vbl i _ _))) = (True,i)
    get_itop _ = (False,itop)
\end{code}

\subsection{Instantiating Quantifiers}

\begin{eqnarray*}
   \beta.(\bb n {v^+} t) &=& \bb n {\beta^*.v^+} {\beta.t}
\\ \beta.(\ll n {v^+} t) &=& \ll n {\beta^*.v^+} {\beta.t}
\\ \beta.(\xx n t)       &=& \xx {n} {\beta.t}
\end{eqnarray*}
\begin{code}
instantiate insctxt binding (Bnd tk n vs tm)
  = do vs' <- fmap theFreeVars $ instVarSet insctxt binding vs
       tm' <- instantiate insctxt binding tm
       bnd tk n vs' tm'
instantiate insctxt binding (Lam tk n vl tm)
  = do vl' <- instVarList insctxt binding vl
       tm' <- instantiate insctxt binding tm
       lam tk n vl' tm'
instantiate insctxt binding (Cls n tm)
  = do tm' <- instantiate insctxt binding tm
       return $ Cls n tm'
\end{code}

\newpage
\subsection{Instantiating Substitutions}

We need to keep in mind that we use the substitution form to represent assignment. 
If the term is a predicate variable ``$:=$'',
then we have an assignment.
\begin{eqnarray*}
   \beta.(\ss {(:=)} {v^n} {t^n}) &=& \ss {(:=)} {\beta^*(v^n)} {\beta^*.t^n}
\\ \beta.(\ss t {v^n} {t^n}) &=& \ss {\beta.t} {\beta^*(v^n)} {\beta^*.t^n}
\end{eqnarray*}
\begin{code}
instantiate insctxt binding (Sub tk tm s)
  = do s' <- instSub insctxt binding s
       tm' <- if isAssignment tm
              then return tm
              else instantiate insctxt binding tm
       return $ Sub tk tm' s'
\end{code}

\subsection{Instantiating Iteration}

\begin{eqnarray*}
   \beta.(\ii \bigoplus p {\seqof{\lst l^1,\dots,\lst l^a}})
   &=& I\seqof{g^1_1,\dots,g^a_1}
       \oplus\dots\oplus
       I\seqof{g^1_i,\dots,g^a_i}
       \oplus\dots\oplus
       I\seqof{g^1_n,\dots,g^a_n}
\\ \where
\\ \beta &=& \beta' \oplus
             \setof{ \lst l^1 \mapsto \seqof{g^1_1,\dots,g^1_n}
                   , \dots
                   , \lst l^a \mapsto \seqof{g^a_1,\dots, g^a_n}
                   }
\\ I\seqof{v^1_i,\dots,v^a_i} &=& p(v^1_i,\dots,v^a_i)
\\ I\seqof{\lst l^1_i,\dots,\lst l^a_i}
   &=& \ii \bigoplus p {\seqof{\lst l^1_i,\dots,\lst l^a_i}}
\end{eqnarray*}
Note that all lists must be of the same length,
and at any list position $i$, the general variables $g^1_i, \dots, g^a_i$
are of the same type (std/list).
\begin{code}
instantiate insctxt binding (Iter tk sa na si ni lvs)
  = do lvtss <- instIterLVS insctxt binding lvs
       -- all have same non-zero length
       -- have the same kind of object (list-var/term)
       case lvtss of
         [lvts]  ->  return $ mkI lvts
         _       ->  return $ Cons tk sa na $ map mkI lvtss
  where
    mkI :: [LVarOrTerm] -> Term
    mkI lvts@(Right _:_) = Cons tk si ni $ tmsOf lvts
    mkI lvts@(Left  _:_) = Iter tk sa na si ni $ lvsOf lvts
\end{code}

\newpage

\section{Helper Functions}

\subsection{Iteration Stuff}

So, below, we want to return
$
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
$
\begin{code}
instIterLVS :: MonadFail m => InsContext
            -> Binding -> [ListVar] -> m [[LVarOrTerm]]
instIterLVS insctxt binding lvs
  = do lvtss <- sequence $ map (instTLGVar insctxt binding) lvs
       let lvtss' = transpose lvtss
       checkAndGroup arity [] lvtss'
       -- fail "instIterLVS NYI"
  where
    arity = length lvs
\end{code}

\begin{code}
instTLGVar :: MonadFail m => InsContext -> Binding -> ListVar -> m [LVarOrTerm]
instTLGVar insctxt binding lv
  = case lookupLstBind binding lv of
      Nothing              ->  return $ [injLV lv]  -- maps to self !
      Just (BindList vl')  ->  return $ map injGV vl'
      Just (BindTLVs tlvs) ->  return tlvs
      _ -> fail "instTLGVar: bound to sets."

injV :: Variable -> LVarOrTerm
injV = injTM . varAsTerm
injGV :: GenVar -> LVarOrTerm
injGV (StdVar v)   =  injV v
injGV (LstVar lv)  =  injLV lv
\end{code}

\begin{code}
checkAndGroup :: MonadFail m => Int -> [[LVarOrTerm]] -> [[LVarOrTerm]]
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
\subsection{Instantiating Substitutions}

The \texttt{Substn} constructor is used to represent substitutions,
and assignments.
While this obviously requires separate treatment for the two cases,
it turns out that the pair-lists in the \texttt{Substn} part
are processed the same way.

\begin{code}
instSub :: MonadFail m => InsContext -> Binding -> Substn -> m Substn
instSub insctxt binding (Substn ts lvs)
  = do ts'  <- instZip (instStdVar insctxt binding)
                       (instantiate insctxt binding) (S.toList ts)
       ts'' <- sequence $ map getTheTargetVar ts'
       vtlvss' <- instZip (instLLVar insctxt binding) (instLLVar insctxt binding)
                          (S.toList lvs)
       let (lvtlvss,rvtlvss) = unzip vtlvss'
       let (vtts,lvts) = unzip lvtlvss
       let (vtrs,lvrs) = unzip rvtlvss
       let lvs' = zip (concat lvts) (concat lvrs)
       let ts''' = zip (concat vtts) (concat vtrs)
       ts4 <- sequence $ map getTheTermVar ts'''
       substn (ts''++ts4) lvs'

instZip inst1 inst2 pairs
  = sequence $ map (instPair inst1 inst2) pairs
  where
    instPair inst1 inst2 (thing1,thing2)
      = do thing1' <- inst1 thing1
           thing2' <- inst2 thing2
           return (thing1',thing2')

getTheTargetVar :: MonadFail m => (FreeVars,Term) -> m (Variable,Term)
getTheTargetVar (fvs,tm)
  = do v' <- getTheVar fvs
       return (v',tm)

getTheTermVar :: MonadFail m => (Term,Term) -> m (Variable,Term)
getTheTermVar (Var _ v,t)  = return (v,t)
getTheTermVar (bt,_)       = fail ("getTheTermVar: expected Var, not "++show bt)

getTheVar :: MonadFail m => FreeVars -> m Variable
getTheVar fvs@(vs,diffs)
  = case S.toList vs of
      [StdVar v] | null diffs  ->  return v
      _  -> fail ("getTheVar: expected a single variable, not "++show fvs)
\end{code}

\newpage
This code is used for list-var in substitutions only.
\begin{code}
instLLVar :: MonadFail m => InsContext
          -> Binding -> ListVar -> m ([Term],[ListVar])
instLLVar insctxt binding lv
  = case lookupLstBind binding lv of
      Just (BindList vl')  ->  do lvs <- fromGVarToLVar vl'
                                  return ([],lvs)
      Just (BindSet  vs')  ->  do lvs <- fromGVarToLVar $ S.toList vs'
                                  return ([],lvs)
      Just (BindTLVs tlvs) ->  return (tmsOf tlvs, lvsOf tlvs)
      Nothing              ->  fail $ unlines
                                     [ "instLLVar: l-var not found"
                                     , "l-var = " ++ trLVar lv
                                     , "bind = " ++ trBinding binding
                                     ]

fromGVarToLVar :: MonadFail m => VarList -> m [ListVar]
fromGVarToLVar [] = return []
fromGVarToLVar (StdVar v:vl)
 = fail ("fromGVarToLVar: Std variable found - " ++ show v)
fromGVarToLVar (LstVar lv:vl)
  = do lvs <- fromGVarToLVar vl
       return (lv:lvs)
\end{code}

\newpage
\subsubsection{Instantiate Variable Collections}

When we use a binding to instantiate variables and variable-sets/lists,
we need to keep in mind that some variables might be bound to terms,
in which case we need to return the free-variables for that term.
This is why all the functions here return \texttt{FreeVars} 
rather than \texttt{VarSet}.
The following code needs updating to handle free-variables properly.

Let $g$ denote a general variable, and $G$ a set of same.
\begin{eqnarray*}
   \beta.G &=& \textstyle \bigcup_{g \in G} \beta.g
\end{eqnarray*}
\begin{code}
instVarSet :: MonadFail m => InsContext -> Binding -> VarSet -> m FreeVars
instVarSet insctxt binding vs
  = do fvss <- sequence $ map (instGVar insctxt binding) $ S.toList vs
       return $ mrgFreeVarList fvss
\end{code}



For a general variable:
\begin{eqnarray*}
   \beta.v &=& \beta(v)
\\ \beta.T &=& \fv(\beta(T))
\\ \beta.\lst g &=& \beta(\lst g)
\end{eqnarray*}
\begin{code}
instGVar :: MonadFail m => InsContext -> Binding -> GenVar -> m FreeVars
instGVar insctxt binding (StdVar v)  = instStdVar insctxt binding v
instGVar insctxt binding (LstVar lv) = instLstVar insctxt binding lv
\end{code}

\begin{code}
instStdVar :: MonadFail m => InsContext -> Binding -> Variable -> m FreeVars
instStdVar insctxt binding v
  = case lookupVarBind binding v of
      Nothing             ->  return $ single v  -- maps to self !
      Just (BindVar v')   ->  return $ single v'
      Just (BindTerm t')  ->  return $ freeVars (icSC insctxt) t'
      _  ->  fail "instStdVar: bound to identifier."
  where single v = (S.singleton (StdVar v),[])
\end{code}

\begin{code}
instLstVar :: MonadFail m => InsContext -> Binding -> ListVar -> m FreeVars
instLstVar insctxt binding lv
  = case lookupLstBind binding lv of
      Nothing              ->  return $ single lv  -- maps to self !
      Just (BindList vl')  ->  return (S.fromList vl',[])
      Just (BindSet  vs')  ->  return (vs',[])
      Just (BindTLVs tlvs)
        | all isVar ts  -> return ( S.fromList
                                    $ ( map (StdVar . theVar) ts)
                                        ++ (map LstVar lvs)
                                  , [] )
        | otherwise     ->  fail "instLstVar: bound to non-variable terms."
        where (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
  where
    single lv = (S.singleton (LstVar lv),[])
\end{code}



With $L$ a list of general variables
\begin{eqnarray*}
   \beta.L &=& \mathsf{concat}_{g \in L} \beta.g
\end{eqnarray*}
\begin{code}
instVarList :: MonadFail m => InsContext -> Binding -> VarList -> m VarList
instVarList insctxt binding vl
  = fmap concat $ sequence $ map (instLGVar insctxt binding) vl
\end{code}
We do not expect these to map to terms.
\begin{code}
instLGVar :: MonadFail m => InsContext -> Binding -> GenVar -> m VarList
instLGVar insctxt binding (StdVar v)
  =  do fvs' <- instStdVar insctxt binding v
        v' <- getTheVar fvs'
        return [StdVar v]
instLGVar insctxt binding gv@(LstVar lv)
  = case lookupLstBind binding lv of
      Nothing              ->  return [gv]  -- maps to self !
      Just (BindList vl')  ->  return vl'
      _ -> fail "instLGVar: bound to sets or terms."
\end{code}

\newpage
\section{Side-Condition Instantiation (Total)}

Doing it again, with side-conditions.
Basically we drill down to the atomic side-conditions,
instantiate and simplify those,
and merge together.

\begin{code}
instantiateSC :: MonadFail m => InsContext -> Binding -> SideCond -> m SideCond
\end{code}
side-conditions:
\begin{eqnarray*}
   \beta.(D \disj  T) &=& \beta.D \disj \fv(\beta(T))
\\ \beta.(C \supseteq T)  &=& \beta.C \supseteq \fv(\beta(T))
\\ \beta(\ispre \supseteq T) &=& \ispre \supseteq \fv(\beta(T))
\\ \beta(\fresh F) &=& \fresh \beta(F)
\end{eqnarray*}
\begin{code}
instantiateSC insctxt bind (tvscs,freshvs)
  = do tvscss' <- sequence $ map (instantiateTVSC insctxt bind) tvscs
       freshvs' <- instVarSet insctxt bind freshvs
       mkSideCond (icDV insctxt) (concat tvscss') $ theFreeVars freshvs'
\end{code}
For atomic side-conditions:
\begin{eqnarray*}
   \beta.(D \disj  T) &=& \beta.D \disj \fv(\beta(T))
\\ \beta.(C \supseteq T)  &=& \beta.C \supseteq \fv(\beta(T))
\\ \beta(\ispre \supseteq T) &=& \ispre \supseteq \fv(\beta(T))
\end{eqnarray*}
Consider this example:
\begin{description}
\item[Law] $P[\lst e/\lst x] = P, \qquad \lst x \notin P$
\item[Goal] $R[O_m/O'])[O'/O_m], \qquad O',O \supseteq R$.
\item[Bind] 
   $\beta
    =
    \setof{
      P \mapsto R[O_m/O']
      ,
      \lst e \mapsto \seqof{O'}
      ,
      \lst x \mapsto \seqof{O_m}
    }
   $
\item[FV(Sub)]
   $\fv(\ss t {v^n} {t^n})
      \defs
      (\fv(t)\setminus{v^m})\cup \bigcup_{s \in t^m}\fv(s)
       \textbf{~where~}  v^m = v^n \cap \fv(t)
   $
\end{description}
The following should fail as $\lst x (O_m)$ is in $P (R[O_m/O'])$.
\begin{eqnarray*}
\lefteqn{\beta(\lst x \disj P)}
\\ &=&  \beta(\lst x) \disj \fv(\beta(P))
\\ &=& \seqof{O_m} \disj \fv(R[O_m/O'])
\\ &=&  \seqof{O_m} \disj (\fv(R)\setminus \setof{O'}) \cup \setof{O_m}
\\ &=&  \seqof{O_m} \disj (\setof{O,O'}\setminus \setof{O'}) \cup \setof{O_m}
        \qquad \text{~uses~} O',O \supseteq R
\\ &=&  \seqof{O_m} \disj (\setof{O} \cup \setof{O_m})
\\ &=&  \seqof{O_m} \disj \setof{O,O_m}
\\ &=&  \false
\end{eqnarray*}

Now consider another example (UTCP theory):
\begin{description}
\item[Static Vars (not in $O,O'$.)]
   $E_i, R_i, N_i$.
\item[Known Vars] $O = \setof{s,ls}$.
\item[Law] $P;Q = \exists O_0 \bullet P[O_0/O'] \land Q[O_0/O], 
\qquad O,O' \supseteq_a P; O,O' \supseteq_a Q; \fresh O_0$
\item[Goal] $(E_1 \subseteq ls \land a \land ls'=(ls\setminus R_1)\cup N_1)
             ;
             (E_1 \subseteq ls \land a \land ls'=(ls\setminus R_1)\cup N_1) 
             \qquad O',O \supseteq a,b$
\item[Bind] 
   $\beta
    =
    \setof{
      P \mapsto (E_1 \subseteq ls \land a \land ls'=(ls\setminus R_1)\cup N_1)
      ,
      Q \mapsto (E_2 \subseteq ls \land b \land ls'=(ls\setminus R_2)\cup N_2)
      ,
      0 \mapsto 0
      ,
      O \mapsto \seqof{O}
    }
   $
\end{description}
The following should succeed because $E_i,R_i,N_i$ are not in $O$,
while $ls,ls'$ and $a$ and $b$ are covered by $O,O'$.
We start by processing the match predicate:
\begin{eqnarray*}
\lefteqn{\beta(\exists O_0 \bullet P[O_0/O'] \land Q[O_0/O])}
\\ &=& \exists O_0 \bullet \beta(P[O_0/O']) \land \beta(Q[O_0/O])
\\ &=& \exists O_0 \bullet \beta(P)[O_0/O'] \land \beta(Q)[O_0/O]
       \qquad O,0 \mapsto O,0
\\ &=& \exists O_0 \bullet 
       (E_1 \subseteq ls \land a \land ls'=(ls\setminus R_1)\cup N_1)[O_0/O'] 
       \land 
       (E_2 \subseteq ls \land b \land ls'=(ls\setminus R_2)\cup N_2)[O_0/O]
\\ &=& \exists O_0 \bullet 
       (E_1 \subseteq ls)[O_0/O'] \land 
       a[O_0/O'] \land 
       (ls'=(ls\setminus R_1)\cup N_1)[O_0/O'] 
       \land {}
\\ & & \phantom{\exists O_0 \bullet {}}
      (E_2 \subseteq ls)[O_0/O] \land 
      b[O_0/O] \land 
      (ls'=(ls\setminus R_2)\cup N_2)[O_0/O] 
\\ &=& \exists O_0 \bullet 
       (E_1 \subseteq ls) \land 
       a[O_0/O'] \land 
       (ls_0=(ls\setminus R_1)\cup N_1)[O_0/O'] 
       \land {} \qquad \text{uses } O=\setof{s,ls}, \dots
\\ & & \phantom{\exists O_0 \bullet {}}
      (E_2 \subseteq ls_0) \land 
      b[O_0/O] \land 
      (ls'=(ls_0\setminus R_2)\cup N_2)
\end{eqnarray*}
Now, the law side-condition:
\begin{eqnarray*}
\lefteqn{\beta(O,O' \supseteq_a P \land  O,O' \supseteq_a Q \land \fresh O_0)}
\\ &=& \beta(O,O' \supseteq_a P) \land  
       \beta(O,O' \supseteq_a Q) \land \beta(\fresh O_0)
\\ &=& O,O' \supseteq_a \beta(P) \land  
       O,O' \supseteq_a \beta(Q) \land \fresh O_0
\\ &=& O,O' \supseteq 
           \dfv(E_1 \subseteq ls \land a \land ls'=(ls\setminus R_1)\cup N_1)) 
           \land  {} 
\\ & & O,O' \supseteq 
           \dfv(E_2 \subseteq ls \land b \land ls'=(ls\setminus R_2)\cup N_2)
           \land \fresh O_0
\\ &=& O,O' \supseteq \setof{ls,ls'} \cup \fv(a) 
       \land  
       O,O' \supseteq \setof{ls,ls'} \cup \fv(b)
\\ &=& \true, \qquad \text{uses } \fv(a),\fv(b) \subseteq O,O'
\end{eqnarray*}
We define dynamic free variables ($\dfv$) as:
\begin{eqnarray*}
  \dfv &:& T \fun \Set V
\\ \dfv(t) &\defs& filter(isDynamic,\fv(t)) 
\end{eqnarray*}

\begin{code}
instantiateTVSC :: MonadFail m => InsContext
               -> Binding -> TVarSideConds -> m [TVarSideConds]
instantiateTVSC insctxt bind tvsc
  = do (vsDC,diffs) <- instVarSet insctxt bind $ tvscVSet tvsc
       if null diffs
         then instTVSC insctxt vsDC fvsT tvsc
         else fail "instantiateTVSC: explicit diffs in var-set not handled."
  where
     fvsT = instantiateGVar insctxt bind $ termVar tvsc
\end{code}

\begin{code}
instTVSC :: MonadFail m => InsContext
               -> VarSet -> FreeVars -> TVarSideConds -> m [TVarSideConds]
instTVSC insctxt vsDC fvT (TVSC _ vsD mvsC mvsCd)   
  = do  tvscsD <- instDisjoint insctxt vsD   fvT
        tvscsC <- instCovers   insctxt mvsC  fvT
        tvscCd <- instDynCvg   insctxt mvsCd fvT 
        return (tvscsD++tvscsC++tvscCd)
\end{code}


\newpage
\subsection{Disjointedness}

\begin{eqnarray*}
   \beta.(D \disj  T) &=& \beta.D \disj \fv(\beta(T))
\\ &=& \beta.D \disj (F \cup \{e_i\setminus B_i\}_{i \in 1\dots N})
\\ &=& \beta.D \disj F \land \{\beta.D \disj (e_i\setminus B_i)\}_{i \in 1\dots N}
\\ &=& \beta.D \disj F \land \{(\beta.D\setminus B_i) \disj e_i\}_{i \in 1\dots N}
\end{eqnarray*}
where $\fv(\beta(T)) = F \cup \{e_i\setminus B_i\}_{i \in 1\dots N}$,
$F \disj e_i$, $F \disj B_i$.
\begin{code}
instDisjoint :: MonadFail m 
             => InsContext -> VarSet -> FreeVars -> m [TVarSideConds]
instDisjoint insctxt vsD (fF,vLessBs)
  =  return (tvsc1s ++ tvsc2s)
  where
    tvsc1s = map (mkDisj vsD) $ S.toList fF
    mkDisj vsD gv = gv `disjfrom` vsD
    tvsc2s = map (f2 vsD) vLessBs
    f2 vsD (evF,vsB) = mkDisj (vsD S.\\ vsB) evF
\end{code}

\subsection{Covering}


The general case, 
where $\fv(\beta(T)) = F \cup \{F_i\setminus B_i\}_{i \in 1\dots N}$,
$F \disj F_i$, $F \disj B_i$:
\begin{eqnarray*}
   \beta.(C \supseteq T)
   &=& \beta.C \supseteq \fv(\beta(T))
\\ &=& \beta.C \supseteq (F \cup \{e_i\setminus B_i\})
\\ &=& \beta.C \supseteq F \land \{\beta.C \supseteq (e_i\setminus B_i)\}
\\ &=& \beta.C \supseteq F \land \{(\beta.C \cup B_i) \supseteq e_i\}
\end{eqnarray*}

\begin{code}
instCovers :: MonadFail m 
           => InsContext -> (Maybe VarSet) -> FreeVars 
           -> m [TVarSideConds]
instCovers insctxt Nothing    (fF,vLessBs)  =  return []
instCovers insctxt (Just vsC) (fF,vLessBs)  =  return (tvsc1s ++ tvsc2s)
  where
    tvsc1s = map (mkCovers vsC) (S.toList fF)
    mkCovers vsC gv = gv `coveredby` vsC
    tvsc2s = map (f2 vsC) vLessBs
    f2 vsC (evF,vsB) = mkCovers (vsC `S.union` vsB) evF
\end{code}

\newpage
\subsection{Dynamic Coverage}

The general case, 
where $\fv(\beta(T)) = F \cup \{F_i\setminus B_i\}_{i \in 1\dots N}$,
$F \disj F_i$, $F \disj B_i$:

We assume here that $D$ covers all dynamic variables.
\begin{eqnarray*}
   \beta.(C \supseteq_a T)
   &=& \beta.C \supseteq \dfv(\beta(T))
\\ &=& \beta.C \supseteq (\fv(\beta(T)) \mid_D)
\\ &=& \beta.C \supseteq (F \cup \{e_i\setminus B_i\})  \mid_D
\\ &=& \beta.C \supseteq (F  \mid_D \cup \{e_i\setminus B_i\} \mid_D) 
\\ &=& \beta.C \supseteq (F  \mid_D \cup \{(e_i \mid_D)\setminus B_i\} ) 
\\ &=& \beta.C \supseteq (F  \mid_D \cup \{(e_i \cap D)\setminus B_i\} ) 
\\ &=& \beta.C \supseteq F \mid_D 
       \land \{\beta.C \supseteq ((e_i \cap D)\setminus B_i)\} 
\\ &=& \beta.C \supseteq F \mid_D 
       \land \{e_i \in \beta.C \cond{e_i \in D \land e_i \notin B_i} \true \} 
\end{eqnarray*}
We include $e_i$ if $e_i \in D \land e_i \notin B_i$.


\begin{code}
instDynCvg :: MonadFail m 
           => InsContext -> (Maybe VarSet) -> FreeVars 
           -> m [TVarSideConds]
instDynCvg insctxt Nothing    (fF,vLessBs)  =  return []
instDynCvg insctxt (Just vsCd) (fF,vLessBs)  =  return (tvsc1s ++ tvsc2s)
  where
    restrict2 vS vR
      | S.null vR  =  vS
      | otherwise  =  vS `S.intersection` vR 
    mkDynCovers vs gv = gv `dyncovered` vs
    vsD = icDV insctxt
    fFD = fF `restrict2` vsD
    isIn vsD (ev,_) = ev `S.member` vsD
    vDLessBs = filter (isIn vsD) vLessBs
    isSeparate (ev,vsB) = not ( ev `S.member` vsB)
    vDNotInBs = filter isSeparate vDLessBs
    f2 vs (evFD,vsB) = mkDynCovers vs evFD
    tvsc1s = map (mkDynCovers vsCd) (S.toList fFD)
    tvsc2s = map (f2 vsCd) vDNotInBs
\end{code}

\newpage
\subsection{Side-condition Variable Instantiation}

Instantiate a (std./list)-variable either according to the binding,
or by itself if not bound:
\begin{code}
instantiateGVar :: InsContext -> Binding -> GenVar -> FreeVars
instantiateGVar insctxt bind (StdVar v)   =  instantiateVar  insctxt bind v
instantiateGVar insctxt bind (LstVar lv)  =  instantiateLstVar insctxt bind lv
\end{code}

\begin{eqnarray*}
   \beta(v) &=& v, \qquad  v \notin \beta
\\ \beta(v) &=& \beta.v, \qquad \mbox{if $\beta.v$ is an variable}
\\ \beta(v) &=& \fv_{sc}(\beta.v), \quad \mbox{if $\beta.v$ is a term}
\end{eqnarray*}
\begin{code}
instantiateVar :: InsContext -> Binding -> Variable -> FreeVars
instantiateVar insctxt bind v
  = case lookupVarBind bind v of
        Nothing            ->  (S.singleton $ StdVar v,[])
        Just (BindVar v')  ->  (S.singleton $ StdVar v',[])
        Just (BindTerm t)  ->  deduceFreeVars insctxt t
\end{code}
We note here that \texttt{FreeVars} represents the following structure:
$$ 
(F,D)
=
(F,\setof{(\dots,(e_i,B_i),\dots)})
 = 
( \setof{\dots,v,\dots}
, \setof{\dots,( e , \setof{\dots,x,\dots} ),\dots}
)
$$
where $v$ is any general variable, 
$e$ are non. obs. variables that don't occur in the $F$,
and $x$ are obs. vars. or list-vars.
It represents the variable-set: $F \cup \bigcup_i (e_i\setminus B_i)$
\begin{eqnarray*}
   \fv_{(tvscs,\_)}(t) 
   &=& 
   \bigcup_{v \in \pi_1\fv(t)} \scvarexp_{tvscs}(v)
   \cup
   \bigcup_{(e,B) \in \pi_2\fv(t)} \scdiffexp_{tvscs}(e,B)
\end{eqnarray*}
\begin{code}
deduceFreeVars :: InsContext -> Term -> FreeVars
deduceFreeVars insctxt t 
  = mrgFreeVarList 
      ( map (scVarExpand sc) (S.toList fF)
        ++
        map (scDiffExpand sc) dD )
  where
     sc = icSC insctxt
     (fF,dD) = freeVars sc t
\end{code}

\begin{eqnarray*}
   \scvarexp_{sc}(v) &=& \setof v, \qquad v \text{ is obs. var.}
\\ \scvarexp_{(tvscs,\_)}(e) 
   &=& \tvscsvarexp(e,tvscs(e)) \cond{e \in tvscs} \setof e
\end{eqnarray*}
\begin{code}
scVarExpand :: SideCond -> GenVar -> FreeVars
scVarExpand _ v@(StdVar (Vbl _ ObsV _)) = injVarSet $ S.singleton v
scVarExpand sc gv 
  = case findAllGenVar gv sc of
      []    ->  injVarSet $ S.singleton gv
      tvscs  ->  tvscsVarExpand gv tvscs
\end{code}

\newpage

For any given variable, we can end up with one of these possibilities: 
disjoint ($v \disj D$), covered ($C \supseteq v$),
dynamic coverage ($Cd \supseteq_a v$),  
or a mix of the cases with $C$ and $Cd$ disjoint from $D$.
\begin{eqnarray*}
   \tvscsvarexp(e,\seqof{C \supseteq e'})     &=& C \cond{e = e'} \setof e 
\\ \tvscsvarexp(e,\seqof{\_,C \supseteq e'})  &=& C \cond{e = e'} \setof e 
\\ \tvscsvarexp(e,\seqof{\_ \disj \_})        &=& \setof{e}
\end{eqnarray*}
\begin{code}
tvscsVarExpand :: GenVar -> [TVarSideConds] -> FreeVars
tvscsVarExpand e []  =  injVarSet $ S.singleton e
tvscsVarExpand e (TVSC e' _ (Just vsC) _ : _)
  |  e == e'        =  injVarSet vsC
tvscsVarExpand e (_:tvscs) = tvscsVarExpand e tvscs
\end{code}


\begin{eqnarray*}
\scdiffexp_{sc}(e,B) 
    &=& dosomethingwith
         ( \scvarexp_{sc}(e)
         , \power(\scvarexp_{sc})(B)
         )
\end{eqnarray*}
\begin{code}
scDiffExpand sc (e,bB) = noFreevars -- for now
\end{code}

\begin{eqnarray*}
   \beta(\lst v) &=& \setof{\lst v}, \qquad\qquad \lst v \notin \beta
\\ \beta(\lst v) &=& \elems(\beta.\lst v),
    \qquad\qquad \mbox{if $\beta.\lst v$ is a list}
\\ \beta(\lst v) &=& \beta.\lst v,
      \qquad\qquad \mbox{if $\beta.\lst v$ is a set}
\\ \beta(\lst v) &=& L \cup \bigcup \fv_{sc}^*(T)
     \quad \mbox{if $\beta.\lst v$ has form $(L,T)$}
\end{eqnarray*}
\begin{code}
instantiateLstVar :: InsContext -> Binding -> ListVar -> FreeVars
instantiateLstVar insctxt bind lv
  = case lookupLstBind bind lv of
      Nothing             ->  (S.singleton $ LstVar lv, [])
      Just (BindList vl)  ->  (S.fromList vl, [])
      Just (BindSet  vs)  ->  (vs, [])
      Just (BindTLVs tlvs)
       -> let (ts,lvs) = (tmsOf tlvs, lvsOf tlvs)
          in  mrgFreeVarList
               ( ( S.fromList $ map LstVar lvs,[]) 
                 : map (deduceFreeVars insctxt) ts )
\end{code}
