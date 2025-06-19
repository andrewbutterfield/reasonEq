\chapter{Type Checking and Inference}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Typing ( TypeVariable
              , TypeSubst
              , TypeScheme(..), pattern Scheme
              , TermVariable
              , Env
              , TypeEnv(..)
              , typeInference
              , CanonicalMap
              , typeVarEquivalence
              , TypCmp
              , canonise
              )
where

import Data.Maybe
import Data.List (nub,singleton,sort)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import YesBut
import Control (mapsnd)
import LexBase
import Variables
import Types
import AST
import VarData

import StdTypeSignature

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}

\newpage
\section{Introduction to Typing}

Once we start to deal with predicates that refer to data items such as 
numbers, sets, lists, etc., 
we need typing information to prevent spurious matches
(e.g. $42 = 42 \land 42$ or $\True = \True + 0$).
The plan is that when matching is done
it ensures that the \h{Type} component of the \emph{focus} term 
indicates the correct type.

We implement the W algorithm for type inferencing, 
by adapting a version by Martin Grabm{\"u}ller (MG)
(\url{https://github.com/mgrabmueller}), which is closely based on THIH by Mark P. Jones


\section{Datatypes}

We show the MG abstract syntax and then connect these with our own types.


\subsection{Literals}

From MG:
$$
\begin{array}{l@{\quad}l}
\textbf{data}~Lit & {} = LInt~Integer
\\ & {} \mid ~LBool~Bool
\\ & {} \textbf{deriving}~(Eq,Ord)
\end{array}
$$

From \reasonEq:
$$
\begin{array}{l@{\quad}l} 
\h{data Value} & = \h{Boolean b}
\\ & {} \mid \h{Integer i}
\end{array}
$$

\subsection{Expressions}

From MG:
$$
\begin{array}{l@{\quad}l}
\textbf{data}~Exp & {} = EVar~String
\\ & {} \mid ~ELit~Lit
\\ & {} \mid ~EApp~Exp~Exp
\\ & {} \mid ~EAbs~String~Exp
\\ & {} \mid ~ELet~String~Exp~Exp
\\ & {} \textbf{deriving}~(Eq,Ord)
\end{array}
$$
From \reasonEq: 
$$
\begin{array}{l@{\quad}l} 
\h{data Term} & {} = \h{Var typ v}
\\ & {} \mid ~\h{Val typ k} 
\\ & {} \mid ~\h{Cons typ sb "@" [Term,Term]} 
\\ & {} \mid ~\h{Lam typ "lambda" Term}
\\ & {} \mid ~\dots
\end{array}
$$
We don't have a let-term, but also have the following:
$$
\begin{array}{l@{\quad}l} 
\h{data Term} & {} = \dots
\\ & {} \mid ~\h{Bnd typ n vs Term} 
\\ & {} \mid ~\h{Cls n Term} 
\\ & {} \mid ~\h{Sub typ Term sub}
\\ & {} \mid ~\h{Iter typ sa na si ni lvs}
\\ & {} \mid ~\h{Typ typ}
\end{array}
$$

\subsection{Type Variables}

We represent type-variables with our identifiers:
\begin{code}
type TypeVariable = Identifier
\end{code}

From MG:
$$
\begin{array}{l@{\quad}l}
\textbf{data}~Type & {} = Tvar~String
\\ & {} \mid ~TInt
\\ & {} \mid ~TBool
\\ & {} \mid ~TFun~Type~Type
\\ & {} \textbf{deriving}~(Eq,Ord)
\end{array}
$$

From \reasonEq:
$$
\begin{array}{l@{\quad}l} 
\h{data Type} & = \h{ArbType} 
\\ & {} \mid ~\h{TypeVar Identifier}
\\ & {} \mid ~\h{TypeCons Identifier [Type]}
\\ & {} \mid ~\h{AlgType Identifier [(Identifier,[Type])]}
\\ & {} \mid ~\h{FunType Type Type}
\\ & {} \mid ~\h{GivenType Identifier}
\\ & {} \mid ~\h{BottomType}
\end{array}
$$
Here $TInt$ and $TBool$ are modelled respectively 
by \h{GivenType "Z"} and \h{GivenType "B"}.

For \h{AlgType} (of which \h{TypeCons} is a special case),
we should refer to \url{https://stanford-cs242.github.io/f19/lectures/03-2-algebraic-data-types.html}.


\subsection{Type Schemes}

From MG:
$$
\begin{array}{l@{\quad}l}
\textbf{data}~Scheme & {} = Scheme~[String]~Type
\end{array}
$$

A type-scheme quantifies over type-variables 
($\forall t_1,\dots,t_n \bullet t$).
\begin{code}
data TypeScheme = TS [TypeVariable] Type deriving Show
pattern Scheme qvars typ = TS qvars typ
\end{code}


\subsection{Type Substitutions}

A type-substitution is a mapping from type-variables to types.
\begin{code}
type TypeSubst = Map TypeVariable Type
nullSubst :: TypeSubst
nullSubst = M.empty

composeSubst         :: TypeSubst -> TypeSubst -> TypeSubst
composeSubst s1 s2   = (M.map (apply s1) s2) `M.union` s1
\end{code}

\subsection{Types Class}

From MG:
$$
\begin{array}{lll}
\lefteqn{\textbf{class}~Types~a~\textbf{where}}
\\ \quad ftv & :: & a \fun Set~String
\\ \quad apply & :: & Subst \fun a \fun a
\end{array}
$$

We use the MG \h{Types} class as is:
\begin{code}
class Types a where
    ftv    ::  a -> Set TypeVariable
    apply  ::  TypeSubst -> a -> a
\end{code}

We have instances for types, lists of types, and type-schemes:
\begin{code}
instance Types Type where
    ftv ArbType          =  S.empty
    ftv (TypeVar n)      =  S.singleton n
    ftv (TypeCons i ts)  =  S.unions $ map ftv ts
    ftv (GivenType _)    =  S.empty
    ftv (FunType t1 t2)  =  ftv t1 `S.union` ftv t2
    ftv t                =  error ("Type.ftv NYfI: "++show t)

    apply _ ArbType          =  ArbType
    apply s t@(TypeVar n)    =  case M.lookup n s of
                                  Nothing  ->  t
                                  Just t'  ->  t'
    apply s (TypeCons i ts)  =  TypeCons i $ map (apply s) ts
    apply s (FunType t1 t2)  =  FunType (apply s t1) (apply s t2)
    apply _ t@(GivenType _)  =  t
    apply s t                =  error ("Type.apply NYfI: "++show t)

instance Types TypeScheme where
    ftv (Scheme vars t)      =  (ftv t) `S.difference` (S.fromList vars)

    apply s (Scheme vars t)  =  Scheme vars (apply (foldr M.delete s vars) t)

instance Types a => Types [a] where
    apply s  =  map (apply s)
    ftv l    =  foldr S.union S.empty (map ftv l)
\end{code}

\subsection{Type Environments}

A type environment is a mapping from a term variable to a type scheme.
For us variables are complicated, 
so we need to be careful about what we choose to be a ``variable''
for type-checking.
For instance, we expect $x$, $x'$ and $x_1$ to have the same type,
but we don't expect $x$ and $\lst x$ to have the same type.
In fact, the notion of a type for $\lst x$ isn't particularly useful.
At best, it would resolve into a product type once it was bound in a match to something concrete.
While a static variable $x$ is different from a dynamic $x$,
it is not helpful to have static variables that use the same identifiers
as dynamic ones.
In conclusion, we will also just associate types with variable identifiers.
\begin{code}
type TermVariable = Identifier
type Env = Map TermVariable TypeScheme
newtype TypeEnv = TypeEnv Env

instance Types TypeEnv where
    ftv (TypeEnv env)      =  ftv (M.elems env)
    apply s (TypeEnv env)  =  TypeEnv (M.map (apply s) env)
\end{code}

Removing an term variable from an environment:
\begin{code}
remove :: TypeEnv -> TermVariable -> TypeEnv
remove (TypeEnv env) var  =  TypeEnv (M.delete var env)
\end{code}

The function \h{generalize}, given an environment and type,
generates a type-scheme that pulls out type variables free in the type
that are not free in the environment:
\begin{code}
generalize        ::  TypeEnv -> Type -> TypeScheme
generalize env t  =   Scheme vars t
  where vars = S.toList ((ftv t) `S.difference` (ftv env))
\end{code}

\subsection{Fresh Typenames}

We generate fresh names of the form prefix-number,
for a generally fixed prefix, and with an ascending numeric postfix.

\begin{code}
type FreshInts = [Int] -- should be an infinite strictly ascending list
newTypeVariable :: FreshInts -> String -> (FreshInts,Type)
newTypeVariable (fi:fis) prefix = (fis,TypeVar $ jId (prefix++show fi))
\end{code}
We will choose to use uppercase `A' as the fixed prefix,
and expect all type-variables in theories
to start with a lowercase letter, 
so that generated names always precede those in the theories.
This is to support the need for equivalence classes of type-variables,
with canonical representatives, discussed below.
\begin{code}
newTyVar :: FreshInts -> (FreshInts,Type)
newTyVar fis = newTypeVariable fis genTypeRoot
\end{code}


Replaces all bound type variables in a type
scheme with fresh type variables:
\begin{code}
instantiate :: FreshInts -> TypeScheme -> (FreshInts,Type)
instantiate fis (Scheme vars t) 
  = (fis',apply s t)
  where
    (fis',vnvs) = mapNTV fis [] vars
    mapNTV fis vnvs [] = (fis,vnvs)
    mapNTV fis vnvs (v:vars)
      = let (fis',nv) = newTyVar fis  
        in mapNTV fis' ((v,nv):vnvs) vars
    s = M.fromList vnvs                                 
\end{code}

\newpage
\section{Unification}

We use \h{MonadFail} here to handle errors, as per the rest of \reasonEq.

\subsection{Building Type-substitutions}

The ``occurs-check'' occurs whenever we create a identifier-type binding:
\begin{code}
varBind :: MonadFail mf => TypeVariable -> Type -> mf TypeSubst
varBind u t  
  | t == TypeVar u      =  return nullSubst
  | u `S.member` ftv t  =  fail 
                             ("occurs check fails: " 
                               ++ show u ++ " vs. " ++ show t)
  | otherwise           =  return $ M.singleton u t
\end{code}

\subsection{Most-general Unification}

\begin{code}
mgu :: MonadFail mf => FreshInts -> Type -> Type -> mf (FreshInts,TypeSubst)
mgu fis ArbType ArbType = return (fis,M.empty)
mgu fis (TypeVar u) t          =  do ts <- varBind u t ; return (fis,ts)
mgu fis t (TypeVar u)          =  do ts <- varBind u t ; return (fis,ts)
mgu fis tc1@(TypeCons _ _) tc2@(TypeCons _ _)
  | tc1 == tc2                 =  return (fis,M.empty)
mgu fis ta1@(AlgType _ _) ta2@(AlgType _ _)
  | ta1 == ta2                 =  return (fis,M.empty)
mgu fis (FunType l r) (FunType l' r')  
  =  do  (fis1,s1) <- mgu fis l l'
         (fis2,s2) <- mgu fis1 (apply s1 r) (apply s1 r')
         return ( fis2, s1 `composeSubst` s2 )
mgu fis (GivenType gt1) (GivenType gt2)
  | gt1==gt2                   =  return (fis,nullSubst)
mgu fis t1 t2                  =  fail ("mgu types don't unify:\n  t1 is "
                                        ++show t1
                                        ++"\n  t2 is "++show t2)
\end{code}

\section{Type Inference}

\subsection{Type Inferencer}

This is the main entry point:
\begin{code}
typeInference :: MonadFail mf 
              => [VarTable] 
              -> Term 
              -> mf (Type,Term,TypeSubst)
typeInference vts trm
  = do  let (fis,env) = buildTypeEnv vts [1..] M.empty (getVars trm)
        -- ! fis is infinite !
        (_,(sub, typ)) <- inferTypes vts fis (TypeEnv env) trm
        let typ' = apply sub typ
        return (typ',settype typ' trm,sub)

--        let tk = termtype trm
--        let trm' = if isEType $ pdbg "TK" tk
--                   then settype typ' trm
--                   else settype typ' trm

getVars :: Term -> [Variable]
getVars = stdVarsOf . S.toList . mentionedIds


buildTypeEnv :: [VarTable] -> FreshInts -> Env -> [Variable] 
             -> (FreshInts,Env)
buildTypeEnv vts fis env [] = (fis,env)
buildTypeEnv vts fis env (v:vs) 
  = let (fis',env') = addVarType vts fis env v
    in  buildTypeEnv vts fis' env' vs

addVarType :: [VarTable] -> FreshInts -> Env -> Variable -> (FreshInts,Env)
addVarType vts fis env v@(Vbl n _ _)
  = case lookupVarTables vts v of
      KnownConst trm ->  buildTypeEnv vts fis env (getVars trm)           
      KnownVar typ -> (fis, M.insert n (Scheme [] typ) env)
     -- generic or unknown
      _ -> let (fis',tv) = newTyVar fis 
           in (fis',M.insert n (Scheme [] tv) env)
\end{code}



\newpage
\subsection{Infer Types}

We use some special names to identify lambdas and explicit application operators
\begin{code}
lambda = jId "lambda"
app = jId "@"
\end{code}

\TLEGEND 

\begin{code}
inferTypes :: MonadFail mf
           => [VarTable] -> FreshInts 
           -> TypeEnv -> Term -> mf (FreshInts,(TypeSubst, Type))
\end{code}

\subsubsection{Values}

$\ITLIT$
\begin{code}
inferTypes vts fis _ (Val _ l) = return (fis,(nullSubst,valueType l))
\end{code}

\subsubsection{Variables}

$\ITVAR$
\begin{code}
inferTypes vts fis (TypeEnv env) (Var _ (Vbl n _ _)) 
  = case M.lookup n env of
      Nothing     ->  fail $ "unbound variable: " ++ show n
      Just sigma  ->  do let (fis',t) = instantiate fis sigma
                         return (fis,(nullSubst, t))
\end{code}

\subsubsection{Abstraction}

$\ITABS$

$\ITABSN$
\begin{code}
inferTypes vts fis env (Lam _ lmbd [StdVar (Vbl n _ _)] e)
  | lmbd == lambda 
  = do let (fis1,tv,env') = abstractLambdaVar fis env n
       (fis2,(s1, t1)) <- inferTypes vts fis1 env' e
       return (fis2,(s1, FunType (apply s1 tv) t1))
-- for multiple abs-variables we just do a recursive trick
inferTypes vts fis env (Lam typ lmbd (StdVar (Vbl n _ _):vl) e)
  | lmbd == lambda
  = do let (fis1,tv,env') = abstractLambdaVar fis env n
       (fis2,(s1, t1)) <- inferTypes vts fis1 env' lam'
       return (fis2,(s1, FunType (apply s1 tv) t1))
  where lam' = fromJust $ eLam typ lmbd vl e
\end{code} 

\subsubsection{Application}

$\IAPP$
\begin{code}
inferTypes vts fis env (Cons _ True f [e1,e2])
  | f == app 
  = do  let (fis1,tv) = newTyVar fis 
        (fis2,(s1, t1)) <- inferTypes vts fis1 env e1
        (fis3,(s2, t2)) <- inferTypes vts fis2 (apply s1 env) e2
        (fis4,s3) <- mgu fis3 (apply s2 t1) (FunType t2 tv)
        return (fis4,(s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv))
\end{code}

$\ICONS$
\begin{code}
inferTypes vts fis env econs@(Cons _ True _ _)
  = inferTypes vts fis env $ consToApp econs
\end{code}

\subsubsection{Substitution}

$\ILET$
\begin{code}
inferTypes vts fis env (Sub _ e2 (Substn ves lvlvs))
  | islet vel && S.null lvlvs
  = do  (fis1,(s1, t1)) <- inferTypes vts fis env e1
        let TypeEnv env' = remove env x
        let t' = generalize (apply s1 env) t1
        let env'' = TypeEnv (M.insert x t' env')
        (fis2,(s2, t2)) <- inferTypes vts fis1 (apply s1 env'') e2
        return (fis2,(s1 `composeSubst` s2, t2))
  where
    vel = S.toList ves
    islet [_] = True; islet _ = False
    ((Vbl x _ _),e1) = head vel
\end{code}

\begin{code}
inferTypes vts fis env t = return (fis,(M.empty,ArbType))
-- missing:
\end{code}

\newpage
\subsubsection{Support}

We convert a lambda with multiple abstraction variables
into a recursive nesting of lambdas with a single abstraction variable.
\begin{code}
abstractLambdaVar :: FreshInts -> TypeEnv -> Identifier 
                  -> (FreshInts,Type,TypeEnv)
abstractLambdaVar fis env n
  = let (fis1,tv) = newTyVar fis 
        TypeEnv env' = remove env n
        env'' = TypeEnv (env' `M.union` (M.singleton n (Scheme [] tv)))
    in (fis1,tv,env'')

abstractLambdaVars  :: FreshInts -> TypeEnv -> [Identifier] 
                  -> (FreshInts,[Type],TypeEnv)
abstractLambdaVars fis env [n] 
  = let (fis',tv,env') = abstractLambdaVar fis env n
    in  (fis',[tv],env')
abstractLambdaVars fis env (n:ns)
  =  let (fis1,tv,env1) = abstractLambdaVar fis env n
         (fis2,tvs,env2) = abstractLambdaVars fis1 env1 ns
     in  (fis2,tv:tvs,env2) 
\end{code}

We convert a cons $(f~e_1~e_2~\dots~e_n)$
into nested applications $(@~(\dots(@~(@~f~ e_1)~e_2)\dots)~e_n)$.
\begin{code}
consToApp :: Term -> Term
consToApp (Cons _ _ f es)
  = foldl mkApply (fromJust $ eVar ArbType (StaticVar f)) es
consToApp cons = cons

mkApply :: Term -> Term -> Term
mkApply f e = (Cons ArbType True app [f,e])
\end{code}

\newpage
\section{Type-Variable Equivalence}



Unification is used for type inference and results in a type-substitution that
maps type variables to types.
Of particular interest are mappings from type-variables
to types that are just a single type-variable,
as these effectively define the two variables as equivalent.
We want to make that equivalence relation manifest.

\subsection{Motivating Example}

Consider the following type-substitution:
\begin{eqnarray*}
   A_1 &\mapsto& A_3^*
\\ A_2 &\mapsto& A_3
\\ A_4 &\mapsto& A_3^*
\\ A_5 &\mapsto& (A_3^* \fun A_3^*)
\\ t   &\mapsto& A_3
\end{eqnarray*}
Here, $t$ was used in the type-signature for \h{hd} in the \h{Lists} theory,
while $A_1,\dots,A_5$ were generated by \h{buildTypeEnv}.
The issue is that inferred type for the candidate uses $A_3$  
which then doesn't match the use of $t$ in the pattern.
However, $t$ and $A_3$ (and $A_2$) are basically the same.

We can convert all type-variable bindings of the form $s \mapsto t$
into a equivalence $s \cong t$, which results in the following:
\begin{eqnarray*}
   A_1 &\mapsto& A_3^*
\\ A_2 & \cong & A_3
\\ A_4 &\mapsto& A_3^*
\\ A_5 &\mapsto& (A_3^* \fun A_3^*)
\\ t   & \cong & A_3
\end{eqnarray*}
We immediately get the following equivalence classes:
$
  \setof{A_1}, \setof{A_2,A_3,t}, \setof{A_4}, \setof{A_5}
$.
We note that $A_1$ and $A_4$ map to the same things,
so they are also equivalent:
$$
  \setof{A_1,A_4}, \setof{A_2,A_3,t}, \setof{A_5}
$$
So, for every type-variable, we want to answer the following two questions:
\begin{itemize}
  \item What other type-variables are equivalent?
  \item Which of the equivalent type-variables should be the chosen representative?
\end{itemize}
We never want to choose a pattern type-variable,
so we will choose the candidate type-variable $A_i$ 
with the lowest-valued subscript $i$.
The above example simplifies to:
\begin{eqnarray*}
   A_1 &\mapsto& A_2^*
\\ A_5 &\mapsto& (A_2^* \fun A_2^*)
\end{eqnarray*}

Example coded up:
\begin{code}
genTypeRoot = "A"
hdConsTl = M.fromList 
    [ (_1, TypeCons star [TypeVar _3]) 
    , (_2, TypeVar _3)
    , (_4, TypeCons star [TypeVar _3])
    , (_5, FunType (TypeCons star [TypeVar _3]) (TypeCons star [TypeVar _3]))
    , ( t, TypeVar _3)]
  where mktyvar n = jId (genTypeRoot++show n)
        [_1,_2,_3,_4,_5] = map mktyvar  [1..5]
        star = jId "*"
        t = jId "t"
\end{code}

\newpage
\subsection{Implementation}

We represent 
$
\setof{i_{11},\dots,i_{1N_1}},
\dots,
\setof{i_{k1},\dots,i_{kN_k}}
\dots,
\setof{i_{N1},\dots,i_{NN_N}}
$
by sorted nested lists, to begin with.
In reality we may want to also have a map from type-variables to their canonical form.
\begin{code}
type CanonicalMap = Map TypeVariable TypeVariable
typeVarEquivalence :: TypeSubst -> ([([TypeVariable],Type)],CanonicalMap)
typeVarEquivalence tsubst = 
  let
    tvtyps = M.toList tsubst
    eqvtyppairs = map mkEqvTypePair tvtyps
    groups = sort $ groupByType eqvtyppairs
    canonMap = mkCanonicalMap groups
    canonGrps = mapsnd (mkCanonicalTypes canonMap) groups
  in (canonGrps,canonMap)
\end{code}

We switch to having ordered lists of equivalent type-variables
\begin{eqnarray*}
   \seqof{A_1} &\mapsto& A_3^*
\\ \seqof{A_2} &\mapsto& A_3
\\ \seqof{A_4} &\mapsto& A_3^*
\\ \seqof{A_5} &\mapsto& (A_3^* \fun A_3^*)
\\ \seqof{t}   &\mapsto& A_3
\end{eqnarray*}
\begin{code}
mkEqvTypePair :: (TypeVariable,Type) -> ([TypeVariable],Type)
mkEqvTypePair (tv,typ@(TypeVar tv')) = ([tv,tv'],typ)
mkEqvTypePair (tv,typ) = ([tv],typ)
\end{code}

We then group type-variable lists by their associated type
\begin{eqnarray*}
   \seqof{A_1,A_4} &\mapsto& A_3^*
\\ \seqof{A_2,A_3,t} &\mapsto& A_3
\\ \seqof{A_5} &\mapsto& (A_3^* \fun A_3^*)
\end{eqnarray*}
\begin{code}
groupByType :: [([TypeVariable],Type)] -> [([TypeVariable],Type)]
groupByType [] = []
groupByType ((tvs,typ):tvstyps) 
  = grpByType tvs typ $ groupByType tvstyps

grpByType tvs typ [] = [(tvs,typ)]
grpByType tvs typ (tvstyp@(tvs',typ'):tvstyps)
  | typ == typ'  =  grpByType (tvs `mrg` tvs') typ tvstyps
  | otherwise    =  tvstyp : grpByType tvs typ tvstyps

xs `mrg` ys =  nub $ sort (xs++ys)
\end{code}

Finally, we replace all type-variables in the types 
by their corresponding canonical type-variable:
\begin{eqnarray*}
   \seqof{A_1,A_4} &\mapsto& A_2^*
\\ \seqof{A_2,A_3,t} &\mapsto& A_2
\\ \seqof{A_5} &\mapsto& (A_2^* \fun A_2^*)
\end{eqnarray*}
We start by building the ``canonical map'' that maps a type-variable
to its canonical representation:
$$
\{
A_1 \mapsto A_1
,
A_2 \mapsto A_2
,
A_3 \mapsto A_2
,
A_4 \mapsto A_1
,
A_5 \mapsto A_5
,
t       \mapsto A_2
\}
$$
\begin{code}
mkCanonicalMap :: [([TypeVariable],Type)] -> CanonicalMap
mkCanonicalMap = M.unions . map mkCanonMap

mkCanonMap :: ([TypeVariable],Type) -> CanonicalMap
mkCanonMap ([],_) = M.empty
mkCanonMap (tvs@(tv:_),_) = M.fromList $ map (addrng tv) tvs

addrng x y = (y,x)
\end{code}
We then map the canonical map over every type present:
\begin{code}
mkCanonicalTypes :: CanonicalMap -> Type -> Type
mkCanonicalTypes canon (TypeVar i) 
  =  TypeVar $ applyMap canon i
mkCanonicalTypes canon (TypeCons i ts)
  =  TypeCons i $ map (mkCanonicalTypes canon) ts
mkCanonicalTypes canon (AlgType i fs)
  =  AlgType i $ map (mkCanonicalFields canon) fs
mkCanonicalTypes canon (FunType t1 t2)
  =  FunType (mkCanonicalTypes canon t1) (mkCanonicalTypes canon t2)
-- ArbType, GivenType, BottomType are unchanged
mkCanonicalTypes canon typ = typ

mkCanonicalFields canon (i,ts) = (i,map (mkCanonicalTypes canon) ts)

applyMap :: Ord a => Map a a -> a -> a
applyMap mapping x 
  = case M.lookup x mapping of
      Nothing -> x
      Just y  -> y
\end{code}

Finally, building a type-variable binary relation from a canonical map:
\begin{code}
type TypCmp = Type -> Type -> Bool


canonise :: TypCmp -> CanonicalMap -> TypCmp
canonise typcmp canon t1 t2
  = mkCanonicalTypes canon t1 `typcmp` mkCanonicalTypes canon t2
\end{code}





