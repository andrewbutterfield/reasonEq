\chapter{Type Checking and Inference}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Typing where

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import LexBase
import Variables
import AST
import FreeVars
import VarData
import Binding

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)

import Debugger
\end{code}

\newpage
\section{Introduction to Typing}

We implement the W algorithm for type inferencing, 
based on a version by Martin Grabm{\"u}ller (MG)
(https://github.com/mgrabmueller).
We follow the structure of that document.

\section{Preliminaries}

We have the following broad correspondance between MG types and ours
(we use notation \texttt{<Typ:=val>} to denote 
a component of type \texttt{Typ} with a specific value \texttt{val}).

\subsection{Literals}

The MG \h{Lit} type is a subset of our \h{Value} type:
\begin{verbatim}
data Lit          --> data Value = ...
  =  LInt Integer       |  Integer Integer
  |  LBool Bool         |  Boolean Bool
\end{verbatim}

\subsection{Types}

The MG \h{Type} type is mainly a subset of our \h{Type},
where specific MG concrete types map to our \h{GivenType}
with meaningful identifiers.
\begin{verbatim}
data Type           --> data Type = ...  
  =  TVar String          |  TypeVar Identifier
  |  TInt                 |  GivenType <Identifer:="Z">
  |  TBool                |  GivenType <Identifer:="B">
  |  TFun Type Type       |  FunType Type Type
\end{verbatim}
\begin{code}
tInt   =  GivenType $ jId "Z"
tBool  =  GivenType $ jId "B"
\end{code}

\subsection{Terms}

The MG \h{Exp} type is very $\lambda$-calculus oriented,
whereas our \h{Term} type is very model-theoretic logic oriented.
We have a general $\lambda$ construct,
and can use \h{Cons} to represent the MG \h{EApp}.
However, there is no close correspondance for the MG \h{ELet}.
Here we exploit the law $\LET x = e_1 \IN e_2  =  e_2[e_1/x]$
and represent it using our \h{Sub} term.
\begin{verbatim}
data Exp                 --> data Term = ...
  =  EVar String               | Var TermKind Variable 
  |  ELit Lit                  | Val TermKind Value
  |  EApp Exp Exp              | Cons TermKind 
                                      Subable := True
                                      Identifier := "@"
                                      [Term] := [exp1,exp2]                
  |  EAbs String Exp           | Lam TermKind 
                                     Identifer := "lambda"
                                     VarList   := [Variable]
                                     Term
  |  ELet String Exp Exp       | Sub TermKind
                                     Term := exp2
                                     Substn :=  [exp1/var]
\end{verbatim}

\newpage
Building the extended $\lambda$-calculus with \h{Term}s.
\begin{code}
eAbs :: Identifier -> Term -> Term
eAbs x t = fromJust $ lam arbtype lambda [StdVar $ StaticVar x] t
lambda = jId "lambda"
arbtype = E ArbType
eFApp :: Identifier -> Term -> Term
eFApp f t =  Cons arbtype False f [t]
eApp :: Term -> Term -> Term
eApp fun arg = Cons arbtype True app [fun,arg]
app = jId "@"
eLet :: Identifier -> Term -> Term -> Term
eLet x e1 e2 
  = Sub arbtype e2 $ jSubstn [(vx,e2)] []
  where vx = StaticVar x 
\end{code}

\subsection{Type Schemes}

Our type-scheme uses our \h{Identifier} type:
\begin{code}
data TypeScheme = TS [Identifier] Type
pattern Scheme qvars typ = TS qvars typ
\end{code}

\subsection{Types Class}

We use the MG \h{Types} class:
\begin{code}
class Types a where
    ftv    ::  a -> Set Identifier
    apply  ::  TypeSubst -> a -> a
\end{code}

We specialise the MG \h{Type} instance for our types:
\begin{code}
instance Types Type where
    ftv (TypeVar n)      =  S.singleton n
    ftv (GivenType _)    =  S.empty
    ftv (FunType t1 t2)  =  ftv t1 `S.union` ftv t2
    ftv t                =  error ("Type.ftv NYfI: "++show t)

    apply s t@(TypeVar n)    =  case M.lookup n s of
                               Nothing  ->  t
                               Just t'  ->  t'
    apply s (FunType t1 t2)  = FunType (apply s t1) (apply s t2)
    apply _ t@(GivenType _)  = t
    apply s t                =  error ("Type.apply NYfI: "++show t)

instance Types a => Types [a] where
    apply s  =  map (apply s)
    ftv l    =  foldr S.union S.empty (map ftv l)
\end{code}

We specialise the MG \h{Scheme} instance for our types:
\begin{code}
instance Types TypeScheme where
    ftv (Scheme vars t)      =  (ftv t) `S.difference` (S.fromList vars)

    apply s (Scheme vars t)  =  Scheme vars (apply (foldr M.delete s vars) t)
\end{code}

\subsection{Type Substitutions}

Our type-substitution uses \h{Identifier}:
\begin{code}
type TypeSubst = Map Identifier Type
nullSubst :: TypeSubst
nullSubst = M.empty

composeSubst         :: TypeSubst -> TypeSubst -> TypeSubst
composeSubst s1 s2   = (M.map (apply s1) s2) `M.union` s1
\end{code}

\subsection{Type Environments}

\begin{code}
newtype TypeEnv = TypeEnv (Map Identifier TypeScheme)

instance Types TypeEnv where
    ftv (TypeEnv env)      =  ftv (M.elems env)
    apply s (TypeEnv env)  =  TypeEnv (M.map (apply s) env)
\end{code}

Removing an identifier from an environment:
\begin{code}
remove :: TypeEnv -> Identifier -> TypeEnv
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

We do not adopt the MG monadic approach in for fresh names,
because this code will be used within an existing monadic setup in \reasonEq.
We simply pull off the head of an infinite ascending list
\begin{code}
type TIState = [Int]
newTyVar :: TIState -> String -> (TIState,Type)
newTyVar (ti:tis) prefix = (tis,TypeVar $ jId (prefix++show ti))

prfxa = "a" ; prfxb = "b" -- used in MG code
\end{code}

Replaces all bound type variables in a type
scheme with fresh type variables:
\begin{code}
instantiate :: TIState -> TypeScheme -> (TIState,Type)
instantiate tis (Scheme vars t) 
  = (tis',apply s t)
  where
    (tis',vnvs) = mapNTV tis [] vars
    mapNTV tis vnvs [] = (tis,vnvs)
    mapNTV tis vnvs (v:vars)
      = let (tis',nv) = newTyVar tis prfxa 
        in mapNTV tis' ((v,nv):vnvs) vars
    s = M.fromList vnvs                                 
\end{code}

\newpage
\section{Unification}

We use \h{MonadFail} here to handle errors, as per the rest of \reasonEq.

\subsection{Building Type-substitutions}

The ``occurs-check'' occurs whenever we create a identifier-type binding:
\begin{code}
varBind :: MonadFail mf => Identifier -> Type -> mf TypeSubst
varBind u t  
  | t == TypeVar u      =  return nullSubst
  | u `S.member` ftv t  =  fail 
                             ("occurs check fails: " 
                               ++ show u ++ " vs. " ++ show t)
  | otherwise           =  return $ M.singleton u t
\end{code}

\subsection{Most-general Unification}

\begin{code}
mgu :: MonadFail mf => TIState -> Type -> Type -> mf (TIState,TypeSubst)
mgu tis (FunType l r) (FunType l' r')  
  =  do  (tis1,s1) <- mgu tis l l'
         (tis2,s2) <- mgu tis1 (apply s1 r) (apply s1 r')
         return ( tis2, s1 `composeSubst` s2 )
mgu tis (TypeVar u) t          =  do ts <- varBind u t ; return (tis,ts)
mgu tis t (TypeVar u)          =  do ts <- varBind u t ; return (tis,ts)
mgu tis (GivenType gt1) (GivenType gt2)
  | gt1==gt2                   =  return (tis,nullSubst)
mgu tis t1 t2                  =  fail ("mgu NYfI")
-- missing Types
-- ArbType
-- TypeCons
-- AlgType
\end{code}

\section{Type Inference}

\subsection{Type Inferencer}

This is the main entry point:
\begin{code}
typeInference :: MonadFail mf => Map Identifier TypeScheme -> Term -> mf Type
typeInference env e =
    do  (_,(s, t)) <- ti [1..] (TypeEnv env) e
        return (apply s t)
\end{code}


\subsection{Literal Types}

\begin{code}
tiLit :: Value -> Type
tiLit (Integer _) = tInt
tiLit (Boolean _) = tBool
\end{code}

\newpage
\subsection{Infer Types}

\begin{code}
ti :: MonadFail mf 
   => TIState -> TypeEnv -> Term -> mf (TIState,(TypeSubst, Type))
--ti (TypeEnv env) (EVar n) = 
--    case Map.lookup n env of
--       Nothing     ->  throwError $ "unbound variable: " ++ n
--       Just sigma  ->  do  t <- instantiate sigma
--                           return (nullSubst, t)
ti tis _ (Val _ l) = return (tis,(nullSubst,tiLit l))
--ti env (EAbs n e) =
--    do  tv <- newTyVar "a"
--        let TypeEnv env' = remove env n
--            env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
--        (s1, t1) <- ti env'' e
--        return (s1, TFun (apply s1 tv) t1)
--ti env exp@(EApp e1 e2) =
--    do  tv <- newTyVar "a"
--        (s1, t1) <- ti env e1
--        (s2, t2) <- ti (apply s1 env) e2
--        s3 <- mgu (apply s2 t1) (TFun t2 tv)
--        return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
--    `catchError`
--    \e -> throwError $ e ++ "\n in " ++ show exp
--ti env (ELet x e1 e2) =
--    do  (s1, t1) <- ti env e1
--        let TypeEnv env' = remove env x
--            t' = generalize (apply s1 env) t1
--            env'' = TypeEnv (Map.insert x t' env')
--        (s2, t2) <- ti (apply s1 env'') e2
--        return (s1 `composeSubst` s2, t2)
ti tis env t = fail ("ti NYfI")
\end{code}

