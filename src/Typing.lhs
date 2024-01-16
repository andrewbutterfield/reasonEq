\chapter{Type Checking and Inference}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2024

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Typing (
              )
where

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import YesBut
import LexBase
import Variables
import AST
import FreeVars
import VarData
import Binding
import MatchContext

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
The plan is that when a proof is setup, 
it ensures that the \h{TermKind} component indicates the correct type.

We implement the W algorithm for type inferencing, 
by adapting a version by Martin Grabm{\"u}ller (MG)
(https://github.com/mgrabmueller).
The mapping from his datatypes to ours is shown
at the end of this chapter 
(Sec.\ref{sec:MG-to-reasonEq},p\pageref{sec:MG-to-reasonEq}).


\section{Datatypes}

We have the following broad correspondance between MG types and ours
(we use notation \texttt{<Typ:=val>} to denote 
a component of type \texttt{Typ} with a specific value \texttt{val}).

\subsection{Type Variables}

We represent type-variables with our identifiers:
\begin{code}
type TypeVariable = Identifier
\end{code}

\subsection{Type Schemes}

A type-scheme quantifies over type-variables 
($\forall t_1,\dots,t_n \bullet t$).
\begin{code}
data TypeScheme = TS [TypeVariable] Type
pattern Scheme qvars typ = TS qvars typ
\end{code}

\subsection{Types Class}

We use the MG \h{Types} class as is:
\begin{code}
class Types a where
    ftv    ::  a -> Set TypeVariable
    apply  ::  TypeSubst -> a -> a
\end{code}

We have instances for types, lists of types, and type-schemes:
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

instance Types TypeScheme where
    ftv (Scheme vars t)      =  (ftv t) `S.difference` (S.fromList vars)

    apply s (Scheme vars t)  =  Scheme vars (apply (foldr M.delete s vars) t)
\end{code}

\subsection{Type Substitutions}

A type-substition is a mappimg from type-variables to types.
\begin{code}
type TypeSubst = Map TypeVariable Type
nullSubst :: TypeSubst
nullSubst = M.empty

composeSubst         :: TypeSubst -> TypeSubst -> TypeSubst
composeSubst s1 s2   = (M.map (apply s1) s2) `M.union` s1
\end{code}

\subsection{Type Environments}

A type environment is a mapping from a term variable to a type scheme.
For us variables are complicated, 
so we need to be careful about what we choose to be a ``variable''
for type-checking.
For instance, we expect $x$, $x'$ and $x_1$ to have the same type,
but we don't expect $x$ and $\lst x$ to have the same type.
In fact, the notion of a type for $\lst x$ isn't particularly useful.
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
type FreshInts = [Int]
newTyVar :: FreshInts -> String -> (FreshInts,Type)
newTyVar (fi:fis) prefix = (fis,TypeVar $ jId (prefix++show fi))
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
      = let (fis',nv) = newTyVar fis "a" 
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
typeInference :: MonadFail mf => Env -> Term -> mf Type
typeInference env e =
    do  (_,(s, t)) <- fi [1..] (TypeEnv env) e
        return (apply s t)
\end{code}



\newpage
\subsection{Infer Types}

\begin{code}
fi :: MonadFail mf 
   => FreshInts -> TypeEnv -> Term -> mf (FreshInts,(TypeSubst, Type))
fi fis (TypeEnv env) (Var _ (Vbl n _ _)) 
  = case M.lookup n env of
      Nothing     ->  fail $ "unbound variable: " ++ show n
      Just sigma  ->  do let (fis',t) = instantiate fis sigma
                         return (fis,(nullSubst, t))
fi fis _ (Val _ l) = return (fis,(nullSubst,valueType l))
fi fis env (ELam ArbType lmbd [StdVar (Vbl n _ _)] e)
  | lmbd == lambda 
  = do let (tis1,tv) = newTyVar fis "a"
       let TypeEnv env' = remove env n
       let env'' = TypeEnv (env' `M.union` (M.singleton n (Scheme [] tv)))
       (tis2,(s1, t1)) <- fi fis env'' e
       return (tis2,(s1, FunType (apply s1 tv) t1))
fi fis env exp@(Cons _ True ap [e1,e2])
  | ap == app 
  = do  let (tis1,tv) = newTyVar fis "a"
        (tis2,(s1, t1)) <- fi tis1 env e1
        (tis3,(s2, t2)) <- fi tis2 (apply s1 env) e2
        (tis4,s3) <- mgu tis3 (apply s2 t1) (FunType t2 tv)
        return (tis4,(s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv))
fi fis env (Sub _ e2 (Substn ves lvlvs))
  | islet vel && S.null lvlvs
  = do  (tis1,(s1, t1)) <- fi fis env e1
        let TypeEnv env' = remove env x
        let t' = generalize (apply s1 env) t1
        let env'' = TypeEnv (M.insert x t' env')
        (tis2,(s2, t2)) <- fi tis1 (apply s1 env'') e2
        return (tis2,(s1 `composeSubst` s2, t2))
  where
    vel = S.toList ves
    islet [_] = True; islet _ = False
    ((Vbl x _ _),e1) = head vel
fi fis env t = fail ("fi NYfI")
-- missing:
\end{code}



\section{MG to \reasonEq\ datatype mapping}\label{sec:MG-to-reasonEq}

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
  |  TInt                 |  GivenType <Identifier:="Z">
  |  TBool                |  GivenType <Identifier:="B">
  |  TFun Type Type       |  FunType Type Type
\end{verbatim}

\subsection{Terms}

The MG \h{Exp} type is very $\lambda$-calculus oriented,
whereas our \h{Term} type is very model-theoretic logic oriented.
We have a general $\lambda$ construct,
and can use \h{Cons} to represent the MG \h{EApp}.
However, there is no close correspondance for the MG \h{ELet}.
Here we exploit the law $\LET x := e_1 \IN e_2  =  e_2[e_1/x]$
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
                                     Identifier := "lambda"
                                     VarList   := [Variable]
                                     Term
  |  ELet String Exp Exp       | Sub TermKind
                                     Term := exp2
                                     Substn :=  [exp1/var]
\end{verbatim}

\newpage
Building the extended $\lambda$-calculus with \h{Term}s.
\begin{code}
eVbl :: String -> Term
eVbl n = jeVar $ StaticVar $ jId n
eLitI n = Val arbtype $ Integer n
eLitB b = Val arbtype $ Boolean b
eAbs :: String -> Term -> Term
eAbs x t = fromJust $ lam arbtype lambda [StdVar $ StaticVar $ jId x] t
lambda = jId "lambda"
arbtype = E ArbType
eFApp :: Identifier -> Term -> Term
eFApp f t =  Cons arbtype False f [t]
eApp :: Term -> Term -> Term
eApp fun arg = Cons arbtype True app [fun,arg]
app = jId "@"
eLet :: String -> Term -> Term -> Term
eLet x e1 e2 
  = Sub arbtype e2 $ jSubstn [(vx,e1)] []
  where vx = StaticVar $ jId x 
\end{code}

\subsection{Tests}

Example expressions:
\begin{code}
e0  =  eLet "id" (eAbs "x" (eVbl "x"))
        (eVbl "id")

e1  =  eLet "id" (eAbs "x" (eVbl "x"))
        (eApp (eVbl "id") (eVbl "id"))

e2  =  eLet "id" (eAbs "x" (eLet "y" (eVbl "x") (eVbl "y")))
        (eApp (eVbl "id") (eVbl "id"))

e3  =  eLet "id" (eAbs "x" (eLet "y" (eVbl "x") (eVbl "y")))
        (eApp (eApp (eVbl "id") (eVbl "id")) (eLitI 2))

e4  =  eLet "id" (eAbs "x" (eApp (eVbl "x") (eVbl "x")))
        (eVbl "id")

e5  =  eAbs "m" (eLet "y" (eVbl "m")
                 (eLet "x" (eApp (eVbl "y") (eLitB True))
                       (eVbl "x")))
       
e6  =  eApp (eLitI 2) (eLitI 2)
\end{code}

\begin{code}
ttest :: Env -> Term -> IO ()
ttest env e =
    do  let res = typeInference env e
        case res of
          Yes t   ->  putStrLn $ show e ++ " :: " ++ show t ++ "\n"
          But err  ->  putStrLn $ show e ++ "\n " ++ (unlines err) ++ "\n"
\end{code}

\begin{code}
elcTest :: IO ()
elcTest = mapM_ (ttest M.empty) [e0, e1, e2, e3, e4, e5, e6]
-- |Collecting Constraints|
-- |main = mapM_ test' [e0, e1, e2, e3, e4, e5]|
\end{code}

