\section{Abstract Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AST ( TermSub, LVarSub
           , Substn, pattern Substn, substn
           , pattern TermSub, pattern LVarSub
           , Type
           , pattern ArbType,  pattern TypeVar, pattern TypeApp
           , pattern DataType, pattern FunType, pattern GivenType
           , isSubTypeOf
           , Txt
           , Value, pattern Boolean, pattern Integer, pattern Txt
           , TermKind(..)
           , isPredKind, isExprKind, ekType
           , Term, readTerm
           , pattern Val, pattern Var, pattern Cons
           , pattern Bind, pattern Lam, pattern Cls
           , pattern Sub, pattern Iter, pattern Type
           , var,  eVar,  pVar
           , bind, eBind, pBind, uBind
           , lam,  eLam,  pLam
           , binderClass
           , pattern EVal, pattern EVar, pattern ECons
           , pattern EBind, pattern ELam, pattern ESub, pattern EIter
           , pattern PVal, pattern PVar, pattern PCons
           , pattern PBind, pattern PLam, pattern PSub, pattern PIter
           , pattern E2, pattern P2
           , termkind, isVar, isExpr, isPred, isAtomic
           , theVar
           , freeVars, subTerms
           , mentionedVars, mentionedVarLists, mentionedVarSets
           , int_tst_AST
           ) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Utilities
import LexBase
import Variables

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{AST Introduction}

We implement a abstract syntax tree for a notion of ``terms''
that cover both expressions and predicates.
We also provide a side-condition language.

\newpage
\subsection{Substitutions}

Substitutions associate a list of terms (types,expressions,predicates)
with some variables.
We also want to allow list-variables of the appropriate kind
to occur for things, but only when the target variable is also
a list variable.
\begin{code}
type TermSub = Set (Variable,Term) -- target variable, then replacememt term
type LVarSub = Set (ListVar,ListVar) -- target list-variable, then replacement l.v.
data Substn --  pair-sets below are unique in fst part
  = SN TermSub LVarSub
  deriving (Eq,Ord,Show,Read)
\end{code}

Patterns and builders:
\begin{code}
pattern Substn ts lvs  <-  SN ts lvs
pattern TermSub ts     <-  SN ts _
pattern LVarSub lvs    <-  SN _  lvs

substn :: Monad m => [(Variable,Term)] -> [(ListVar,ListVar)] -> m Substn
substn ts lvs
 | null ts && null lvs = fail "Empty substitution."
 | dupKeys ts'  =  fail "Term substitution has duplicate variables."
 | dupKeys lvs' =  fail "List-var subst. has duplicate variables."
 | otherwise    = return $ SN (S.fromList ts') (S.fromList lvs')
 where
  ts'  = sort ts
  lvs' = sort lvs

dupKeys :: Eq a => [(a,b)] -> Bool
-- assumes list is ordered
dupKeys ((a1,_):next@((a2,_):_))  =  a1 == a2 || dupKeys next
dupKeys _                         =  False
\end{code}

Tests for substitution construction:
\begin{code}
i_a = fromJust $ ident "a"
i_b = fromJust $ ident "b"
i_e = fromJust $ ident "e"
i_f = fromJust $ ident "f"
i_v = fromJust $ ident "v"
i_P = fromJust $ ident "P"
i_Q = fromJust $ ident "Q"

lva = ObsLVar  Before (i_a) [] []
lvb = ObsLVar  After  (i_b) [] []
lve = ExprLVar Before (i_e) [] []
lvf = ExprLVar Before (i_f) [] []

lvs_ord_unq = [(lva,lvf),(lvb,lve)]
test_substn_lvs_id = testCase "LVarSub ordered, unique"
 ( substn [] lvs_ord_unq  @?= Just (SN S.empty (S.fromList lvs_ord_unq)) )

lvs_unord_unq = [(lvb,lve),(lva,lvf)]

test_substn_lvs_sort = testCase "LVarSub unordered, unique"
 ( substn [] lvs_unord_unq  @?= Just (SN S.empty (S.fromList lvs_ord_unq)) )

lvs_unord_dup = [(lva,lva),(lvb,lve),(lva,lvf)]

test_substn_lvs_dup = testCase "LVarSub with duplicates"
 ( substn [] lvs_unord_dup  @?= Nothing )

substnTests = testGroup "AST.substn"
               [ test_substn_lvs_id
               , test_substn_lvs_sort
               , test_substn_lvs_dup
               ]
\end{code}

\newpage
\subsection{Types}

Types are a restrictive form of terms,
whose main reason here is to prevent large numbers of spurious matches
occurring with expressions.

The ordering of data-constructors here is important,
as type-inference relies on it.
\begin{code}
data Type -- most general types first
 = T  -- arbitrary type
 | TV Identifier -- type variable
 | TC Identifier [Type] -- type constructor, applied
 | TA Identifier [(Identifier,[Type])] -- algebraic data type
 | TF Type Type -- function type
 | TG Identifier -- given type
 deriving (Eq, Ord, Show, Read)

pattern ArbType = T
pattern TypeVar i  = TV i
pattern TypeApp i ts = TC i ts
pattern DataType i fs = TA i fs
pattern FunType tf ta = TF tf ta
pattern GivenType i = TG i
\end{code}

\subsubsection{Sub-Typing}

No surprises here.
\begin{code}
isSubTypeOf :: Type -> Type -> Bool
_ `isSubTypeOf` ArbType  =  True
ArbType `isSubTypeOf` _  =  False
_ `isSubTypeOf` (TypeVar _)  =  True
(TypeApp i1 ts1) `isSubTypeOf` (TypeApp i2 ts2)
 | i1 == i2  =  ts1 `areSubTypesOf` ts2
(DataType i1 fs1) `isSubTypeOf` (DataType i2 fs2)
 | i1 == i2  =  fs1 `areSubFieldsOf` fs2
(FunType tf1 ta1) `isSubTypeOf` (FunType tf2 ta2) -- tf contravariant !
   = tf2 `isSubTypeOf` tf1 && ta1 `isSubTypeOf` ta2
(GivenType i1) `isSubTypeOf` (GivenType i2)  = i1 == i2
_ `isSubTypeOf` _ = False
\end{code}

\begin{code}
areSubTypesOf :: [Type] -> [Type] -> Bool
[]       `areSubTypesOf` []        =  True
(t1:ts1) `areSubTypesOf` (t2:ts2)  =  t1 `isSubTypeOf` t2 && ts1 `areSubTypesOf` ts2
_        `areSubTypesOf` _         =  False
\end{code}

\begin{code}
areSubFieldsOf :: [(Identifier,[Type])] -> [(Identifier,[Type])] -> Bool
[] `areSubFieldsOf` []  =  True
((i1,ts1):fs1) `areSubFieldsOf` ((i2,ts2):fs2)
 | i1 == i2             =  ts1 `areSubTypesOf` ts2 && fs1 `areSubFieldsOf` fs2
_ `areSubFieldsOf` _    =  False
\end{code}


\newpage
\subsection{Terms}

We want to implement a collection of terms that include
expressions and predicates defined over a range of variables
that can stand for behaviour observations, terms and program variables.


We consider a term as having the following forms:
\begin{description}
  \item [K] A constant value of an appropriate type:
    $\K k$ or $\kk k$.
  \item [V] A variable:
    $\V v$ or $\vv v$.
  \item [C] A constructor that builds a term out of zero or more sub-terms:
    $\C n {ts}$, $\cc n {ts}$,
    $\C {\!\oplus\!} {ts}$ or $t_1 \oplus t_2 \oplus \dots \oplus t_n$.
  \item [B] A binding construct that introduces sets of local variables:
    $\B n {v^+} t$ or $\bb n {v^+} t$.
  \item [L] A binding construct that introduces lists of local variables:
    $\L n {v^+} t$ or $\ll n {v^+} t$.
  \item [X] A closure construct that hides all free variables:
    $\X n t$ or $\xx n t$.
  \item [S] A term with an explicit substitution of terms for variables:
    $\S t v t$, $\ss t {v^n} {t^n}$ or $t\sigma$.
  \item [I] An iteration of a term over a sequence of list-variables:
    $\I \oplus n {lv^+}$ or $\ii \bigoplus n {lvs}$.
  \item [T] An embedding of Types: $\T \tau$ or $\tt\tau$.
\end{description}

\begin{eqnarray*}
   k &\in& Value
\\ n &\in& Name
\\ \tau &\in& Type
\\ v &\in& Var = \dots
\\ t \in T  &::=&  \K k
                ~|~ \V v
                ~|~ \C n {t^*}
                ~|~ \B n {v^+} T
                ~|~ \L n {v^+} T
                ~|~ \S t V T
                ~|~ \X n t
                ~|~ \I \oplus n {lv^+}
                ~|~ \T \tau
\\ &=& \kk k
     ~|~ \vv v
     ~|~ \cc n {ts}
     ~|~ \bb n {v^+} t
     ~|~ \ll n {v^+} t
     ~|~ \ss t {v^n} {t^n}
     ~|~ \xx n t
     ~|~ \ii \bigoplus n {lvs}
     ~|~ \tt \tau
\end{eqnarray*}
We need to distinguish between predicate terms and expression terms.
The key difference is that predicates are all of ``type'' $Env \fun \Bool$,
whereas expressions can have different types.
This means that expression matching requires type information,
while that for predicates does not.

\subsubsection{Values}

For predicates,
the only constants we require are $\True$ and $\False$.
For expressions, the situation is more complicated,
at least as far as `basic' values are concerned.
With the types as proposed (esp. \verb"TA"),
and the term constructors and bindings,
we could develop values from the ground up,
but we would much prefer to have some built-in,
like numbers of various kinds, and maybe characters?
For now we start with booleans, integers and text.
\begin{code}
type Txt = String
data Value
 = VB Bool
 | VI Integer
 | VT Txt
 deriving (Eq, Ord, Show, Read)

pattern Boolean b  =  VB b
pattern Integer i  =  VI i
pattern Txt     t  =  VT t
\end{code}


\subsubsection{Expressions and Predicates}

Do we have mutually recursive datatypes or an explicit tag?
With mutually recursive types
we know which we are handling and just match the appropriate patterns,
except,
we need to embed each in the other,
so there always has to be a case which looks for such an embedding
and handles it.
\begin{verbatim}
handleExpr :: Expr -> ....
handleExpr (EK ke) = ...
handleExpr (EV ve) = ...
...
handleExpr (EP pr) = handlePred pr

handlePred :: Pred -> ....
handlePred (PK kp) = ...
handlePred (PV vp) = ...
...
handlePred (PE e) = handleExpr e
\end{verbatim}
With one recursive type we need to check the expr/predicate tag,
but no longer know that we have one kind of term or the other.
So we still have to check for the two term kinds and handle them both.
\begin{verbatim}
handleTerm :: Term -> ....
handleTerm (K E ke) = ...
handleTerm (K P kp) = ...
handleTerm (V E ve) = ...
handleTerm (V P vp) = ...
...
...
\end{verbatim}
From a coding point of view, given pattern synonyms in particular,
there is little to differentiate the two approaches.
One possible advantage of the latter is that if had something
whose handling did not depend on it being expression or predicate,
then we might just need one way to handle it.
A possible candidate here are variables:
\begin{verbatim}
handleTerm (V _ v) = ...
\end{verbatim}
However, `naked' verbs in predicates are always of type boolean,
while those in expressions can have arbitrary types.

\newpage
\subsubsection{Term Kinds}

Given the role played by types,
it makes sense that what marks the distinction between expressions
and predicates is the presence/absence of type information.
\begin{code}
data TermKind
 = P -- predicate
 | E Type -- expression (with type annotation)
 deriving (Eq, Ord, Show, Read)

isPredKind, isExprKind :: TermKind -> Bool
isPredKind P     = True; isPredKind _ = False
isExprKind (E _) = True; isExprKind _ = False

ekType :: TermKind -> Type
ekType (E typ)  =  typ
\end{code}
This is equivalent to \verb"Maybe Type",
but we want it less verbose.

\subsubsection{Terms}

So we shall go with a single term type (\verb"Term"),
with an annotation that is equivalent to \verb"Maybe Type".
\begin{code}
data Term
 = K TermKind Value                    -- Value
 | V TermKind Variable                 -- Variable
 | C TermKind Identifier [Term]        -- Constructor
 | B TermKind Identifier VarSet Term   -- Binder (unordered)
 | L TermKind Identifier VarList Term  -- Binder (ordered)
 | X Identifier Term                   -- Closure (always a predicate)
 | S TermKind Term Substn              -- Substitution
 | I TermKind                          -- Iterator
     Identifier  -- top grouping constructor
     Identifier  -- component constructor
     [ListVar]   -- list-variables, same length as component arity
 | ET Type                              -- Embedded TypeVar
 deriving (Eq, Ord, Show, Read)

readTerm :: String -> Term
readTerm = read
\end{code}

We  need to have a correlation between some terms
and the variables they use.
In particular the \texttt{TermKind} of a \texttt{V} \texttt{Term}
will have to correspond to the \texttt{VarClass} value of the variable.
Also, in binding constructs,
all the general variables being bound will have to agree on \texttt{VarClass}.

Kind-neutral patterns:
\begin{code}
pattern Val  tk k          =   K tk k
pattern Var  tk v          <-  V tk v
pattern Cons tk n ts       =   C tk n ts
pattern Bind tk n vs tm    <-  B tk n vs tm
pattern Lam  tk n vl tm    <-  L tk n vl tm
pattern Cls     n tm       =   X n tm
pattern Sub  tk tm s       =   S tk tm s
pattern Iter tk na ni lvs  =   I tk na ni lvs
\end{code}

Smart constructors for variables and binders.

Variable must match term-class.
\begin{code}
var :: Monad m => TermKind -> Variable -> m Term
var P        v |       isPredVar v  =  return $ V P v
var tk@(E _) v | not $ isPredVar v  =  return $ V tk v
var _       _   =   fail "var: TermKind/VarClass mismatch"
eVar t v = var (E t) v
pVar   v = var P v
\end{code}

\newpage
All variables in a binder variable-set must have the same class.
\begin{code}
bind tk n vs tm
 | S.null vs  =  return tm  -- vacuous binder
 | uniformVarSet vs  =  return $ B tk n vs tm
 | otherwise = fail "bind: var.-set has mixed variables."

eBind typ n vs tm  =  bind (E typ) n vs tm
pBind     n vs tm  =  bind P       n vs tm
-- just for universal closure: [p]
uBind     n    tm  =  return $ B P n S.empty tm
\end{code}

All variables in a lambda variable-list must have the same class.
\begin{code}
lam tk n vl tm
 | null vl  =  return tm  -- vacuous binder
 | uniformVarList vl  =  return $ L tk n vl tm
 | otherwise = fail "lam: var.-list has mixed variables."

eLam typ n vl tm  =  lam (E typ) n vl tm
pLam     n vl tm  =  lam P       n vl tm
\end{code}

\begin{code}
uniformVarSet s = uniformVarList $ S.toList s

uniformVarList [] = True
uniformVarList [_] = True
uniformVarList (gv:vl) = uvl (whatGVar gv) vl
 where
   uvl _ [] = True
   uvl what (gv:vl)
     | whatGVar gv == what  =  uvl what vl
     | otherwise            =  False
\end{code}

It will also be good to enquire the class of a binder:
\begin{code}
binderClass :: Monad m => Term -> m VarClass
binderClass (L _ _ (gv:_) _)  =  return $ whatGVar gv
binderClass (B _ _ gvs    _)  =  return $ whatGVar $ S.elemAt 0 gvs
binderClass _ = fail "binderClass: not a binding term."
\end{code}

Patterns for expressions:
\begin{code}
pattern EVal t k           =  K (E t) k
pattern EVar t v          <-  V (E t) v
pattern ECons t n ts       =  C (E t) n ts
pattern EBind t n vs tm   <-  B (E t) n vs tm
pattern ELam t n vl tm    <-  L (E t) n vl tm
pattern ESub t tm s        =  S (E t) tm s
pattern EIter t na ni lvs  =  I (E t) na ni lvs
\end{code}

Patterns for predicates:
\begin{code}
pattern PVal k             =  K P k
pattern PVar v            <-  V P v
pattern PCons n ts         =  C P n ts
pattern PBind n vs tm     <-  B P n vs tm
pattern PLam n vl tm      <-  L P n vl tm
pattern PSub tm s          =  S P tm s
pattern PIter na ni lvs    =  I P na ni lvs
\end{code}


Pattern for embedded types:
\begin{code}
pattern Type t             =  ET t
\end{code}

Patterns for binary constructions:
\begin{code}
pattern E2 t n t1 t2  = C (E t) n [t1,t2]
pattern P2   n t1 t2  = C P     n [t1,t2]
\end{code}

It can help to test if a term is an variable, expression or predicate:
\begin{code}
termkind :: Term -> TermKind
termkind (Val tk k)           =  tk
termkind (Var tk v)           =  tk
termkind (Cons tk n ts)       =  tk
termkind (Bind tk n vl tm)    =  tk
termkind (Lam tk n vs tm)     =  tk
termkind (Cls i tk)           =  P
termkind (Sub tk tm s)        =  tk
termkind (Iter tk na ni lvs)  =  tk

isVar, isExpr, isPred, isAtomic :: Term -> Bool
isVar (Var _ _) = True ; isVar _ = False
isExpr t = termkind t /= P
isPred t = termkind t == P
isAtomic (K _ _)  =  True
isAtomic (V _ _)  =  True
isAtomic _        =  False
\end{code}

Pulling out variables:
\begin{code}
theVar :: Term -> Variable
-- pre-theVar t  =  isVar t
theVar (V _ v)  =  v
\end{code}

In \cite{UTP-book} we find the notion of texts, in chapters 6 and 10.
We can represent these using this proposed term concept,
as values of type \verb"Txt", or as terms with modified names.
They don't need special handling or representation here.

\subsubsection{Term Tests}

Test values:
\begin{code}
lv_a = ObsLVar  Static i_a [] []
lv_b = VarLVar         i_b [] []
lv_e = ExprLVar Static i_e [] []
lv_P = PredLVar Static i_P [] []

t42 = Val (E ArbType) $ VI 42
n = fromJust $ ident "n"
\end{code}

We need to test the variable and binder smart constructors
\begin{code}
v_P  = PreCond  i_P
v_Q' = PostCond i_Q
v_a =  PreVar    $ i_a
v_b =  PreVar    $ i_b
v_v =  ScriptVar $ i_v
v_a' = PostVar   $ i_a
v_b' = PostVar   $ i_b

varConstructTests  = testGroup "AST.var,eVar,pVar"
 [ testCase "var P P (Ok)"
   ( var P v_P  @?= Just (V P (PreCond i_P) ))
 , testCase "var (E ArbType) P (Fail)"
   ( var (E ArbType) v_P  @?= Nothing )
 , testCase "var P a (Fail)"
   ( var P v_a  @?= Nothing )
 , testCase "var (E ArbType) a (Ok)"
   ( var (E ArbType) v_a
      @?= Just (V (E ArbType) (PreVar i_a )) )
 , testCase "eVar tarb P (Fail)" ( eVar ArbType v_P  @?= Nothing )
 , testCase "eVar tarb a (Ok)"
   ( eVar ArbType v_a @?= Just (V (E ArbType) (PreVar i_a ) ) )
 , testCase "pVar a (Fail)" ( pVar v_a  @?= Nothing )
 , testCase "pVar P (Ok)"
   ( pVar v_P @?= Just (V P (PreCond i_P) ) )
 ]

gv_a =  StdVar v_a
gv_b =  StdVar v_b
gv_v =  StdVar v_v
gv_a' = StdVar v_a'
gv_b' = StdVar v_b'

bindConstructTests  =  testGroup "AST.bind"
 [ testCase "bind P n {} t42 (Ok)"
   ( bind P n S.empty t42 @?= Just t42 )
 , testCase "bind P n {a} t42 (Ok)"
   ( bind P n (S.fromList [gv_a]) t42
     @?= Just (B P n (S.fromList [gv_a]) t42) )
 , testCase "bind P n {a$} t42 (Ok)"
   ( bind P n (S.fromList [LstVar lv_a]) t42
     @?= Just (B P n (S.fromList [LstVar lv_a]) t42) )
 , testCase "bind P n {a,a$} t42 (Ok)"
   ( bind P n (S.fromList [gv_a,LstVar lv_a]) t42
     @?= Just (B P n (S.fromList [gv_a,LstVar lv_a]) t42) )
 , testCase "bind P n {a,e$} t42 (Fail)"
   ( bind P n (S.fromList [gv_a,LstVar lv_e]) t42 @?= Nothing )
 , testCase "bind P n {e$,a} t42 (Fail)"
   ( bind P n (S.fromList [LstVar lv_e,gv_a]) t42 @?= Nothing )
 , testCase "bind P n {a,b,e$} t42 (Fail)"
   ( bind P n (S.fromList [gv_a,gv_b,LstVar lv_e]) t42 @?= Nothing )
 ]

lamConstructTests  =  testGroup "AST.lam"
 [ testCase "lam P n [] t42 (Ok)"
   ( lam P n [] t42 @?= Just t42 )
 , testCase "lam P n [a] t42 (Ok)"
   ( lam P n [gv_a] t42 @?= Just (L P n [gv_a] t42) )
 , testCase "lam P n [a$] t42 (Ok)"
   ( lam P n [LstVar lv_a] t42
     @?= Just (L P n [LstVar lv_a] t42) )
 , testCase "lam P n [a,a$] t42 (Ok)"
   ( lam P n [gv_a,LstVar lv_a] t42
     @?= Just (L P n [gv_a,LstVar lv_a] t42) )
 , testCase "lam P n [a,e$] t42 (Fail)"
   ( lam P n [gv_a,LstVar lv_e] t42 @?= Nothing )
 , testCase "lam P n [e$,a] t42 (Fail)"
   ( lam P n [LstVar lv_e,gv_a] t42 @?= Nothing )
 , testCase "lam P n [a,b,e$] t42 (Fail)"
   ( lam P n [gv_a,gv_b,LstVar lv_e] t42 @?= Nothing )
 ]

termConstructTests  =  testGroup "Term Smart Constructors"
  [ varConstructTests, bindConstructTests,lamConstructTests ]
\end{code}

\newpage
\subsection{Free and Bound Variables}

\begin{eqnarray*}
   fv(\kk k) &=& \emptyset
\\ fv(\vv v) &=& \setof v
\\ fv(\cc n {ts}) &=& \bigcup fv(ts)
\\ fv(\bb n {v^+} t) &=& fv(t) \setminus v^+
\\ fv(\ll n {v^+} t) &=& fv(t) \setminus v^+
\\ fv(\xx n t) &=& \emptyset
\\ fv(\ss t {v^n} {t^n}) &=& fv(t) \setminus v^n \cup \bigcup fv(t^n)
\\ fv(\ii \bigoplus n {lvs}) &=& \emptyset
\\ fv(\tt \tau) &=& \emptyset
\end{eqnarray*}
\begin{code}
freeVars :: Term -> VarSet
freeVars (V _ v)       =  S.singleton $ StdVar v
freeVars (C _ _ ts)    =  S.unions $ map freeVars ts
freeVars (B _ _ vs t)  =  freeVars t `S.difference` vs
freeVars (L _ _ vl t)  =  freeVars t `S.difference` (S.fromList vl)
freeVars (X _ _)       =  S.empty
freeVars (S _ t (SN tsub lvsub))
  = (freeVars t `S.difference` tvs) `S.union` rvs
  where
     (tsvl,rtl) = unzip $ S.toList tsub
     (tlvl,rlvl) = unzip $ S.toList lvsub
     tvs = S.fromList (map StdVar tsvl ++ map LstVar tlvl)
     rvs = S.unions (map freeVars rtl)
           `S.union`
           (S.map LstVar $ S.fromList rlvl)
freeVars (I _ _ _ lvs)  =  S.fromList $ map LstVar lvs
freeVars _ = S.empty
\end{code}


\newpage
\subsection{Parts of Terms}

Sometimes we want lists of all term components
of a given type (terms/variables/list-variables/variable-sets/variable-lists)

\subsubsection{Sub-Terms}

\begin{code}
subTerms :: Term -> [Term]
subTerms t@(C _ _ ts)    =  t : nub (concat $ map subTerms ts)
subTerms t@(B _ _ _ t')  =  t : subTerms t'
subTerms t@(L _ _ _ t')  =  t : subTerms t'
subTerms t@(X _ t')      =  t : subTerms t'
subTerms t@(S _ t' (SN tsub _))
  = t : nub (concat $ map subTerms (t':map snd (S.toList tsub)))
subTerms t               =  [t]
-- t = head $ subTerms t !!
\end{code}

\subsubsection{(General) Variables}

\begin{code}
mentionedVars :: Term -> VarSet
mentionedVars (V _ v)       =  S.singleton $ StdVar v
mentionedVars (C _ _ ts)    =  S.unions $ map mentionedVars ts
mentionedVars (B _ _ vs t)  =  mentionedVars t `S.union` vs
mentionedVars (L _ _ vl t)  =  mentionedVars t `S.union` (S.fromList vl)
mentionedVars (X _ _)       =  S.empty
mentionedVars (S _ t (SN tsub lvsub))
  = (mentionedVars t `S.union` tvs) `S.union` rvs
  where
     (tsvl,rtl) = unzip $ S.toList tsub
     (tlvl,rlvl) = unzip $ S.toList lvsub
     tvs = S.fromList (map StdVar tsvl ++ map LstVar tlvl)
     rvs = S.unions (map mentionedVars rtl)
           `S.union`
           (S.map LstVar $ S.fromList rlvl)
mentionedVars (I _ _ _ lvs)  =  S.fromList $ map LstVar lvs
mentionedVars _ = S.empty
\end{code}

\newpage
\subsubsection{Variable Collections}

\begin{code}
mentionedVarLists :: Term -> [VarList]
mentionedVarLists (C _ _ ts) = concat $ map mentionedVarLists ts
mentionedVarLists (B _ _ _ t) = mentionedVarLists t
mentionedVarLists (L _ _ vl t) = vl : mentionedVarLists t
mentionedVarLists (X _ t) = mentionedVarLists t
mentionedVarLists (S _ t (SN tsub lvsub))
  = mentionedVarLists t ++ concat (map mentionedVarLists rtl)
  where rtl = map snd $ S.toList tsub
mentionedVarLists (I _ _ _ lvs) = [map LstVar lvs]
mentionedVarLists _ = []
\end{code}

Here we include the implicit variable-sets induced by substitution targets.
\begin{code}
mentionedVarSets :: Term -> [VarSet]
mentionedVarSets (C _ _ ts) = concat $ map mentionedVarSets ts
mentionedVarSets (B _ _ vs t) = vs : mentionedVarSets t
mentionedVarSets (L _ _ _ t) = mentionedVarSets t
mentionedVarSets (X _ t) = mentionedVarSets t
mentionedVarSets (S _ t (SN tsub lvsub))
  = mentionedVarSets t ++ tvs ++ rvs
  where
     (tsvl,rtl) = unzip $ S.toList tsub
     (tlvl,rlvl) = unzip $ S.toList lvsub
     tsvs  = S.fromList (map StdVar tsvl)
     tlvs  = S.fromList (map LstVar tlvl)
     tvs   = [tsvs,tlvs,tsvs `S.union` tlvs]
     rtvs  = S.unions (concat (map mentionedVarSets rtl))
     rlvvs = S.fromList (map LstVar rlvl)
     rvs   = [rtvs,rlvvs,rtvs `S.union` rlvvs]
mentionedVarSets (I _ _ _ lvs) = [S.fromList $ map LstVar lvs]
mentionedVarSets _ = []
\end{code}

\newpage

\subsection{Exported Test Group}
\begin{code}
int_tst_AST :: [TF.Test]
int_tst_AST
 = [ testGroup "\nAST Internal"
     [ substnTests
     , termConstructTests
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
\end{code}
