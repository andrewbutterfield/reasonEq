\section{Abstract Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AST ( VarRole, pattern NoRole
           , pattern Before, pattern During, pattern After
           , Variable
           , pattern StaticVar
           , pattern ObsVar, pattern ExprVar, pattern PredVar
           , pattern PreVar, pattern MidVar, pattern PostVar
           , pattern PreCond, pattern PostCond
           , pattern PreExpr, pattern PostExpr
           , isPreVar
           , ListVar
           , pattern ObsLVar, pattern ExprLVar, pattern PredLVar
           , pattern PreVars, pattern PostVars, pattern MidVars
           , pattern PreExprs, pattern PrePreds
           , isPreListVar
           , GenVar, pattern StdVar, pattern LstVar
           , isPreGenVar
           , VarList
           , VarSet
           , isPreVarSet
           , TermSub, LVarSub, Substn, pattern Substn
           , pattern TermSub, pattern LVarSub, substn
           , Type
           , pattern ArbType,  pattern TypeVar, pattern TypeApp
           , pattern DataType, pattern FunType, pattern GivenType
           , Text, Value, pattern Boolean, pattern Integer, pattern Text
           , TermKind(..)
           , Term
           , pattern Val, pattern Var, pattern Cons
           , pattern Bind, pattern Lam, pattern Sub, pattern Iter
           , pattern EVal, pattern EVar, pattern ECons
           , pattern EBind, pattern ELam, pattern ESub, pattern EIter
           , pattern PVal, pattern PVar, pattern PCons
           , pattern PBind, pattern PLam, pattern PSub, pattern PIter
           , pattern Type
           , pattern E2, pattern P2
           , termkind, isExpr, isPred
           , VarSideCond, pattern Exact, pattern Approx
           , pattern Disjoint, pattern Covers, pattern DisjCov, pattern PreDisj
           , vscTrue
           , addPreSC, addExactSC, addDisjSC, addCoverSC, checkNewSC
           , VarSCMap, SideCond, scTrue
           , pattern SC, pattern Fresh, pattern VarSCs, sidecond
           , int_tst_AST
           ) where
import Data.Char
import Data.List
import Data.Maybe (fromJust)
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import LexBase

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
\end{code}

\subsection{AST Introduction}

We implement a number of variants of variables,
terms that cover expressions and predicates,
and a side-condition language.

\newpage
\subsection{Variables}

We want to implement a range of variables
that can stand for behaviour observations, and arbitrary terms.
We also want to support the notion of list-variables that denote lists of variables.

Variables are either:
\begin{description}
  \item[Static]
    that capture context-sensitive information that does not change during
    the lifetime of a program.
    These always take values that range over appropriate program observations.
  \item[Dynamic]
    that represent behaviour
    with observations that change as the program runs.
    These can have added `decorations' that limit their scope
    to pre, post, and intermediate states of execution.
\end{description}
Dynamic variables can:
\begin{itemize}
  \item
     track a single observable aspect of the behaviour as the program
    runs,
  \item
    denote arbitrary expressions whose values depend on dynamic observables,
    or
  \item
    denote arbitrary predicates whose truth value depend on dynamic observables.
\end{itemize}
The latter two cases are the main mechanism for defining semantics
and laws.

In places where list of variables occur,
it is very useful to have (single) variables
that are intended to represent such lists.
We call these list-variables,
and they generally can take similar decorations as dynamic variables.
Such lists occur in binders, substitutions and iterated terms.

We use short constructors for the datatypes,
and define pattern synonyms with more meaning names.

We start by defining the various roles for dynamic variables
\begin{code}
data VarRole -- Variable role
  = RN -- None
  | RB -- Before (pre)
  | RD String -- During (intermediate)
  | RA -- After (post)
  deriving (Eq, Ord, Show, Read)

pattern NoRole = RN
pattern Before = RB
pattern During n = RD n
pattern After  = RA
\end{code}

Then we view variables as having four flavours:
\begin{code}
data Variable
 = VS Identifier -- Static
 | VO VarRole Identifier -- Dynamic Observation
 | VE VarRole Identifier -- Dynamic Expression
 | VP VarRole Identifier -- Dynamic Predicate
 deriving (Eq,Ord,Show,Read)

pattern StaticVar i = VS i

pattern ObsVar  r i = VO r i
pattern ExprVar r i = VE r i
pattern PredVar r i = VP r i
\end{code}

We also have some pre-wrapped patterns for common cases:
\begin{code}
pattern PreVar   i    = VO RB i
pattern PostVar  i    = VO RA i
pattern MidVar   i n  = VO (RD n) i
pattern PreCond  i    = VP RB i
pattern PostCond i    = VP RA i
pattern PreExpr  i    = VE RB i
pattern PostExpr i    = VE RA i
\end{code}

Some variable predicates:
\begin{code}
isPreVar :: Variable -> Bool
isPreVar (PreVar _)  = True
isPreVar (PreExpr _) = True
isPreVar (PreCond _) = True
isPreVar _           = False
\end{code}

\subsubsection{Identifier and Variable test values}
\begin{code}
i_a = fromJust $ ident "a"
i_b = fromJust $ ident "b"
i_e = fromJust $ ident "e"
i_f = fromJust $ ident "f"

v_a = StdVar $ PreVar $ i_a
v_b = StdVar $ PreVar $ i_b
v_e = PreExpr $ i_e
v_f = PreExpr $ i_f
v_a' = StdVar $ PostVar $ i_a
v_b' = StdVar $ PostVar $ i_b
v_e' = PostExpr $ i_e
v_f' = PostExpr $ i_f
\end{code}

\subsubsection{List Variables}

We also need to introduce the idea of lists of variables,
for use in binding constructs,
which may themselves contain special variables
that denote lists of variables.
We only require this facility for dynamic variables.
We define a list-variable as a specially marked variable with the addition
of a list of identifiers, corresponding to variable `roots'

\begin{code}
data ListVar
 = LO VarRole Identifier [Identifier]
 | LE VarRole Identifier [Identifier]
 | LP VarRole Identifier [Identifier]
 deriving (Eq, Ord, Show, Read)

pattern ObsLVar  r i rs = LO r i rs
pattern ExprLVar r i rs = LE r i rs
pattern PredLVar r i rs = LP r i rs
\end{code}

Pre-wrapped patterns:
\begin{code}
pattern PreVars  i    <-  LO RB i _
pattern PostVars i    <-  LO RA i _
pattern MidVars  i n  <-  LO (RD n) i _
pattern PreExprs i    <-  LE RB i _
pattern PrePreds i    <-  LP RB i _
\end{code}

Useful predicates:
\begin{code}
isPreListVar :: ListVar -> Bool
isPreListVar (PreVars _)  = True
isPreListVar (PreExprs _) = True
isPreListVar (PrePreds _) = True
isPreListVar _            = False
\end{code}

\subsubsection{List Variable test values}
\begin{code}
lva = ObsLVar Before (i_a) []
lvb = ObsLVar After (i_b) []
lve = ExprLVar Before (i_e) []
lvf = ExprLVar Before (i_f) []
\end{code}

\subsubsection{Variable Lists}

A variable-list is composed in general of a mix of normal variables
and list-variables.
We gather these into a `general' variable type
\begin{code}
data GenVar
 = GV Variable -- regular variable
 | GL ListVar  -- variable denoting a list of variables
 deriving (Eq, Ord, Show, Read)

pattern StdVar v = GV v
pattern LstVar lv = GL lv

type VarList = [GenVar]
\end{code}

Some useful predicates:
\begin{code}
isPreGenVar :: GenVar -> Bool
isPreGenVar (StdVar v) = isPreVar v
isPreGenVar (LstVar lv) = isPreListVar lv
\end{code}


We also want variable sets:
\begin{code}
type VarSet = Set GenVar

disjoint, overlaps :: Ord a => Set a -> Set a -> Bool
s1 `disjoint` s2 = S.null (s1 `S.intersection` s2)
s1 `overlaps` s2 = not (s1 `disjoint` s2)

isPreVarSet :: VarSet -> Bool
isPreVarSet = all isPreGenVar . S.toList
\end{code}

\subsubsection{Variable Set test values}
\begin{code}
s0   = S.fromList [] :: VarSet
sa   = S.fromList [v_a]
sa'  = S.fromList [v_a']
sb   = S.fromList [v_b]
sab  = S.fromList [v_a,v_b]
saa' = S.fromList [v_a,v_a']
sab' = S.fromList [v_a,v_b']
sbb' = S.fromList [v_b,v_b']
\end{code}

\newpage
\subsection{Substitutions}

Substitutions associate a list of terms (types,expressions,predicates)
with some variables.
We also want to allow list-variables of the appropriate kind
to occur for things, but only when the target variable is also
a list variable.
\begin{code}
type TermSub = [(Variable,Term)] -- target variable, then replacememt term
type LVarSub = [(ListVar,ListVar)] -- target list-variable, then replacement l.v.
data Substn --  pair-lists below are ordered and unique in fst part
  = SN TermSub LVarSub
  deriving (Eq,Ord,Show,Read)
\end{code}

Patterns and builders:
\begin{code}
pattern Substn ts lvs <- SC ts lvs
pattern TermSub ts   <- SC ts _
pattern LVarSub lvs  <- SC _  lvs

substn :: Monad m => TermSub -> LVarSub -> m Substn
substn ts lvs
 | dupKeys ts'  =  fail "Term substitution has duplicate variables"
 | dupKeys lvs' =  fail "List-var subst. has duplicate variables"
 | otherwise    = return $ SN ts' lvs'
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
lvs_ord_unq = [(lva,lvf),(lvb,lve)]
test_substn_lvs_id = testCase "LVarSub ordered, unique"
 ( substn [] lvs_ord_unq  @?= Just (SN [] lvs_ord_unq) )

lvs_unord_unq = [(lvb,lve),(lva,lvf)]

test_substn_lvs_sort = testCase "LVarSub unordered, unique"
 ( substn [] lvs_unord_unq  @?= Just (SN [] lvs_ord_unq) )

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
 | TA Identifier [Type] -- type application
 | TD Identifier [(Identifier,[Type])] -- ADT
 | TF Type Type -- function type
 | TG Identifier -- given type
 deriving (Eq, Ord, Show, Read)

pattern ArbType = T
pattern TypeVar i  = TV i
pattern TypeApp i ts = TA i ts
pattern DataType i fs = TD i fs
pattern FunType tf ta = TF tf ta
pattern GivenType i = TG i
\end{code}

\newpage
\subsection{Terms}

We want to implement a collection of terms that include
expressions and predicates defined over a range of variables
that can stand for behaviour observations, terms and program variables.


We consider a term as having the following forms:
\begin{description}
  \item [K] A constant value of an appropriate type.
  \item [V] A variable.
  \item [C] A constructor that builds a term out of zero or more sub-terms.
  \item [B] A binding construct that introduces sets of local variables.
  \item [L] A binding construct that introduces lists of local variables.
  \item [S] A term with an explicit substitution of terms for variables.
  \item [I] An iteration of a term over a sequence of list-variables.
  \item [T] An embedding of Types
\end{description}
\begin{eqnarray}
   k &\in& Value
\\ n &\in& Name
\\ \tau &\in& Type
\\ v &\in& Var = \dots
\\ t \in T  &::=&  K~k | V~n | C~n~t^* | (B|L)~n~v^+~t | S~t~(v,t)^+ | I~n~n~v^+ | T~\tau
\end{eqnarray}
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
With the types as proposed (esp. \verb"TD"),
and the term constructors and bindings,
we could develop values from the ground up,
but we would much prefer to have some built-in,
like numbers of various kinds, and maybe characters?
For now we start with booleans, integers and text.
\begin{code}
type Text = String
data Value
 = VB Bool
 | VI Integer
 | VT Text
 deriving (Eq, Ord, Show, Read)

pattern Boolean b = VB b
pattern Integer i = VI i
pattern Text    t = VT t
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
 | S TermKind Term Substn              -- Substitution
 | I TermKind                          -- Iterator
     Identifier  -- top grouping constructor
     Identifier  -- component constructor
     [ListVar]   -- list-variables, same length as component arity
 | ET Type                              -- Embedded TypeVar
 deriving (Eq, Ord, Show, Read)
\end{code}

Kind-neutral patterns:
\begin{code}
pattern Val tk k           =  K tk k
pattern Var tk v           =  V tk v
pattern Cons tk n ts       =  C tk n ts
pattern Bind tk n vl tm    =  B tk n vl tm
pattern Lam tk n vs tm     =  L tk n vs tm
pattern Sub tk tm s        =  S tk tm s
pattern Iter tk na ni lvs  =  I tk na ni lvs
\end{code}
Patterns for expressions:
\begin{code}
pattern EVal t k           =  K (E t) k
pattern EVar t v           =  V (E t) v
pattern ECons t n ts       =  C (E t) n ts
pattern EBind t n vl tm    =  B (E t) n vl tm
pattern ELam t n vs tm     =  L (E t) n vs tm
pattern ESub t tm s        =  S (E t) tm s
pattern EIter t na ni lvs  =  I (E t) na ni lvs
\end{code}
Patterns for predicates:
\begin{code}
pattern PVal k             =  K P k
pattern PVar v             =  V P v
pattern PCons n ts         =  C P n ts
pattern PBind n vl tm      =  B P n vl tm
pattern PLam n vs tm       =  L P n vs tm
pattern PSub tm s          =  S P tm s
pattern PIter na ni lvs    =  I P na ni lvs
\end{code}
Pattern for embedded types:
\begin{code}
pattern Type t             =  ET t
\end{code}

Patterns for binary constructions:
\begin{code}
pattern E2 t n t1 t2 = C (E t) n [t1,t2]
pattern P2 n t1 t2   = C P n [t1,t2]
\end{code}

It can help to test if a term is an expression or predicate:
\begin{code}
termkind :: Term -> TermKind
termkind (Val tk k)           =  tk
termkind (Var tk v)           =  tk
termkind (Cons tk n ts)       =  tk
termkind (Bind tk n vl tm)    =  tk
termkind (Lam tk n vs tm)     =  tk
termkind (Sub tk tm s)        =  tk
termkind (Iter tk na ni lvs)  =  tk

isExpr, isPred :: Term -> Bool
isExpr t = termkind t /= P
isPred t = termkind t == P
\end{code}

In \cite{UTP-book} we find the notion of texts, in chapters 6 and 10.
We can represent these using this proposed term concept,
as values of type \verb"Text", or as terms with modified names.
They don't need special handling or representation here.


\newpage
\subsection{Side-Conditions}

A side-condition is property used in laws,
typically putting a constraint on the free variables of some term.
In many logics, these can be checked by simple inspection of a term.
However, given a logic like ours with explict expression and predicate (a.k.a. \emph{schematic}) variables this is not always possible.

A side condition is about a relationship between the free variables
of term ($T$),
and a set of other (general) variables ($x,\lst{v}$)
The relationship can have the form:
\begin{eqnarray*}
   x,\lst v   \notin  \fv(T) && \mbox{disjoint}
\\ x,\lst v      =    \fv(T) && \mbox{exact}
\\ x,\lst v \supseteq \fv(T) && \mbox{covering}
\\ pre      \supseteq \fv(T) && \mbox{pre-condition}
\end{eqnarray*}
Let $D$, $X$ and $C$ denote sets of variables
that are meant to be be disjoint, exact, and covering respectively.
Let $pre$ denote the assertion that the term has only pre-variables.
Let $F$ denote the free variables of the expression or predicate variable
under consideration.

In addition we may also have a requirement that certain variables are new, or fresh. This applies to the whole term being matched, and not just those terms signified by expression and prediate variables. Let $N$ denote this set.

Here we use $D$, $X$, $C$, $N$, to represent themselves
and also be a shorthand for $D \cap F = \emptyset$,
$X = F$, $F \subseteq C$,
and $fresh(N)$ respectively.
Which is which should be clear from context.

There are a number of laws that govern how
different combinations of the above side-conditions interact.
\begin{eqnarray*}
   N_1 \land N_2 &=& N_1 \cup N_2
\\ D_1 \land D_2 &=& D_1 \cup D_2
\\ X_1 \land X_2 &=& X_1 = X_2 \;\land\; X_1
\\ C_1 \land C_2 &=& C_1 \cap C_2
\\
\\ N_1 \land X_2 &=& N_1 \cap X_2 = \emptyset \;\land\; N_1 \;\land\; X_1
\\ N_1 \land C_2 &=& N_1 \cap C_1 = \emptyset \;\land\; N_1 \;\land\; C_1
\\ D_1 \land X_2 &=& D_1 \cap X_2 = \emptyset \;\land\; X_2
\\ D_1 \land C_2 &=& C_2 \cap D_1 = \emptyset \;\land\; D_1 \;\land\; C_2
\\ X_1 \land C_2 &=& X_1 \subseteq C_2 \;\land\; X_1
\end{eqnarray*}
Given that variable matching will respect variable roles (\verb"VarRole"),
if we have either $C$ or $X$ specified, then we check $pre$ at side-condition generation time.
We can summarise by saying, given a satisfiable side-condition involving $N$, $D$, $X$, and $C$, then there is a faithful representation
where the following invariant holds:
\[
N \not\!\cap\; X
\land
N \not\!\cap\; C
\land
D \not\!\cap\; X
\land
D \not\!\cap\; C
\land
X \subseteq C
\]
In fact we see that our representation either consists solely of $X$,
or else contains one or more of $pre$, $D$, or $C$.
If both $pre$ and $C$ were specified, then we will have checked that all relevant variables in $C$ satisfy $pre$, and hence it becomes superfluous.

\newpage
\subsubsection{Variable side-conditions}
So, a side-condition associated with a term variable is either exact,
or approximate:
\begin{code}
data VarSideCond
 = X VarSet
 | A Bool -- true if term must be a pre-condition
     (Maybe VarSet) -- D
     (Maybe VarSet) -- C
 deriving (Eq,Ord,Show,Read)

pattern Exact vs = X vs
pattern Approx pre mD mC <- A pre mD mC
pattern Disjoint d <- A _ (Just d) _
pattern Covers c <- A _ _ (Just c)
pattern DisjCov d c <- A _ (Just d) (Just c)
pattern PreDisj pre d <- A pre (Just d) _
\end{code}

Typically a variable side-condition will be built
from fragments that specify one of $pre$, $D$, $X$ or $C$,
starting with a condition where all parts are ``null'',
signalling a trivially true side-condition.
\begin{code}
vscTrue :: VarSideCond
vscTrue = A False Nothing Nothing
\end{code}

We will want to merge a set with a maybe-set below:
\begin{code}
mrgSet  :: Ord a
          => (Set a -> Set a -> Set a) -> Set a -> Maybe (Set a)
          -> Set a
mrgSet op s Nothing    =  s
mrgSet op s (Just s')  =  s `op` s'

jmrgSet op s ms = Just $ mrgSet op s ms
\end{code}

Variable Side-Condition test values:
\begin{code}
sc_pre          =  A True Nothing Nothing
sc_exact_a      =  Exact sa
sc_exact_b      =  Exact sb
sc_exact_ab     =  Exact sab
sc_exact_ab'    =  Exact sab'
sc_cover_a      =  A False Nothing $ Just sa
sc_cover_ab     =  A False Nothing $ Just sab
sc_cover_ab'    =  A False Nothing $ Just sab'
sc_disjoint_a   =  A False (Just sa) Nothing
sc_disjoint_b   =  A False (Just sb) Nothing
sc_disjoint_ab  =  A False (Just sab) Nothing
sc_D_a_C_b      =  A False (Just sa) (Just sb)
sc_D_a_C_bb'    =  A False (Just sa) (Just sbb')
\end{code}

\newpage
\paragraph{Adding $pre$:} check against any pre-existing $X$ or $C$
\begin{code}
addPreSC :: Monad m => VarSideCond -> m VarSideCond

addPreSC vsc@(Exact x)
 | isPreVarSet x   =  return vsc
 | otherwise       =  fail "AST.addPreSC: exact set is not a precondition"

addPreSC vsc@(Covers vs)
 | isPreVarSet vs   =  return vsc
 | otherwise        =  fail "AST.addPreSC: covering set is not a precondition"

addPreSC (Approx _ mD mC) = return $ A True mD mC
\end{code}

Tests:
\begin{code}
test_add_pre_to_true = testCase "Add pre to trivial SC"
 ( addPreSC vscTrue  @?=  Just sc_pre )

test_add_pre_to_exact_ok = testCase "Add pre to exact SC (OK)"
 ( addPreSC sc_exact_ab  @?=  Just sc_exact_ab )

test_add_pre_to_exact_fail = testCase "Add pre to exact SC (Fail)"
 ( addPreSC sc_exact_ab'  @?=  Nothing )

test_add_pre_to_cover_ok = testCase "Add pre to cover SC (OK)"
 ( addPreSC sc_cover_ab  @?=  Just sc_cover_ab )

test_add_pre_to_cover_fail = testCase "Add pre to cover SC (Fail)"
 ( addPreSC sc_cover_ab'  @?=  Nothing )

test_add_pre_to_disjoint = testCase "Add pre to disjoint"
 ( addPreSC sc_disjoint_ab  @?=  Just (A True (Just sab) Nothing) )

addPreTests = testGroup "AST.addPreSC"
               [ test_add_pre_to_true
               , test_add_pre_to_exact_ok
               , test_add_pre_to_exact_fail
               , test_add_pre_to_cover_ok
               , test_add_pre_to_cover_fail
               , test_add_pre_to_disjoint
               ]
\end{code}

\newpage
\paragraph{Adding $D$:} check against any pre-existing $X$ or $C$
\begin{code}
addDisjSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond

addDisjSC d vsc@(Exact x)
 | d `disjoint` x  =  return vsc
 | otherwise       =  fail "AST.addDisjSC: exact and disjoint sets overlap"

addDisjSC d (Approx pre mD mC@(Just c))
 | c `disjoint` d  =  return $ A pre (jmrgSet S.union d mD) mC
 | otherwise       =  fail "AST.addDisjSC: covering and disjoint sets overlap"

addDisjSC d (Approx pre mD mC)
  = return $ A pre (jmrgSet S.union d mD) mC
\end{code}

Tests:
\begin{code}
test_add_disj_to_true = testCase "Add disjoint to trivial SC"
 ( addDisjSC sab vscTrue  @?=  Just sc_disjoint_ab)

test_add_disj_to_exact_ok = testCase "Add disjoint to exact (Ok)"
 ( addDisjSC sb sc_exact_a  @?=  Just sc_exact_a )

test_add_disj_to_exact_fail = testCase "Add disjoint to exact (Fail)"
 ( addDisjSC sb sc_exact_ab  @?=  Nothing )

test_add_disj_to_cover_ok = testCase "Add disjoint to cover (Ok)"
 ( addDisjSC sb sc_cover_a  @?=  Just (A False (Just sb) (Just sa)) )

test_add_disj_to_cover_fail = testCase "Add disjoint to cover (Fail)"
 ( addDisjSC sb sc_cover_ab  @?=  Nothing )

test_add_disj_to_disj = testCase "Add disjoint to disjoint"
 ( addDisjSC sa sc_disjoint_b  @?=  Just sc_disjoint_ab )

test_add_disj_to_mixed = testCase "Add disjoint to disjoint and cover"
 ( addDisjSC sa' sc_D_a_C_b  @?=  Just (A False (Just saa') (Just sb)) )

addDisjTests = testGroup "AST.addDisjSC"
               [ test_add_disj_to_true
               , test_add_disj_to_exact_ok
               , test_add_disj_to_exact_fail
               , test_add_disj_to_cover_ok
               , test_add_disj_to_cover_fail
               , test_add_disj_to_disj
               , test_add_disj_to_mixed
               ]
\end{code}

\newpage
\paragraph{Adding $X$:} check against any pre-existing $pre$, $D$, $X$ or $C$
\begin{code}
addExactSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond

addExactSC x vsc@(Exact x0)
 | x == x0    =  return vsc
 | otherwise  =  fail "AST.addExactSC: differing exact sets"

addExactSC x (Approx pre _ _)
 | pre && not (isPreVarSet x) = fail "AST.addExactSC: exact set not pre-condition"

addExactSC x (Disjoint d)
 | x `overlaps` d = fail "AST.addExactSC: exact and disjoint sets overlap"

addExactSC x (Covers c)
 | not(x `S.isSubsetOf` c) = fail "AST.addExactSC: exact not inside covering set"

addExactSC x _ = return $ Exact x
\end{code}

Tests:
\begin{code}
test_add_exact_to_true = testCase "Add exact to trivial SC"
 ( addExactSC sab vscTrue  @?=  Just sc_exact_ab)

test_add_exact_to_exact_ok = testCase "Add exact to exact (Ok)"
 ( addExactSC sa sc_exact_a  @?=  Just sc_exact_a )

test_add_exact_to_exact_fail = testCase "Add exact to exact (Fail)"
 ( addExactSC sb sc_exact_ab  @?=  Nothing )

test_add_exact_to_cover_ok = testCase "Add exact to cover (Ok)"
 ( addExactSC sa sc_cover_ab  @?=  Just sc_exact_a )

test_add_exact_to_cover_fail = testCase "Add exact to cover (Fail)"
 ( addExactSC sb sc_cover_a  @?=  Nothing )

test_add_exact_to_disj = testCase "Add exact to disjoint"
 ( addExactSC sa sc_disjoint_b  @?=  Just sc_exact_a )

test_add_exact_to_mixed = testCase "Add exact to disjoint and cover"
 ( addExactSC sb sc_D_a_C_b  @?=  Just sc_exact_b )

addExactTests = testGroup "AST.addExactSC"
               [ test_add_exact_to_true
               , test_add_exact_to_exact_ok
               , test_add_exact_to_exact_fail
               , test_add_exact_to_cover_ok
               , test_add_exact_to_cover_fail
               , test_add_exact_to_disj
               , test_add_exact_to_mixed
               ]
\end{code}

\newpage
\paragraph{Adding $C$:} check against any pre-existing $pre$, $D$, or $X$
\begin{code}
addCoverSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond

addCoverSC c vsc@(Exact x)
 | x `S.isSubsetOf` c  =  return vsc
 | otherwise           =  fail "AST.addCoverSC: exact set not inside covering set"

addCoverSC c (Approx pre _ _)
 | pre && not (isPreVarSet c) = fail "AST.addCoverSC: cover set not pre-condition"

addCoverSC c (Disjoint d)
 | c `overlaps` d = fail "AST.addCoverSC: cover and disjoint sets overlap"

addCoverSC c (Approx pre mD mC)
 | S.null c'  =  return $ Exact S.empty
 | otherwise  =  return $ A pre mD $ Just c'
 where c' = mrgSet S.intersection c mC
\end{code}

Tests:
\begin{code}
test_add_cover_to_true = testCase "Add cover to trivial SC"
 ( addCoverSC sab vscTrue  @?=  Just sc_cover_ab)

test_add_cover_to_exact_ok = testCase "Add cover to exact (Ok)"
 ( addCoverSC sab sc_exact_a  @?=  Just sc_exact_a )

test_add_cover_to_exact_fail = testCase "Add cover to exact (Fail)"
 ( addCoverSC sb sc_exact_ab  @?=  Nothing )

test_add_cover_to_cover_c = testCase "Add cover to cover (still cover)"
 ( addCoverSC sa sc_cover_ab  @?=  Just sc_cover_a )

test_add_cover_to_cover_x = testCase "Add cover to cover (exact)"
 ( addCoverSC sb sc_cover_a  @?=  Just (Exact s0) )

test_add_cover_to_disj = testCase "Add cover to disjoint"
 ( addCoverSC sb sc_disjoint_a  @?=  Just sc_D_a_C_b )

test_add_cover_to_mixed = testCase "Add cover to disjoint and cover"
 ( addCoverSC sb sc_D_a_C_bb'  @?=  Just sc_D_a_C_b )

addCoverTests = testGroup "AST.addCoverSC"
               [ test_add_cover_to_true
               , test_add_cover_to_exact_ok
               , test_add_cover_to_exact_fail
               , test_add_cover_to_cover_c
               , test_add_cover_to_cover_x
               , test_add_cover_to_disj
               , test_add_cover_to_mixed
               ]
\end{code}

\subsubsection{Variable condition-add tests}
\begin{code}
varSCTests = testGroup "Adding Variable Side-Conditions"
                [ addPreTests
                , addDisjTests
                , addExactTests
                , addCoverTests
                ]
\end{code}

\subsubsection{Full Side Conditions}

Checking $N$ against a variable-side condition, looking at $X$ and $C$.
\begin{code}
checkNewSC :: VarSet -> VarSideCond -> Bool
checkNewSC n (Exact x)   =  n `disjoint` x
checkNewSC n (Covers c)  =  n `disjoint` c
checkNewSC _ _           =  True
\end{code}

A side-condition for a law lumps together $N$
with a mapping from term variables to variable side-conditions.
\begin{code}
type VarSCMap = Map Variable VarSideCond
data SideCond
 = SC VarSet VarSCMap
 deriving (Eq,Ord,Show,Read)
\end{code}
If both entities are empty, then we have the trivial side-condition,
which is always true:
\begin{code}
scTrue :: SideCond
scTrue = SC S.empty M.empty
\end{code}

Test values:
\begin{code}
m_e_pre = M.fromList [(v_e,sc_pre)]
m_e_exact_a = M.fromList [(v_e,sc_exact_a)]
m_e_cover_a = M.fromList [(v_e,sc_cover_a)]
m_e_disjoint_ab = M.fromList [(v_e,sc_disjoint_ab)]
m_e_X_b_f_C_ab = M.fromList [(v_e,sc_exact_b),(v_f,sc_cover_ab)]
\end{code}

Pattern synonyms and builder
\begin{code}
pattern SideCond n vmap <- SC n vmap
pattern Fresh n <- SC n _
pattern VarSCs vmap <- SC _ vmap

sidecond :: Monad m => VarSet -> VarSCMap -> m SideCond
sidecond n vmap
 | all (checkNewSC n) $ M.elems vmap  =  return $ SC n vmap
 | otherwise  =  fail "fresh set conflicts with variable side-condition"
\end{code}

Tests:
\begin{code}
test_sidecond_empty = testCase "Trivial side-condition"
 ( sidecond S.empty M.empty @?=  Just scTrue)

test_sidecond_freshonly = testCase "Only Freshness"
 ( sidecond sab M.empty @?=  Just (SC sab M.empty) )

test_sidecond_one_pre = testCase "One Precondition"
 ( sidecond S.empty m_e_pre @?=  Just (SC S.empty m_e_pre) )

test_sidecond_fresh_exact_ok = testCase "Freshness and Exact (Ok)"
 ( sidecond sb m_e_exact_a @?=  Just (SC sb m_e_exact_a) )

test_sidecond_fresh_exact_fail = testCase "Freshness and Exact (Fail)"
 ( sidecond sa m_e_exact_a @?=  Nothing )

test_sidecond_fresh_cover_ok = testCase "Freshness and Cover (Ok)"
 ( sidecond sb m_e_cover_a @?=  Just (SC sb m_e_cover_a) )

test_sidecond_fresh_cover_fail = testCase "Freshness and Cover (Fail)"
 ( sidecond sa m_e_cover_a @?=  Nothing )

test_sidecond_fresh_exact_cover_fail = testCase "Freshness, Exact and Cover (Fail)"
 ( sidecond sa m_e_X_b_f_C_ab @?=  Nothing )

test_sidecond_fresh_disjoint = testCase "Freshness and Disjoint"
 ( sidecond saa' m_e_disjoint_ab @?=  Just (SC saa' m_e_disjoint_ab) )

sidecondTests = testGroup "AST.sidecond"
               [ test_sidecond_empty
               , test_sidecond_freshonly
               , test_sidecond_one_pre
               , test_sidecond_fresh_exact_ok
               , test_sidecond_fresh_exact_fail
               , test_sidecond_fresh_cover_ok
               , test_sidecond_fresh_cover_fail
               , test_sidecond_fresh_exact_cover_fail
               , test_sidecond_fresh_disjoint
               ]
\end{code}

\newpage

\subsection{Exported Test Group}
\begin{code}
int_tst_AST :: [TF.Test]
int_tst_AST
 = [ testGroup "\nAST Internal"
     [ substnTests
     , varSCTests
     , sidecondTests
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
\end{code}
