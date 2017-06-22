\section{Abstract Syntax}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AST ( Name
           , Identifier, validIdent, ident, idName
           , VarRole, pattern NoRole
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
           , Substn
           , Type
           , pattern ArbType,  pattern TypeVar, pattern TypeApp
           , pattern DataType, pattern FunType, pattern GivenType
           , _NAME, nametype, _ENV, envtype
           , Text, Value, pattern Boolean, pattern Integer, pattern Text
           , TermKind(..)
           , Term
           , pattern EVal, pattern EVar, pattern ECons
           , pattern EBind, pattern ELam, pattern ESub, pattern EIter
           , pattern PVal, pattern PVar, pattern PCons
           , pattern PBind, pattern PLam, pattern PSub, pattern PIter
           , pattern E2, pattern P2
           , VarSideCond, pattern Exact, pattern Approx
           , pattern Disjoint, pattern Covers, pattern DisjCov, pattern PreDisj
           , nullVSC
           , addPreSC, addExactSC, addDisjSC, addCoverSC, checkNewSC
           , VarSCMap, SideCond
           , pattern SC, pattern Fresh, pattern VarSCs, sidecond
           , test_AST
           ) where
import Data.Char
import Data.List
import Data.Set(Set)
import qualified Data.Set as S
import Data.Map(Map)
import qualified Data.Map as M

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
--import Test.QuickCheck ((==>))
\end{code}

\subsection{AST Introduction}

We implement names, identifiers, a number of variants of variables,
terms that cover expressions and predicates, and a side-condition language.

\subsection{Naming}

We consider `names' to be arbitrary strings,
while `identifiers' are names that satisfy a fairly standard convention
for program variables, namely starting with an alpha character,
followed by zero of more alphas, digits and underscores.

\begin{code}
type Name = String

newtype Identifier = Id Name deriving (Eq, Ord, Show, Read)

validIdent :: Name -> Bool
validIdent (c:cs) =  isAlpha c && all isIdContChar cs
validIdent _      =  False

ident :: Monad m => Name -> m Identifier
ident nm
 | validIdent nm  = return $ Id nm
ident nm = fail ("'"++nm++"' is not an Identifier")

isIdContChar c = isAlpha c || isDigit c || c == '_'

idName :: Identifier -> Name
idName (Id nm) = nm
\end{code}
We will allow the definition, in this module only,
of identifiers whose names start with an underscore.
These will usually be intended to provide some ``base names'',
to key builtin entities that we wish to protect from outside interference.

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
  | RD Name -- During (intermediate)
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

\subsection{Substitutions}

Substitutions associate a list of terms (types,expressions,predicates)
with some variables.
We also want to allow list-variables of the appropriate kind
to occur for things, but only when the target variable is also
a list variable.
\begin{code}
type Substn t
  =  ( [(Variable,t)]        -- target variable, then replacememt term
     , [(ListVar,ListVar)] ) -- target list-variable, then replacement l.v.
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

We will define a two special ``types'' at this point: one that denotes
``names'', and the other that denotes ``environments'',
which are mappings from variable names, to a pair of a type and a value.
For now we just introduce special identifiers for these:
\begin{code}
_NAME = Id "_NAME"
nametype :: Type
nametype = TG _NAME

_ENV  = Id "_ENV"
envtype :: Type
envtype = TG _ENV
\end{code}

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
\end{description}
\begin{eqnarray}
   k &\in& Value
\\ n &\in& Name
\\ v &\in& Var = \dots
\\ t \in T  &::=&  K~k | V~n | C~n~t^* | (B|L)~n~v^+~t | S~t~(v,t)^+ | I~n~n~v^+
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
 | S TermKind Term (Substn Term)       -- Substitution
 | I TermKind                          -- Iterator
     Identifier  -- top grouping constructor
     Identifier  -- component constructor
     [ListVar]   -- list-variables, same length as component arity
 deriving (Eq, Ord, Show, Read)
\end{code}

Patterns for expressions:
\begin{code}
pattern EVal t k = K (E t) k
pattern EVar t v = V (E t) v
pattern ECons t n ts = C (E t) n ts
pattern EBind t n vl tm = B (E t) n vl tm
pattern ELam t n vs tm = L (E t) n vs tm
pattern ESub t tm s = S (E t) tm s
pattern EIter t na ni lvs = I (E t) na ni lvs
\end{code}

Patterns for predicates:
\begin{code}
pattern PVal k = K P k
pattern PVar v = V P v
pattern PCons n ts = C P n ts
pattern PBind n vl tm = B P n vl tm
pattern PLam n vs tm = L P n vs tm
pattern PSub tm s = S P tm s
pattern PIter na ni lvs = I P na ni lvs
\end{code}

Patterns for binary constructions:
\begin{code}
pattern E2 t n t1 t2 = C (E t) n [t1,t2]
pattern P2 n t1 t2   = C P n [t1,t2]
\end{code}


In \cite{UTP-book} we find the notion of texts, in chapters 6 and 10.
We can represent these using this proposed term concept,
as values of type \verb"Text", or as terms with modified names.
They don't need special handling or representation here.



\subsection{Side-Conditions}

A side-condition is property used in laws,
typically putting a constraint on the free variables of some term.
In many logics, these can be checked by simple inspection of a term.
However, given a logic like ours with explict expression and predicate (a.k.a. \emph{schematic}) variables this is not always possible.

A side condition is about a relationship between the free variables
of term ($T$),
and a set of other (general) variables ($x,\lst v$)
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
starting with a ``null'' condition.
\begin{code}
nullVSC :: VarSideCond
nullVSC = A False Nothing Nothing
\end{code}

We will want to merge a set with a maybe-set below:
\begin{code}
mergeSet  :: Ord a
          => (Set a -> Set a -> Set a) -> Set a -> Maybe (Set a)
          -> Maybe (Set a)
mergeSet op s Nothing   = Just (s)
mergeSet op s (Just s') = Just (s `op` s')
\end{code}

Adding $pre$: check against any pre-existing $X$ or $C$
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

Adding $D$, check against any pre-existing $X$ or $C$
\begin{code}
addDisjSC :: Monad m => VarSet -> VarSideCond -> m VarSideCond
addDisjSC d vsc@(Exact x)
 | d `disjoint` x  =  return vsc
 | otherwise       =  fail "AST.addDisjSC: exact and disjoint sets overlap"
addDisjSC d (Approx pre mD mC@(Just c))
 | c `disjoint` d  =  fail "AST.addDisjSC: covering and disjoint sets overlap"
 | otherwise           = return $ A pre (mergeSet S.union d mD) mC
addDisjSC d (Approx pre mD mC)
  = return $ A pre (mergeSet S.union d mD) mC
\end{code}

Adding $X$, check against any pre-existing $pre$, $D$, $X$ or $C$
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

Adding $C$, check against any pre-existing $pre$, $D$, or $X$
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
 = return $ A pre mD $ mergeSet S.intersection c mC
\end{code}

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
 = SC { fresh :: VarSet
      , varSCs :: VarSCMap}
 deriving (Eq,Ord,Show,Read)
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
\newpage
\subsection{Internal Test Export}

\subsubsection{Test values}
\begin{code}
v_a = StdVar $ PreVar $ Id "a"
v_b = StdVar $ PreVar $ Id "b"

s0 = S.fromList [] :: VarSet
sa = S.fromList [v_a]
sb = S.fromList [v_b]
sab = S.fromList [v_a,v_b]

v_e = PreExpr $ Id "e"
v_f = PreExpr $ Id "f"
\end{code}

\subsubsection{Tests}
\begin{code}
-- TBD
\end{code}


\subsubsection{Exported Test Group}
\begin{code}
test_AST :: [TF.Test]
test_AST
 = [ testGroup "\nSide Condition Conflicts (AST.mergeSideCond)"
     [
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
\end{code}
