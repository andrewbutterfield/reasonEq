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
           , ListVar
           , pattern ObsLVar, pattern ExprLVar, pattern PredLVar
           , pattern PreVars, pattern PostVars, pattern MidVars
           , pattern PreExprs
           , GenVar, pattern StdVar, pattern LstVar
           , VarList
           , Substn
           , Type
           , pattern ArbType,  pattern TypeVar, pattern TypeApp
           , pattern DataType, pattern FunType, pattern GivenType
           , _NAME, nametype, _ENV, envtype
           , Text, Value, pattern Boolean, pattern Integer, pattern Text
           , TermKind(..)
           , Term
           , pattern EVal, pattern EVar, pattern ECons
           , pattern EBind, pattern ESub, pattern EIter
           , pattern PVal, pattern PVar, pattern PCons
           , pattern PBind, pattern PSub, pattern PIter
           , pattern E2, pattern P2
           , VarSet
           , FreeVarRel(..)
           , SideCond
           , pattern TrueC
           , pattern Fresh
           , pattern IsCond
           , pattern NotIn
           , pattern Is
           , pattern Covers
           , pattern AndC
           , scFresh, isTermVar, scIsCond, scNotIn, scIs, scCovers, scAnd
           , test_AST
           ) where
import Data.Char
import Data.List
import Data.Set(Set)
import qualified Data.Set as S

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
pattern PreVars  i    =  LO RB i []
pattern PostVars i    =  LO RA i []
pattern MidVars  i n  =  LO (RD n) i []
pattern PreExprs i    =  LE RB i []
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
  \item [B] A binding construct that introduces local variables.
  \item [S] A term with an explicit substitution of terms for variables.
  \item [I] An iteration of a term over a sequence of list-variables.
\end{description}
\begin{eqnarray}
   k &\in& Value
\\ n &\in& Name
\\ v &\in& Var = \dots
\\ t \in T  &::=&  K~k | V~n | C~n~t^* | B~n~v^+~t | S~t~(v,t)^+ | I~n~n~v^+
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
 | B TermKind Identifier VarList Term  -- Binder
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
pattern ESub t tm s = S (E t) tm s
pattern EIter t na ni lvs = I (E t) na ni lvs
\end{code}

Patterns for predicates:
\begin{code}
pattern PVal k = K P k
pattern PVar v = V P v
pattern PCons n ts = C P n ts
pattern PBind n vl tm = B P n vl tm
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

A side-condition is a syntactic property,
and therefore in principle ought to be statically checkable.
However, given expression and predicate variables this is not always
possible.

A side condition is about a relationship between the free variables
of an expression or predicate, itself denoted by a variable ($e$, $P$),
and a list (set!) of other (general) variables ($x,\lst v$)
The relationship can have the form:
\begin{eqnarray*}
   x,\lst v   \notin  \fv(e) \mbox{ or } \fv(P) && \mbox{disjoint}
\\ x,\lst v      =    \fv(e) \mbox{ or } \fv(P) && \mbox{exact}
\\ x,\lst v \supseteq \fv(e) \mbox{ or } \fv(P) && \mbox{covering}
\end{eqnarray*}
We represent variable sets as distinct from variable-lists:
\begin{code}
type VarSet = Set GenVar

overlaps :: Ord a => Set a -> Set a -> Bool
s1 `overlaps` s2 = not $ S.null (s1 `S.intersection` s2)
\end{code}
Let $D$, $X$ and $C$ denote sets of variables
that are meant to be be disjoint, exact, and covering respectively.
Let $F$ denote the free variables of the expression or predicate variable
under consideration.
\begin{code}
data FreeVarRel
 = FVD  -- "D" : disjoint, D and F do not overlap
 | FVX  -- "X" : exact, X = F
 | FVC  -- "C" : covering, C contains F
 deriving (Eq, Ord, Show, Read)
\end{code}

We also have requirements for fresh variables,
asserting that expressions and predicates have only pre-variables,
trivial true side-conditions, and conjunctions
of all of the above.
These conditions can conflict with each other,
and can also be simplfified by each others presence.
Let $N$ denote fresh (new) variables.
We also have an explicit false side-condition as a sentinel value.
\begin{code}
data SideCond
 = SCT            -- "T" : trivial/true
 | SCF VarSet     -- "N" : new/fresh, N does not occur free in matched term
                        -- set must be non-empty
 | SCC Variable   -- "c" : condition, F has no dashed vars,
                        -- variable must be VE, VP
 | SCR FreeVarRel -- "D", "X", or "C"
       VarSet           -- D, X, or C, non-empty for D, C
       Variable         -- VE, VP only
 | SCA [SideCond] -- "A" : non empty, non conflicting,
                        -- unique ordered SCF,SCC,SCR only
 | SCINVALID      -- "0" : invalid side-condition
 deriving (Eq,Ord,Show)
\end{code}

We want meaningful matches for \verb"SideCond":
\begin{code}
pattern TrueC = SCT                 -- T
pattern Fresh vs <- SCF vs          -- N
pattern IsCond v <- SCC v           -- c
pattern NotIn vs v <- SCR FVD vs v  -- D
pattern Is vs v <- SCR FVX vs v     -- X
pattern Covers vs v <- SCR FVC vs v -- C
pattern AndC scs <- SCA scs         -- A
\end{code}

Useful to have predicates as well:
\begin{code}
isFresh :: SideCond -> Bool
isFresh (Fresh _) = True
isFresh _         = False
\end{code}

Invariant preserving builders:
\begin{code}
scFresh :: VarList -> SideCond
scFresh [] = TrueC
scFresh vl = SCF $ S.fromList vl

isTermVar :: Variable -> Bool
isTermVar v@(VE _ _) = True
isTermVar v@(VP _ _) = True
isTermVar _          = False

scIsCond :: Variable -> SideCond
scIsCond v
 | isTermVar v  =  SCC v
 | otherwise    =  SCINVALID

scNotIn :: VarList -> Variable -> SideCond
scNotIn vl v
 | not (isTermVar v)  =  SCINVALID
 | null vl            =  TrueC  -- D is empty, so always disjoint !
 | otherwise          =  SCR FVD (S.fromList vl) v

scIs :: VarList -> Variable -> SideCond
scIs vl v
 | not (isTermVar v)  =  SCINVALID
 | otherwise          =  SCR FVX (S.fromList vl) v

scCovers :: VarList -> Variable -> SideCond
scCovers vl v
 | not (isTermVar v)  =  SCINVALID
 | null vl            =  SCR FVX (S.fromList vl) v
 | otherwise          =  SCR FVC (S.fromList vl) v

scAnd :: [SideCond] -> SideCond
scAnd [] = TrueC
scAnd scs
 | flattened == [TrueC]  =  TrueC
 | otherwise  = case mergeSideConds $ sort flattened of
                 []    -> SCINVALID
                 [sc'] -> sc'
                 scs'  -> SCA scs'
  where flattened = flattenSCAnds scs
\end{code}

\subsubsection{Flattening \texttt{SCAnds}.}

\begin{code}
flattenSCAnds :: [SideCond] -> [SideCond]
flattenSCAnds []                =  []
flattenSCAnds t@[TrueC]         =  t
flattenSCAnds (SCINVALID :scs)  =  []
flattenSCAnds ((SCA scas):scs)  =  (flattenSCAnds scas) ++ flattenSCAnds scs
flattenSCAnds ( TrueC    :scs)  =  flattenSCAnds scs
flattenSCAnds ( sc       :scs)  =  sc : flattenSCAnds scs
\end{code}

\subsubsection{Side Condition Conflicts}

Here we use $D$, $X$, $C$, $N$, to represent themselves
and be a shorthand for $D \cap F = \emptyset$,
$X = F$, $F \subseteq C$,
and $fresh(N)$ respectively.
Which is which should be clear from context.

\begin{eqnarray*}
   N_1 \land N_2 &=& N_1 \cup N_2
\\ D_1 \land D_2 &=& D_1 \cup D_2
\\ X_1 \land X_2 &=& X_1 = X_2 \;\land\; X_1
\\ C_1 \land C_2 &=& C_1 \cap C_2
\\
\\ N_1 \land X_2 &=& N_1 \cap X_2 = \emptyset \;\land\; N_1 \;\land\; X_1
\\ N_1 \land C_2 &=& N_1 \cap C_1 = \emptyset \;\land\; N_1 \;\land\; C_1
\\ D_1 \land X_2 &=& D_1 \cap X_2 = \emptyset \;\land\; X_2
\\ D_1 \land C_2 &=& C_2 \not\subseteq D_1 \;\land\; D_1 \;\land\; (C_2 \setminus D_1)
\\ X_1 \land C_2 &=& X_1 \subseteq C_2 \;\land\; X_1
\end{eqnarray*}

We start with a function to merge two non-\verb"SCAnd" \verb"SideCond",
that returns a list, because we can have between zero and two results inclusive.
\begin{code}
mergeSideCond :: SideCond -> SideCond -> [SideCond]

-- Invalid Handling:  C /\ 0 = 0
mergeSideCond sc1 SCINVALID = []
mergeSideCond SCINVALID sc2 = []

-- SCT Handling:  C /\ T = C
mergeSideCond sc1 TrueC = [sc1]
mergeSideCond TrueC sc2 = [sc2]

-- SCC Handling:  iscond(v) /\ iscond(v) = iscond(v)
mergeSideCond sc1@(IsCond v1) (IsCond v2)
 | v1 == v2  =  [sc1]
mergeSideCond sc1 sc2@(IsCond _)  =  [sc1,sc2]

-- SCF Handling: N1 /\ N2 = N1 U N2
mergeSideCond (Fresh vs1) (Fresh vs2) = [SCF (vs1 `S.union` vs2)]
-- SCF Handling: X /\ N =  disjoint(X,N) /\ X /\ N
mergeSideCond sc1@(vs1 `Is` v) sc2@(Fresh vs2)
 | vs1 `overlaps` vs2  =  []
 | otherwise           = [sc1,sc2]
-- SCF Handling: C /\ N =  disjoint(C,N) /\ C /\ N
mergeSideCond sc1@(vs1 `Covers` v) sc2@(Fresh vs2)
  | vs1 `overlaps` vs2  =  []
  | otherwise           = [sc1,sc2]
mergeSideCond sc1 sc2@(Fresh _)  =  [sc1,sc2]

-- SCR of different variables don't interact
mergeSideCond sc1@(SCR _ _ v1) sc2@(SCR _ _ v2)
 | v1 /= v2  =  [sc1,sc2]
-- v1 == v2 everywhere below

-- SCR FVD Handling: D1 /\ D2 = D1 U D2
mergeSideCond sc1@(vs1 `NotIn` v1) sc2@(vs2 `NotIn` v2)
 = [SCR FVD (vs1 `S.union` vs2) v1]
-- SCR FVD Handling: D /\ X = disjoint(D,X) /\ X
mergeSideCond sc1@(vs1 `NotIn` v1) sc2@(vs2 `Is` v2)
 | vs1 `overlaps` vs2  =  []
 | otherwise  =  [sc2]
-- SCR FVD Handling: D /\ C = not(C<= D) /\ D /\ (C\D)
mergeSideCond sc1@(vs1 `NotIn` v1) sc2@(vs2 `Covers` v2)
 | vs2 `S.isSubsetOf` vs1  =  []
 | otherwise  =  [sc1,SCR FVC (vs2 `S.difference` vs1) v1]

-- SCR FVX Handling: X1 /\ X2 = X1 = X2 /\ X1
mergeSideCond sc1@(vs1 `Is` _) sc2@(vs2 `Is` _)
 | vs1 == vs2  = [sc1]
 | otherwise  =  []
-- SCR FVX Handling: X /\ C = X <= C /\ X
mergeSideCond sc1@(vs1 `Is` _) sc2@(vs2 `Covers` _)
 | vs1 `S.isSubsetOf` vs2  = [sc1]
 | otherwise  =  []

-- SCR FVC Handling: C1 /\ C2 = C1 intersect C2
mergeSideCond sc1@(vs1 `Covers` v1) sc2@(vs2 `Covers` _)
 | S.null vs'  =  []
 | otherwise   =  [SCR FVC vs' v1]
 where vs' = vs1 `S.intersection` vs2

-- atomic side-conditions only
mergeSideCond _ (AndC _) = []
mergeSideCond sc1 sc2 = mergeSideCond sc2 sc1
\end{code}

Function \verb"mergeFold" reduces a non-empty list of side-conditions to a single one,
provided all the side-conditions are so-reducible.
\begin{code}
mergeFold :: [SideCond] -> SideCond
mergeFold []   = TrueC
mergeFold [sc] = sc
mergeFold (sc:scs)
 = case mergeSideCond sc $ mergeFold scs of
     []      -> SCINVALID
     (sc':_) -> sc'
\end{code}


We use \verb"mergeSideCond" to implement a function
to merge a sorted list of atomic side-conditions,
where neither \verb"SCINVALID" nor \verb"TrueC" occur.
We first partition the given list into sub-lists: one containing all \verb"SCF",
the others, for each \verb"ExprVar" and \verb"PredVar" found in the list,
containing all the \verb"SCC" and \verb"SCR" referring to that variable.
We merge all the \verb"SCF" into one, and then add that onto the front of the other variable-specific lists. Each of which is then systematically merged.
What remains, if no conflicts are found, is merged and sorted.
\begin{code}
mergeSideConds :: [SideCond] -> [SideCond]
mergeSideConds scs
 = let
   (ns,vscs) = span isFresh scs
   n' = mergeFold ns
   in (n':vscs)
\end{code}

\subsubsection{Side Condition Invariant}

We have some non-trivial invariants here.

\newpage
\subsection{Internal Test Export}

\subsubsection{Test values}
\begin{code}
t = TrueC

v_a = StdVar $ PreVar $ Id "a"
v_b = StdVar $ PreVar $ Id "b"

s0 = S.fromList [] :: VarSet
sa = S.fromList [v_a]
sb = S.fromList [v_b]
sab = S.fromList [v_a,v_b]

n1 = SCF sa
n2 = SCF sb
n12 = SCF sab

v_e = PreExpr $ Id "e"
v_f = PreExpr $ Id "f"

cd1 = SCC v_e
cd2 = SCC v_f

x0  = SCR FVX s0 v_e
x1  = SCR FVX sa v_e
x2  = SCR FVX sb v_e
x2f = SCR FVX sb v_f
x12 = SCR FVX sab v_e

c1  = SCR FVC sa v_e
c2  = SCR FVC sb v_e
c2f = SCR FVC sb v_f
c12 = SCR FVC sab v_e


d1  =  SCR FVD sa v_e
d2  =  SCR FVD sb v_e
d2f = SCR FVD sb v_f
d12 = SCR FVD sab v_e
\end{code}

\subsubsection{Tests}
\begin{code}
-- Invalid SC Handling:  sc /\ 0 = 0
test_C0
 = testCase "SCINVALID is right-zero" (mergeSideCond n1 SCINVALID @?= [])
test_0C
 = testCase "SCINVALID is left-zero" (mergeSideCond SCINVALID n1 @?= [])

-- SCT Handling:  sc /\ T = sc
test_CT = testCase "TrueC is right-identity" (mergeSideCond n1 t @?= [n1])
test_TC = testCase "TrueC is left-identity" (mergeSideCond t n1 @?= [n1])

-- SCC Handling:  iscond(v) /\ iscond(v) = iscond(v)
test_cc
 = testCase "IsCond is self-Idempotent" (mergeSideCond cd1 cd1 @?= [cd1])
test_c1c2
 = testCase "IsCond is Independent" (mergeSideCond cd1 cd2 @?= [cd1,cd2])

-- SCF Handling: N1 /\ N2 = N1 U N2
test_NN
 = testCase "Fresh is self-Idempotent" (mergeSideCond n1 n1 @?= [n1])
test_N1N2
 = testCase "Fresh merges with Union (1)" (mergeSideCond n1 n2 @?= [n12])
test_N2N1
 = testCase "Fresh merges with Union (2)" (mergeSideCond n2 n1 @?= [n12])

-- SCF Handling: X /\ N =  disjoint(X,N) /\ X /\ N
test_XN0
 = testCase "Is left-conflicts with Fresh" (mergeSideCond x1 n1 @?= [])
test_NX0
 = testCase "Fresh left-conflicts with Is" (mergeSideCond n1 x1 @?= [])
test_XN
 = testCase "Is left-compatible with Fresh" (mergeSideCond x1 n2 @?= [x1,n2])
test_NX
 = testCase "Fresh left-compatible with Is" (mergeSideCond n2 x1 @?= [x1,n2])

-- SCF Handling: C /\ N =  disjoint(C,N) /\ C /\ N
test_CN0 = testCase "Covers left-conflicts with Fresh"
                    (mergeSideCond c1 n1 @?= [])
test_NC0 = testCase "Fresh left-conflicts with Covers"
                    (mergeSideCond n1 c1 @?= [])
test_CN  = testCase "Covers left-compatible with Fresh"
                    (mergeSideCond c1 n2 @?= [c1,n2])
test_NC  = testCase "Fresh left-compatible with Covers"
                    (mergeSideCond n2 c1 @?= [c1,n2])

-- SCR FVD Handling: D1 /\ D2 = D1 U D2
test_DD
 = testCase "NotIn merges with union" (mergeSideCond d1 d2 @?= [d12])

-- SCR FVD Handling: D /\ X = disjoint(D,X) /\ X
test_XD0
 = testCase "Is left-conflicts with NotIn" (mergeSideCond x1 d1 @?= [])
test_DX0
 = testCase "NotIn left-conflicts with Is" (mergeSideCond d1 x1 @?= [])
test_XD
 = testCase "Is left-subsumes NotIn" (mergeSideCond x1 d2 @?= [x1])
test_DX
 = testCase "Is right-subsumes NotIn" (mergeSideCond d2 x1 @?= [x1])

-- SCR FVD Handling: D /\ C = not (C <= D) /\ D /\ (C\D)
test_CD0
 = testCase "Covers left-conflicts with NotIn" (mergeSideCond c1 d12 @?= [])
test_DC0
 = testCase "NotIn left-conflicts with Covers" (mergeSideCond d12 c1 @?= [])
test_CD
 = testCase "Covers left-subsumes NotIn" (mergeSideCond c12 d2 @?= [d2,c1])
test_DC
 = testCase "Covers right-subsumes NotIn" (mergeSideCond d2 c12 @?= [d2,c1])

-- SCR FVX Handling: X1 /\ X2 = X1 = X2 /\ X1
test_XX0
 = testCase "Is conflicts if different" (mergeSideCond x1 x2 @?= [])
test_XX
 = testCase "Is OK if identical" (mergeSideCond x1 x1 @?= [x1])

-- SCR FVX Handling: X /\ C = X <= C /\ X
test_XC0
 = testCase "Is left-conflicts with Covers" (mergeSideCond x12 c1 @?= [])
test_CX0
 = testCase "Covers left-conflicts with Is" (mergeSideCond c1 x12 @?= [])
test_XC
 = testCase "Is left-subsumes Covers" (mergeSideCond x1 c12 @?= [x1])
test_CX
 = testCase "Is right-subsumes Covers" (mergeSideCond c12 x1 @?= [x1])

-- SCR FVC Handling: C1 /\ C2 = C1 intersect C2
test_CC0
 = testCase "Covers conflicts if disjoint" (mergeSideCond c1 c2 @?= [])
test_CC
 = testCase "Covers merge with intersection" (mergeSideCond c12 c1 @?= [c1])

-- SCR of different variables don't interact
test_D1X2 = testCase "Diff. Vars Independent (NotIn,Is)"
                     (mergeSideCond d1 x2f @?= [d1,x2f])
test_X2D1 = testCase "Diff. Vars Independent (Is,NotIn)"
                     (mergeSideCond x2f d1 @?= [x2f,d1])
test_D1C2 = testCase "Diff. Vars Independent (NotIn,Covers)"
                     (mergeSideCond d1 c2f @?= [d1,c2f])
test_C2D1 = testCase "Diff. Vars Independent (Covers,NotIn)"
                     (mergeSideCond c2f d1 @?= [c2f,d1])
\end{code}


\subsubsection{Exported Test Group}
\begin{code}
test_AST :: [TF.Test]
test_AST
 = [ testGroup "\nSide Condition Conflicts (AST.mergeSideCond)"
     [
       test_C0, test_0C, test_CT, test_TC, test_cc, test_c1c2
     , test_NN, test_N1N2, test_N2N1
     , test_XN0, test_NX0, test_XN, test_NX
     , test_CN0, test_NC0, test_CN, test_NC
     , test_DD
     , test_XD0, test_DX0, test_XD, test_DX
     , test_CD0, test_DC0, test_CD, test_DC
     , test_XX0, test_XX
     , test_XC0, test_CX0, test_XC, test_CX
     , test_CC0, test_CC
     , test_D1X2, test_X2D1, test_D1C2, test_C2D1
     ]
{-  , testGroup "QuickCheck Ident"
     [
       testProperty "Idents Always" prop_ident
     ] -}
   ]
\end{code}
