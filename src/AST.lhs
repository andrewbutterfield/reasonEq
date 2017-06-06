\section{Abstract Syntax}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module AST ( Name
           , Identifier, ident, idName
           , VarRole, pattern NoRole
           , pattern Before, pattern During, pattern After
           , Variable
           , pattern StaticVar
           , pattern ObsVar, pattern ExprVar, pattern PredVar
           , pattern PreVar, pattern MidVar, pattern PostVar
           , pattern PreCond, pattern PostCond
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
           ) where
import Data.Char
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

ident :: Monad m => Name -> m Identifier
ident nm@(c:cs)
 | isAlpha c && all isIdContChar cs  = return $ Id nm
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
 = K TermKind Value -- value
 | V TermKind Variable -- variable
 | C TermKind Identifier [Term] -- constructor
 | B TermKind Identifier VarList Term -- binder
 | S TermKind Term (Substn Term) -- substitution
 | I TermKind Identifier Identifier [ListVar]
 deriving (Eq, Ord, Show, Read)
\end{code}


In \cite{UTP-book} we find the notion of texts, in chapters 6 and 10.
We can represent these using this proposed term concept,
so they don't need special handling or representation.



\newpage

\subsection{OLD DATATYPES}

EVERYTHING BELOW HERE IS FROM OLD Saoithin/UTP2.


\subsection{Types}


\newpage
\subsection{Type-Tables}
When we do type-inference,
we need to maintain tables mapping variables to types.
Given the presence of binders/quantifiers,
these tables need to be nested.
We shall use integer tags to identify the tables:
\begin{verbatim}
type TTTag = Int
\end{verbatim}

At each level we have a table mapping variables to types,
and then we maintain a master table mapping type-table tags to such
tables:
\begin{verbatim}
type VarTypes = [(String,Type)]  -- Trie Type            -- Var -+-> Type
type TVarTypes = [(String,Type)] -- Trie Type            -- TVar -+-> Type
type TypeTables = [(TTTag,VarTypes)] -- Btree TTTag VarTypes
\end{verbatim}
Quantifiers induce nested scopes which we capture as a list of
type-table tags. Tag 0 is special and always denotes the topmost global
table.


\newpage
\subsection{Terms}

We can posit a very general notion of terms ($t$),
within which we can also embed some other term syntax ($s$).
Terms are parameterised by a notion of constants ($k$)
and with some fixed notion of variables ($v$)
and a distinct notion of \emph{names} ($n$).
\begin{eqnarray*}
   n &\in& Names
\\ k &\in& Constants
\\ v &\in& Variables
\\ \ell &\in& GenVar
\\ vs \in VarList &=& (v | \ell)^*
\\ s &\in& Syntax (other)
\\ t \in Term~k~s
   &::=& k
\\ & | & v
\\ & | & n(t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t)
\\ & | & t[t,\dots,t/v,\dots,v]
\\ & | & [s]
\end{eqnarray*}

So, we expect to have two mutually recursive instantiations
of terms: Expressions ($E$) and Predicates ($P$).
\begin{eqnarray*}
   E &\simeq& Term~\Int~P
\\ P &\simeq& Term~\Bool~E
\end{eqnarray*}

We need to consider zippers.
For term alone, assuming fixed $s$:
\begin{eqnarray*}
   t' \in Term'~k~s
   &::=& n(t,\dots,t,[\_]t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t,[\_]t,\dots,t)
\\ & | & \_[t,\dots,t/v,\dots,v]
\\ & | & t[t,\dots,t,[\_]t,\dots,t/v,\dots,v,v,v,\dots,v]
\end{eqnarray*}
Intuitively, if we have descended into $s$, then
we should have $s'$ here.
So we really have:
\begin{eqnarray*}
   t' \in Term'~k~s
   &::=& n(t,\dots,t [\_]t,\dots,t)
\\ & | & n~vs~@ (t,\dots,t [\_]t,\dots,t)
\\ & | & \_[t,\dots,t/v,\dots,v]
\\ & | & t[t,\dots,t,[\_]t,\dots,t/v,\dots,v,v,v,\dots,v]
\\ & | & [s']
\end{eqnarray*}


\newpage
\subsection{Expressions}

We have a very simple expression abstract syntax
\begin{verbatim}
data Expr
 = Num Int
 | Var Variable
 | App String [Expr]
 | Abs String TTTag VarList [Expr]
 | ESub Expr ESubst
 | EPred Pred
 deriving (Eq, Ord, Show)


n_Eerror = "EXPR_ERR: "
eerror str = App (n_Eerror ++ str) []

type ESubst = Substn Variable ListVar Expr
\end{verbatim}

We need some builders that perform
tidying up for corner cases:
\begin{verbatim}
mkEsub e ([],[]) = e
mkEsub e sub = ESub e sub
\end{verbatim}


\newpage
\subsection{Predicates}

Again, a very simple abstract syntax,
but with the add of a typing hook,
and an explicit 2-place predicate construct.
\begin{verbatim}
data Pred
 = TRUE
 | FALSE
 | PVar Variable
 | PApp String [Pred]
 | PAbs String TTTag VarList [Pred]
 | Sub Pred ESubst
 | PExpr Expr
 | TypeOf Expr Type
 | P2 String ListVar ListVar
 deriving (Eq, Ord, Show)



type PSubst = Substn Variable ListVar Pred
\end{verbatim}

We define two constructor functions to handle
the \texttt{Expr}/\texttt{Pred} ``crossovers'':
\begin{verbatim}
ePred (PExpr e)             =  e
ePred (PVar v)              =  Var v
ePred (Sub (PExpr e) sub)   =  ESub e sub
ePred pr                    =  EPred pr

pExpr (EPred pr)            =  pr
pExpr (Var v)               =  PVar v
pExpr (ESub (EPred pr) sub) =  Sub pr sub
pExpr e                     =  PExpr e
\end{verbatim}

We also define smart constructors for certain constructs
to deal with corner cases.

THIS NEEDS TO GO TO A SPECIAL "builtins" MODULE

\begin{verbatim}
n_Not = "Not"
mkNot p = PApp n_Not [p]

n_And = "And"
mkAnd [] = TRUE
mkAnd [pr] = pr
mkAnd prs = PApp "And" prs

n_Or = "Or"
mkOr [] = FALSE
mkOr [pr] = pr
mkOr prs = PApp "Or" prs

n_Eqv = "Eqv"
mkEqv pr1 pr2 = PApp n_Eqv [pr1,pr2]

n_Forall = "Forall"
mkForall ([]) p = p
mkForall qvs p = PAbs "Forall" 0 qvs [p]

n_Exists = "Exists"
mkExists ([]) p = p
mkExists qvs p = PAbs "Exists" 0 qvs [p]

n_Exists1 = "Exists1"
mkExists1 ([]) p = FALSE
mkExists1 qvs p = PAbs "Exists1" 0 qvs [p]

n_Univ = "Univ"
mkUniv p =  PAbs n_Univ 0 [] [p]

mkSub p ([],[]) = p
mkSub p sub = Sub p sub

n_Pforall = "Pforall"
mkPforall ([]) p  = p
mkPforall qvs p = PAbs "Pforall" 0 qvs [p]

n_Pexists = "Pexists"
mkPexists ([]) p  = p
mkPexists qvs p = PAbs "Pexists" 0 qvs [p]

n_Peabs = "Peabs"
mkPeabs ([]) p  = p
mkPeabs qvs p = PAbs "Peabs" 0 qvs [p]

n_Equal = "Equal"
mkEqual e1 e2 = App n_Equal [e1,e2]
\end{verbatim}
Some query functions:
\begin{verbatim}
isObs (PExpr _) = True
isObs _       = False
\end{verbatim}

variables, and then ``all the rest''.

\newpage
\subsection{Observation Variables}

UTP is based on the notion of alphabetised predicates,
which we support by maintaining information about
variables in the alphabet.
In addition to alphabet membership,
it is useful to be able to distinguish observation variables
that corresponds to program/specification variables ($Script$),
and those that describe other aspects of a languages behaviour ($Model$),
capturing the peculiarities of a given semantic model%
\footnote{
Often referred to in the literature, as \emph{auxiliary} variables
}.
\begin{verbatim}
data OClass = Model | Script deriving (Eq,Ord,Show)

type ObsKind = (Variable,OClass,Type)
\end{verbatim}

\newpage
\subsection{Side-Conditions}

A side-condition is a syntactic property,
and therefore in principle ought to be statically checkable.
\begin{verbatim}
data MType = ObsM | TypeM | ExprM | PredM deriving (Eq,Ord,Show)

data SideCond
 = SCtrue
 | SCisCond MType String                     -- Mvar
 | SCnotFreeIn MType [Variable] String       -- Qvars, Mvar
 | SCareTheFreeOf MType [Variable] String    -- Qvars, Mvar
 | SCcoverTheFreeOf MType [Variable] String  -- Qvars, Mvar
 | SCfresh MType Variable                    -- ObsM for now
 | SCAnd [SideCond]
 deriving (Eq,Ord,Show)
\end{verbatim}
