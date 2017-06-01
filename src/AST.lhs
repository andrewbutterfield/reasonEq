\section{Abstract Syntax}

\subsection{AST Introduction}

We start by giving an overview of the ``design space''
and noting some key implementation decisions we have to take.

\subsubsection{Terms}

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
Do we have mutually recursive datatypes or an explicit tag?

In \cite{UTP-book} we find the notion of texts, in chapters 6 and 10.
We can represent these using the proposed term concept,
so they don't need special handling or representation.

\subsubsection{Variables}

We want to implement a range of variables
that can stand for behaviour observations, and arbitrary terms.
We also want to support the notion of list-variables that denote lists of variables.

Variables are either:
\begin{description}
  \item[Static]
    that capture context-sensitive information that does not change during
    the lifetime of a program.
  \item[Dynamic]
    that represent behaviour
    with observations that change as the program runs.
    These can have added `decorations' that can limit their scope
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

\newpage
\begin{code}
module AST ( Name
           , Identifier, ident
           ) where
import Data.Char
\end{code}

\subsection{Naming}

We consider `names' to be arbitrary strings,
while `identifiers' are names that satisfy a fairly standard convention
for program variables, namely starting with an alpha character,
followed by zero of more alphas, digits and underscores.

\begin{code}
type Name = String

newtype Identifier = Identifier Name deriving (Eq, Ord)

ident :: Monad m => Name -> m Identifier
ident nm@(c:cs)
 | isAlpha c && all isIdContChar cs  = return $ Identifier nm
ident nm = fail ("'"++nm++"' is not an Identifier")

isIdContChar c = isAlpha c || isDigit c || c == '_'

instance Show Identifier where show (Identifier name) = name

instance Read Identifier where
  readsPrec _ name
    = do idnt <- ident name
         return (idnt,"")
\end{code}



\subsection{Variables}

A variable has a \emph{name}.
\begin{verbatim}
type Name = String -- no whitespace !
\end{verbatim}

A variable will have one of the following \emph{kinds}:
\begin{description}
  \item[Observational]
    Corresponds to some observation that can be made of a program,
    and hence belongs, in UTP,  to the alphabet of the corresponding predicate.
  \item[Schematic]
    Stands for an arbitrary chunk of abstract syntax,
    of which we recognise two broad classes:
    \begin{description}
      \item[Expression] denotes an arbitrary expression
      \item[Predicate] denotes an arbitrary predicate
    \end{description}
  \item[Script]
    Represents an actual program variable itself,
    rather than any associated value it may take.
\end{description}
The above kinds all have different roles in the logic underlying UTP.

\begin{verbatim}
data VKind = VObs
           | VExpr
           | VPred
           | VScript
           deriving (Eq, Ord, Show)
\end{verbatim}

In addition, with most of the variable kinds above,
we can associate one of the following \emph{roles}:
\begin{description}
  \item[Static]
    variables whose values a fixed for the life of a (program) behaviour
  \item[Dynamic]
    variables whose values are expected to change over the life of a behaviour.
    \begin{description}
      \item[Pre]
        variables that record the values taken when a behaviour starts
      \item[Post]
        variables that record the values taken when a behaviour ends
      \item[Relational]
        Expression or Predicate variables that denote relations
        between the start and end of behaviours.
      \item[Intermediate]
        indexed variables that record values that arise between successive behaviours
    \end{description}
\end{description}
These distinct roles do not effect how the underlying logic handles
variables, but are used to tailor definitional shorthands that
assume that these are enacting the relevant UTP variable conventions.

\begin{verbatim}
data VRole = VAny -- can play any role, useful for generic laws
           | VStatic
           | VPre
           | VPost
           | VRel          -- VExpr, VPred only
           | VInter String -- VObs, VList VObs only
           deriving (Eq, Ord, Show)
\end{verbatim}


A variable has a name, kind and role:
\begin{verbatim}
type Variable = ( Name
                , VKind
                , VRole
                )
\end{verbatim}

Invariant:
\begin{enumerate}
  \item only kinds \texttt{VExpr} and \texttt{VPred} can have role \texttt{VRel}.
  \item only kind \texttt{VObs} can have role \texttt{VInter}.
\end{enumerate}
\begin{verbatim}
invVariable reserved (name, kind, role, roots)
 = (role == VRel)    `implies`  (kind `elem` [VExpr,VPred])
   &&
   isVInter role     `implies`  (kind == VObs)

isVInter (VInter _) = True
isVInter _          = False

implies :: Bool -> Bool -> Bool
False `implies` _ = True
True `implies` b  = b
\end{verbatim}

We also need to introduce the idea of lists of variables,
for use in binding constructs,
which may themselves contain special variables
that denote lists of variables.
We start by defining a list-variable as a variable with the addition
of a list of names, corresponding to variable `roots'
\begin{verbatim}
type ListVar
 = ( Variable -- variable denoting a list of variables
   , [Name]   -- list of roots to be ignored)
   )
\end{verbatim}
A variable-list is composed in general of a mix of normal variables
and list-variables.
We gather these into a `general' variable type
\begin{verbatim}
data GenVar
 = V Variable -- regular variable
 | L ListVar  -- variable denoting a list of variables
 deriving (Eq, Ord, Show)
type VarList = [GenVar]
\end{verbatim}

\newpage
\subsection{Substitutions}

Substitutions associate a list of things (types,expressions,predicates)
with some (quantified) variables.
We also want to allow list-variables of the appropriate kind
to occur for things, but only when the target variable is also
a list variable.
\begin{verbatim}
type Substn v lv a
  =  ( [(v,a)]     -- target variable, then replacememt object
     , [(lv,lv)] ) -- target list-variable, then replacement l.v.
\end{verbatim}

\subsection{Types}

For now, type variables are strings:
\begin{verbatim}
type TVar = String
\end{verbatim}

The ordering of data-constructors here is important,
as type-inference relies on it.
\begin{verbatim}
data Type -- most general types first
 = Tarb
 | Tvar TVar
 | TApp String [Type]
 | Tfree String [(String,[Type])]
 | Tfun Type Type
 | Tenv
 | Z
 | B
 | Terror String Type
 deriving (Eq,Ord,Show)
\end{verbatim}

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
