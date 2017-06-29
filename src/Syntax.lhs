\section{Concrete Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Syntax ( BasicComp
              , pattern AnySyn,  pattern VarSyn, pattern TypeSyn
              , pattern ExprSyn, pattern PredSyn
              , SimpleForm
              , pattern SimpleForm, simpleform
              , ClosedFormKind
              , LengthConstraint, pattern LenConstraint
              , pattern ClosedMixfix, pattern DelimContainer, pattern NameAppl
              , FormSpec
              , pattern CMixfix, pattern DelimC, pattern NAppl
              , pattern OFixed, pattern ORepeat
              , nullFormSpec, defaultFormSpec
              , ConstructSpec(..)
              , defaultConstructSpec
              , ConstructSpecTable
              ) where
import Data.Maybe (fromJust)
import qualified Data.Map as M

import LexBase
import AST
\end{code}

\subsection{Syntax Introduction}

Here we define ways to specify concrete syntaxes,
such as a plain ASCII form,
or perhaps one using Unicode,
or more elaborate forms such as \LaTeX, or Mathjax.
One issue addressed here,
that is independent of the choice of conrete renderings just discussed,
is how to specify the \emph{form} of various named constructs.
All these constructs have an identifier component,
and the key idea is that it is used to lookup customisable information
about that construct's \emph{concrete syntax}.
In the event of no such custom information existing,
a default approach is adopted.

\subsection{Diversity of Forms}

In our abstract syntax,
we have basically three ways to represent composite terms:
constructor applications; the two kinds of binders; and substitution.
Binders and substitutions are straightforward:
in the ordered binder ($L$) the given ordering of the variable-list
is semantically significant, and so must be preserved in the representation;
whereas in the un-ordered binder ($B$) and the subsitution,
the ordering of the variable- and substitution-lists
have no semantic significance,
and so are always represented by a list ordered by some fixed canonical order.

For the constructor construct ($C$), the picture is more complicated.
This will used to represent things as diverse as logic connectives,
target language syntactic forms, partial function applications,
operators of fixed arity, etc\dots.
We need a general, straightforward way to specify the appropriate form,
for a given identifier.

Here we have examples of the range of forms we might encounter:
\begin{mathpar}
P \land Q

P \equiv Q \equiv R

F(P,Q)

\rho : \mathbb N^*

f(x,y)

f~x~y

\{ 1, 2, 3, 4, 5 \}

[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]

P \cond c Q

\bigcap_{i \in 1 \dots k} R_i

x := e

\textbf{while } c \textbf{ do } \{ s_1 ; s_2 \}

\textbf{for } ( i :=0 | i \leq n | \textsf{inc}~i)\textbf{ do }+ f(i)
\end{mathpar}
We have a mixture of constructs with a fixed number of positions,
each containing a specific kind of term (e.g., $x:=e$ or $P \cond c Q$),
and those that take an arbitrary number of terms of the same kind
(e.g., $\{ 1, 2, 3, 4, 5 \}$),
or even arbitrary numbers of some kind of ``term-cluster''
(e.g., $[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]$).

We note that while binders are simpler,
as they only have one term sub-component,
we still need to be able to specify aspects of their concrete syntax,
as exemplified by the following examples:
\begin{mathpar}
\exists x,y,\lst z \bullet  P

\lambda \lst a,b \bullet e

(+ v ~|~  v < 42 : v^2 )
\end{mathpar}

\subsection{Specifying Forms}

We want to write form specifications whose semantics are
a set of sequences built over basic components that match that form.
Howevever a general approach to this tends to result in specifications
that are easy to \emph{verify} (check that a given list of terms is correct),
and easy to \emph{render}
(generate the correct concrete syntax from a correct list of terms),
but are very difficult to \emph{parse}
(identify and extract from an putative instance of concrete syntax).
Instead we find that we need an abstraction that identifies a number
of common idiomatic forms, that cover the vast range of concrete syntaxes
in use, without guaranteeing complete generality.

Note however, that there is an important separation of concerns here.
The form that a construct can take
is essentially a structural semantics notion.
Any given construct instance must satisfy this structural semantics,
but may be written with different concrete syntax in different situations.
While the need for feasible parsing requires us to describe possible
form specifications using idioms, it does not mean that the form and concrete syntax are essentially the same.

Consider the following simple example, that of the logical-and construct.
Idiommatically we specify this an associative binary operator,
whose form is a list of predicates of length at least two:
\[
   \mbox{``And''} :  Pred^*,  \mbox{length} \geq 2
\]
However, the logical-and of the three predicates $P$, $Q$, and $R$,
could have many concrete forms, not all of which need use an infix notation:
\[
\begin{array}{c}
   P \land Q \land R
\\ And(P,Q,R)
\end{array}
\]

\subsubsection{Open and Closed Forms}

We start by observing that most syntactic idioms can be
classified on a ``open/closed'' spectrum.
A fully closed idiom is one where the syntactic construct starts
and ends with distinguished tokens. Examples include:
\begin{mathpar}
\{ 1, 2, 3, 4, 5 \}

[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]

\textbf{begin }  s_1 ; s_2 ; \dots ; s_n \textbf{ end}

(+ v ~|~  v < 42 : v^2 )
\end{mathpar}
A fully open idiom is a construct that can both start and end with
an arbitrary term, e.g.:
\begin{mathpar}
P \land Q

P \equiv Q \equiv R

\rho : \mathbb N^*

f~x~y

P \cond c Q

x := e
\end{mathpar}
We can also have constructs that are half-and-half, such as:
\begin{mathpar}
F(P,Q)

f(x,y)

\textbf{while } c \textbf{ do } \{ s_1 ; s_2 \}

\textbf{for } ( i :=0 | i \leq n | \textsf{inc}~i)\textbf{ do }+ f(i)

\exists x,y,\lst z \bullet  P

\lambda \lst a,b \bullet e
\end{mathpar}
Interestingly, these are all left-closed,
except for the first one, ``traditional function application'',
which is right-closed.
We have a notion of semi-closed/semi-open too,
where the starting and/or  finishing term is not arbitrary,
but is instead drawn from a restricted set of terms built
from a single token of a designated kind,
usually being identifiers or names.
Examples here can include the following,
where $F$, $f$ and $x$ are restricted to being identifiers,
and not arbitrary terms.
\begin{mathpar}
F(P,Q)

f(x,y)

f~x~y

x := e
\end{mathpar}

\subsubsection{Basic Components}

We assume all forms are built from basic components of four kinds:
variables ($V$); types ($T$); expressions ($E$); and predicates ($P$).
\begin{eqnarray*}
   c \in BasicComp &::=& X ~|~ V ~|~ T ~|~ E ~|~ P
\end{eqnarray*}
where $X$ is a wildcard allowing any kind of term.
\begin{code}
data BasicComp = CX | CV | CT | CE | CP deriving (Eq,Ord,Show,Read)
pattern AnySyn   =  CX
pattern VarSyn   =  CV
pattern TypeSyn  =  CT
pattern ExprSyn  =  CE
pattern PredSyn  =  CP
\end{code}

We will introduce the idea of a ``simple form''
as a (typically short) non-empty sequence of basic components.
\begin{code}
newtype SimpleForm = SF [BasicComp] deriving (Eq,Ord,Show,Read)
pattern SimpleForm bs <- SF bs
simpleform :: Monad m => [BasicComp] -> m SimpleForm
simpleform []  =  fail "Syntax.simpleform: empty basic-comp list."
simpleform bs  =  return $ SF bs
\end{code}

\subsubsection{Specifying Closed Forms}

Closed, and some left semi-closed forms are easy to specify
in a manner that makes them parseable.
They can either be expressed as:
\begin{description}
  \item[Closed-mixfix:]
    An interleaving of specific tokens with particular kinds of terms.
    This is specified as a simple form.
    \\
    Example:
    $\textbf{if } c \textbf{ then } s_1 \textbf{ else } s_2 \textbf{ endif}$
    \\Form: an expression followed by two predicates: $\seqof{E,P,P}$.
  \item[Delimited-container:]
    A collection of grouped terms with three tokens that act as seperator,
    and left- and right-delimiters.
    This is specified with a simple form describing the term-group.
    \\
    Example: $[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]$
    \\Group Form: a variable followed by an expression $\seqof{V,E}$.
  \item[Name-application:]
    A variable followed immediately by a delimited container
    of a fixed length.
    This always has a variable as its first term,
    and all we need to do is provide a simple form for the argument-list
    \\
    Example: $f(a,b,c)$
    \\ Arguments Form: three expressions $\seqof{E,E,E}$.
\end{description}
We see that a closed-form specification identifies
one of the three cases above, along with the required simple form.
\begin{code}
data ClosedFormKind
 = CM  -- Closed Mixfix
 | DC  -- Delimited Container
 | NA  -- Name Application
 deriving (Eq,Ord,Show,Read)
pattern ClosedMixfix = CM
pattern DelimContainer = DC
pattern NameAppl = NA
\end{code}

\subsubsection{Specifying Open Forms}

Open forms arise mainly from the use of infix operator symbols.
Less common are bracket-free function application,
and open mixfix notations.
In any case we really only have two variations:
\begin{description}
  \item[Open-fixed:]
    An interleaving of particular kinds of terms,
    with specific tokens.
    This is specificed as a simple form.
    \\
    Example: $P \cond c Q$
    \\Form: an expression in between two predicates: $\seqof{P,E,P}$.
  \item[Open-Iterated:]
    A list of terms of the same kind, with some possible length constraints.
    \\
    Example (1):
    $P_1 \land P_2 \land \dots \land P_n$
    \\ Form: a basic component ($P$) and a constraint $\mbox{length} \geq 2$.
    \\
    Example (2):
    $f~a_1~a_2~ \dots ~a_k, \quad k \leq A$, where $A$ is the arity of $f$.
    \\Form: a basic component ($E$) and a constraint $\mbox{length} \leq A$.
\end{description}
An open-form specification is one of the two cases above,
with a simple form in the first case,
and basic component plus a length constraint in the second.
\begin{code}
data LengthConstraint = LC Ordering Int deriving (Eq,Ord,Show,Read)
pattern LenConstraint ord i = LC ord i
\end{code}




\subsubsection{Form Specification}

A form specification is either closed, or open.
\begin{code}
data FormSpec
 = CS ClosedFormKind SimpleForm
 | OF SimpleForm
 | OI BasicComp LengthConstraint
 deriving (Eq,Ord,Show,Read)

pattern CMixfix sf    = CS ClosedMixfix   sf
pattern DelimC  sf    = CS DelimContainer sf
pattern NAppl   sf    = CS NameAppl       sf
pattern OFixed  sf    = OF                sf
pattern ORepeat bc lc = OI bc lc

nullFormSpec     =  ORepeat AnySyn $ LenConstraint EQ 0
defaultFormSpec  =  ORepeat AnySyn $ LenConstraint GT (-1)
\end{code}



\subsection{Concrete Syntax Specification}

Given a FormSpec, we also want a way to describe its concrete syntax.
In effect this amounts to describing
which lexical tokens can occur ``around'' the terms that make up the construct.


\subsection{Complete Construct Specifications}

A complete specification of a construct consists of its \texttt{FormSpec},
and its \texttt{TermKind}.
If it is an expression,
the type associated with it can be arbitrary (\texttt{T}),
or can specify more detail, if required.
\begin{code}
data ConstructSpec = XS TermKind FormSpec deriving (Eq,Ord,Show,Read)
\end{code}
We define a default construct specification, as one that defines a predicate:
\begin{code}
defaultConstructSpec :: ConstructSpec
defaultConstructSpec = XS P defaultFormSpec
\end{code}

\subsection{Recording Construct Specifications}

We keep a table, indexed by identifiers,
that records construct specifications.
\begin{code}
type ConstructSpecTable = M.Map Identifier ConstructSpec
\end{code}
In practise, we expect to have a list of such tables,
that we search front to back.
These arise because we have `layers' of theories,
each with its own scope, and corresponding tables.

We have a total lookup that returns the default specification
if it cannot find an entry for the supplied identifier:
\begin{code}
getConstructSpec :: [ConstructSpecTable] -> Identifier -> ConstructSpec
getConstructSpec [] _  =  defaultConstructSpec
getConstructSpec (cst:csts) i
 = case M.lookup i cst of
     Just cs  ->  cs
     Nothing  ->  getConstructSpec csts i
\end{code}

\newpage
\subsection{Constructing Forms}

Given an identifier, a construct specification, and a list of terms,
we want to build the relevant constructor term,
so long as it satisfies the specification:
\begin{code}
buildConstruct :: Monad m
               => ConstructSpec
               -> Identifier
               -> [Term]
               -> m Term
buildConstruct (XS tk fs) i ts =  fail "Syntax.buildConstruct: NYI"
\end{code}

\subsection{Concrete Syntax Specification}

Given an identifer associated with a form specification,
we also want to be able to give a description of a concrete way to
parse and render it.
