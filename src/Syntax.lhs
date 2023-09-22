delimContClosed\section{Concrete Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017-2022

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Syntax ( BasicComp
              , pattern AnySyn,  pattern VarSyn, pattern TypeSyn
              , pattern ExprSyn, pattern PredSyn
              , SimpleForm
              , pattern SimpleForm, simpleform
              , LengthConstraint, pattern LenConstraint
              , FormSpec
              , pattern SimpleSpec, pattern IterateSpec
              , nullFormSpec, defaultFormSpec
              , OpnCls
              , pattern Open, pattern Closed
              , SyntaxSpec
              , pattern ClosedMixfix, pattern DelimContainer, pattern NameAppl
              , pattern OpenFixed, pattern OpenIterated
              , pattern DelimOpen, pattern DelimClosed
              , delimOpen, delimClosed
              , ConcreteForm
              , pattern ConcreteForm
              , closedMixfix
              , delimContOpen, delimContClosed
              , nameApplication
              , openFixed
              , openIterated
              , nullConcrete
              , defaultConcrete
              , int_tst_Syntax
              ) where
import Data.Maybe (fromJust)
import qualified Data.Map as M

import YesBut
import Utilities
import LexBase

import Test.HUnit
import Test.Framework as TF (defaultMain, testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)
--import Test.Framework.Providers.QuickCheck2 (testProperty)
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
simpleform :: (Monad m, MonadFail m) => [BasicComp] -> m SimpleForm
simpleform []  =  fail "Syntax.simpleform: empty basic-comp list."
simpleform bs  =  return $ SF bs
\end{code}

Tests:
\begin{code}
simpleFormTests
 = [ testCase "Empty Simple-Form (Fail)"
     ( simpleform []
       @?=  But ["Syntax.simpleform: empty basic-comp list."])
   , testCase "Singleton Simple-Form (Ok)"
     ( simpleform [AnySyn]
       @?= Yes (SF [AnySyn]) )
   ]
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
    of a fixed length or arbitrary length.
    This always has a name as its first term,
    and all we need to do is provide a simple form for the argument-list,
    if it has a fixed length, or a basic component and length constraints
    if the length is arbitrary.
    \\ Example (1) : $f(a,b,c)$
    \\ Arguments Form: three expressions $\seqof{E,E,E}$.
    \\ Example (2) : $and(P,Q,R,...)$
    \\ Arguments Form: a basic component ($P$)
       and a constraint $\mbox{length} \geq 2$.
\end{description}
We want to keep form distinct from concrete syntax,
so all that we observe for now is that all three of the above cases
have the simple form, while the third can also be a basic component
plus a length constraint.
\begin{code}
data LengthConstraint = LC Ordering Int deriving (Eq,Ord,Show,Read)
pattern LenConstraint ord i = LC ord i
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
    $f~a_1~a_2~ \dots ~a_k, \quad k \leq A+1$, where $A$ is the arity of $f$.
    \\Form: a basic component ($E$) and a constraint $\mbox{length} \leq A+1$.
\end{description}
An open-form specification is one of the two cases above,
with a simple form in the first case,
and basic component plus a length constraint in the second.


\newpage
\subsubsection{Form Specification}

A form specification is either a simple form,
or a list of basic components with a length constraint.
\begin{code}
data FormSpec
 = FS SimpleForm
 | FI BasicComp LengthConstraint
 deriving (Eq,Ord,Show,Read)

pattern SimpleSpec  sf     =  FS sf
pattern IterateSpec bc lc  =  FI bc lc

nullFormSpec     =  IterateSpec AnySyn $ LenConstraint EQ 0
defaultFormSpec  =  IterateSpec AnySyn $ LenConstraint GT (-1)
\end{code}
Test values:
\begin{code}
anything = FS (SF [AnySyn])
\end{code}



\subsection{Concrete Syntax Specification}

Given a FormSpec, we also want a way to describe its concrete syntax.
In effect this amounts to describing
which lexical tokens can occur ``around'' the terms that make up the construct.

We saw earlier that closed-form syntax has
three different cases,
while open-form syntax has two.
This gives us five different syntactic idioms we need to describe:
\begin{description}
  \item[Closed-mixfix:]
    An interleaving of specific tokens with particular kinds of terms.
    It has a simple form and we have to specify a list of tokens
    whose length is one greater than that of the simple form.
    \\
    Example:
    $\textbf{if } c \textbf{ then } s_1 \textbf{ else } s_2 \textbf{ endif}$
    \\Form: an expression followed by two predicates: $\seqof{E,P,P}$.
    \\Syntax: $\seqof{\texttt{if},\texttt{then},\texttt{else},\texttt{endif}}$
  \item[Delimited-container:]
    A collection of grouped terms with three tokens that act as seperator,
    and left- and right-delimiters.
    It has a simple form that describes a term-group,
    and we have to specify the syntax of that group as well as three
    tokens, giving the start and finish delimiters, and the group separator.
    The group itself can either have closed-mixfix or open-fixed syntax.
    \\Example: $[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]$
    \\Group Form: a variable followed by an expression $\seqof{V,E}$.
    \\Group Syntax: open-fixed, $\seqof{\mapsto}$
    \\Collection Syntax: $\seqof{\texttt{[},\texttt{,},\texttt{]}}$
    \\We need to be able to mark delimited groups as open or closed:
\begin{code}
data OpnCls = OPN | CLS deriving (Eq,Ord,Show,Read)
pattern Open = OPN
pattern Closed = CLS
\end{code}
  \item[Name-application:]
    A variable followed immediately by a delimited container
    of a fixed length or arbitrary length.
    This always has a variable/name as its first term,
    and all we need to do is provide a simple form for the argument-list,
    if it has a fixed length, or a basic component and length constraints
    if the length is arbitrary.
    \\ Example (1) : $f(a,b,c)$
    \\ Arguments Form: three expressions $\seqof{E,E,E}$.
    \\ Syntax: $\seqof{\texttt{f},\texttt{(},\texttt{,},\texttt{)}}$
    \\ Example (2) : $and(P,Q,R,...)$
    \\ Arguments Form: a basic component ($P$)
       and a constraint $\mbox{length} \geq 2$.
    \\ Syntax: $\seqof{\texttt{and},\texttt{(},\texttt{,},\texttt{)}}$
  \item[Open-fixed:]
    An interleaving of particular kinds of terms,
    with specific tokens.
    It has a simple form and we have to specify a list of tokens
    whose length is one less than that of the simple form.
    \\
    Example: $P \cond c Q$
    \\Form: an expression in between two predicates: $\seqof{P,E,P}$.
    \\Syntax: $\seqof{\lhd,\rhd}$
  \item[Open-Iterated:]
    A list of terms of the same kind, with some possible length constraints.
    We have to specify a single token, that is interspersed among the terms.
    \\
    Example (1):
    $P_1 \land P_2 \land \dots \land P_n$
    \\ Form: a basic component ($P$) and a constraint $\mbox{length} \geq 2$.
    \\ Syntax: $\land$.
    Example (2):
    $f~a_1~a_2~ \dots ~a_k, \quad k \leq A+1$, where $A$ is the arity of $f$.
    \\Form: a basic component ($E$) and a constraint $\mbox{length} \leq A+1$.
    \\Syntax: \textvisiblespace (whitespace).
\end{description}
\newpage
This leads to the following concrete syntax specifier:
\begin{code}
data SyntaxSpec
 = CM [Token]           -- Closed Mixfix
 | DC                   -- Delimited Container
      OpnCls [Token]      -- group syntax
      Token Token Token   -- l. delim., sep., r. delim.
 | NA                   -- Name Application
      Token               -- nameApplication
      Token Token Token   -- l. delim., sep., r. delim.
 | OF [Token]           -- Open Fixed
 | OI Token             -- Open Iterated
 deriving (Eq,Ord,Show,Read)

pattern ClosedMixfix toks = CM toks
pattern DelimContainer oc toks ldelim sep rdelim = DC oc toks ldelim sep rdelim
pattern NameAppl nm ldelim sep rdelim = NA nm ldelim sep rdelim
pattern OpenFixed toks = OF toks
pattern OpenIterated tok = OI tok

pattern DelimOpen   toks ldelim sep rdelim <- DC Open   toks ldelim sep rdelim
pattern DelimClosed toks ldelim sep rdelim <- DC Closed toks ldelim sep rdelim

delimOpen, delimClosed :: [Token] -> Token -> Token -> Token -> SyntaxSpec
delimOpen   toks ldelim sep rdelim = DelimContainer Open   toks ldelim sep rdelim
delimClosed toks ldelim sep rdelim = DelimContainer Closed toks ldelim sep rdelim
\end{code}
Test tokens:
\begin{code}
t1 = IdTok $ fromJust $ ident "t1"
t2 = IdTok $ fromJust $ ident "t2"
t3 = IdTok $ fromJust $ ident "t3"
t4 = IdTok $ fromJust $ ident "t4"
t5 = IdTok $ fromJust $ ident "t5"
t6 = IdTok $ fromJust $ ident "t6"
tnorm = ArbTok "|"
t12 =[t1,t2]
t123 = [t1,t2,t3]
\end{code}

\newpage
\subsection{Form with Concrete Syntax}

We want to bring a form specification together with
a syntax specification.
\begin{code}
data ConcreteForm = XF FormSpec SyntaxSpec deriving (Eq,Ord,Show,Read)
pattern ConcreteForm fs ss <- XF fs ss
\end{code}
We define six constructor functions, that check arguments.

\subsubsection{Closed-Mixfix Concrete Form}
\begin{code}
closedMixfix :: (Monad m, MonadFail m) => FormSpec -> [Token] -> m ConcreteForm
closedMixfix (IterateSpec _ _) _
 = fail "Syntax.closedMixfix: not compatible with the iteration form."
closedMixfix fs@(SimpleSpec (SimpleForm sf)) toks
 | ltoks /= lsf + 1  = fail ( "Syntax.closedMixfix: #toks("
                            ++ show ltoks
                            ++ ") is not #form("
                            ++ show lsf
                            ++ ")+1." )
 | hasdup toks  =  fail "Syntax.closedMixfix: duplicate tokens not allowed."
 | otherwise    =  return $ XF fs $ ClosedMixfix toks
 where
    lsf = length sf
    ltoks = length toks
\end{code}
We note that the rule about duplicate tokens is perhaps a little
too strict---it outlaws syntax like $|x|$.

Tests:
\begin{code}
closedMixfixTests
 = testGroup "Syntax.closedMixfix"
    [ testCase "Try for Iteration Spec. (Fail)"
      ( closedMixfix defaultFormSpec [] @?=
        But ["Syntax.closedMixfix: not compatible with the iteration form."] )
    , testCase "Incorrect Token count (Fail)"
      ( closedMixfix anything [t1] @?=
        But ["Syntax.closedMixfix: #toks(1) is not #form(1)+1."] )
    , testCase "Duplicate tokens (Fail)"
      ( closedMixfix anything [t1,t1] @?=
        But ["Syntax.closedMixfix: duplicate tokens not allowed."] )
    , testCase "Singleton Spec (Ok)"
      ( closedMixfix anything t12 @?=
        Yes (XF anything $ ClosedMixfix t12) )
    , testCase "'norm' notation (Fail, but should be OK!)"
      ( closedMixfix (SimpleSpec (SF [ExprSyn])) [tnorm,tnorm] @?=
        But ["Syntax.closedMixfix: duplicate tokens not allowed."] )
    ]
\end{code}

\newpage
\subsubsection{Delimited Container (Open) Concrete Form}
\begin{code}
delimContOpen :: (Monad m, MonadFail m) => FormSpec
              -> [Token] -> Token -> Token -> Token
              -> m ConcreteForm
delimContOpen (IterateSpec _ _) _ _ _ _
 = fail "Syntax.delimContOpen: not compatible with the iteration form."
delimContOpen fs@(SimpleSpec (SimpleForm sf)) toks ldelim sep rdelim
 | ltoks /= lsf - 1  = fail ( "Syntax.delimContOpen: #toks("
                            ++ show ltoks
                            ++ ") is not #form("
                            ++ show lsf
                            ++ ")-1." )
 | hasdup (ldelim:sep:rdelim:toks)
                =  fail "Syntax.delimContOpen: duplicate tokens not allowed."
 | otherwise    =  return $ XF fs $ DelimContainer Open toks ldelim sep rdelim
 where
    lsf = length sf
    ltoks = length toks
\end{code}

Tests:
\begin{code}
delimContOpenTests
 = testGroup "Syntax.delimContOpen"
    [ testCase "Try for Iteration Spec. (Fail)"
      ( delimContOpen defaultFormSpec [] t1 t2 t3 @?=
        But ["Syntax.delimContOpen: not compatible with the iteration form."] )
    , testCase "Incorrect Token count (Fail)"
      ( delimContOpen anything [t1] t2 t3 t4 @?=
        But ["Syntax.delimContOpen: #toks(1) is not #form(1)-1."] )
    , testCase "Duplicate tokens (Fail)"
      ( delimContOpen anything [] t3 t4 t3 @?=
        But ["Syntax.delimContOpen: duplicate tokens not allowed."] )
    , testCase "Singleton spec (Ok)"
      ( delimContOpen anything [] t3 t4 t5 @?=
        Yes (XF anything $ DelimContainer Open [] t3 t4 t5) )
    ]
\end{code}


\newpage
\subsubsection{Delimited Container (Closed) Concrete Form}
\begin{code}
delimContClosed :: (Monad m, MonadFail m) => FormSpec
                -> [Token] -> Token -> Token -> Token
                -> m ConcreteForm
delimContClosed (IterateSpec _ _) _ _ _ _
 = fail "Syntax.delimContClosed: not compatible with the iteration form."
delimContClosed fs@(SimpleSpec (SimpleForm sf)) toks ldelim sep rdelim
 | ltoks /= lsf + 1  = fail ( "Syntax.delimContClosed: #toks("
                            ++ show ltoks
                            ++ ") is not #form("
                            ++ show lsf
                            ++ ")+1." )
 | hasdup (ldelim:sep:rdelim:toks)
                =  fail "Syntax.delimContClosed: duplicate tokens not allowed."
 | otherwise    =  return $ XF fs $ DelimContainer Closed toks ldelim sep rdelim
 where
    lsf = length sf
    ltoks = length toks
\end{code}

Tests:
\begin{code}
delimContClosedTests
 = testGroup "Syntax.delimContClosed"
    [ testCase "Try for Iteration Spec. (Fail)"
      ( delimContClosed defaultFormSpec [] t1 t2 t3 @?=
        But ["Syntax.delimContClosed: not compatible with the iteration form."] )
    , testCase "Incorrect Token count (Fail)"
      ( delimContClosed anything [t1] t2 t3 t4 @?=
        But ["Syntax.delimContClosed: #toks(1) is not #form(1)+1."] )
    , testCase "Duplicate tokens (Fail)"
      ( delimContClosed anything t12 t3 t4 t2 @?=
        But ["Syntax.delimContClosed: duplicate tokens not allowed."] )
    , testCase "Singleton spec (Ok)"
      ( delimContClosed anything t12 t3 t4 t5 @?=
        Yes (XF anything $ DelimContainer Closed t12 t3 t4 t5) )
    ]
\end{code}


\newpage
\subsubsection{Name Application Concrete Form}
\begin{code}
nameApplication :: (Monad m, MonadFail m) => FormSpec
                -> Token -> Token -> Token -> Token
                -> m ConcreteForm
nameApplication fs nm ldelim sep rdelim
 | hasdup [nm,ldelim,sep,rdelim]
       =  fail "Syntax.nameApplication: duplicate tokens not allowed."
 | otherwise    =  return $ XF fs $ NameAppl nm ldelim sep rdelim
\end{code}

Tests:
\begin{code}
nameApplTests
 = testGroup "Syntax.nameApplication"
    [ testCase "Duplicate tokens (Fail)"
      ( nameApplication anything t3 t4 t3 t5 @?=
        But ["Syntax.nameApplication: duplicate tokens not allowed."] )
    , testCase "Singleton Simple Form (Ok)"
      ( nameApplication anything t1 t3 t4 t5 @?=
        Yes (XF anything $ NameAppl t1 t3 t4 t5) )
    , testCase "Iteration Form (Ok)"
      ( nameApplication defaultFormSpec t1 t3 t4 t5 @?=
        Yes (XF defaultFormSpec $ NameAppl t1 t3 t4 t5) )
    ]
\end{code}

\newpage
\subsubsection{Open Fixed Concrete Form}
\begin{code}
openFixed :: (Monad m, MonadFail m) => FormSpec -> [Token] -> m ConcreteForm
openFixed (IterateSpec _ _) _
 = fail "Syntax.openFixed: not compatible with the iteration form."
openFixed fs@(SimpleSpec (SimpleForm sf)) toks
 | ltoks /= lsf - 1  = fail ( "Syntax.openFixed: #toks("
                            ++ show ltoks
                            ++ ") is not #form("
                            ++ show lsf
                            ++ ")-1." )
 | hasdup toks  =  fail "Syntax.openFixed: duplicate tokens not allowed."
 | otherwise    =  return $ XF fs $ OpenFixed toks
 where
    lsf = length sf
    ltoks = length toks
\end{code}

Tests:
\begin{code}
openFixedTests
 = testGroup "Syntax.openFixed"
    [ testCase "Try for Iteration Spec. (Fail)"
      ( openFixed defaultFormSpec [] @?=
        But ["Syntax.openFixed: not compatible with the iteration form."] )
    , testCase "Incorrect Token count (Fail)"
      ( openFixed anything [t1] @?=
        But ["Syntax.openFixed: #toks(1) is not #form(1)-1."] )
    , testCase "Singleton spec (Ok)"
      ( openFixed anything [] @?=
        Yes (XF anything $ OpenFixed []) )
    ]
\end{code}



\newpage
\subsubsection{Open Iterated Concrete Form}
\begin{code}
openIterated :: (Monad m, MonadFail m) => FormSpec -> Token -> m ConcreteForm
openIterated (SimpleSpec _) _
 = fail "Syntax.openIterated: not compatible with the simple form."
openIterated fs@(IterateSpec _ _) tok
 = return $ XF fs $ OpenIterated tok
\end{code}

Tests:
\begin{code}
openIteratedTests
 = testGroup "Syntax.openIterated"
    [ testCase "Try for Simple Spec. (Fail)"
      ( openIterated anything t1 @?=
        But ["Syntax.openIterated: not compatible with the simple form."] )
    , testCase "Singleton spec (Ok)"
      ( openIterated defaultFormSpec t1 @?=
        Yes (XF defaultFormSpec $ OpenIterated t1) )
    ]
\end{code}

Special Values:
\begin{code}
nullConcrete = XF nullFormSpec $ OpenIterated tnull

tnull = ArbTok ""

defaultConcrete nm
  = XF defaultFormSpec $ NameAppl (ArbTok nm) tlbr tcomma trbr

tlbr   = ArbTok "("
tcomma = ArbTok ","
trbr   = ArbTok ")"

concreteTests
 = testGroup "Special ConcreteForm Values"
    [ testCase "'Null' Concrete"
       ( Yes nullConcrete @?= openIterated nullFormSpec tnull )
    , testCase "'Default' Concrete"
       ( Yes (defaultConcrete "") @?=
         nameApplication defaultFormSpec tnull tlbr tcomma trbr )
    ]
\end{code}

\newpage
\subsection{Exported Test Group}
\begin{code}
int_tst_Syntax :: [TF.Test]
int_tst_Syntax
 = [ testGroup "\nSyntax Internal"
     simpleFormTests
   , closedMixfixTests
   , delimContOpenTests
   , delimContClosedTests
   , nameApplTests
   , openFixedTests
   , openIteratedTests
   , concreteTests
   ]
\end{code}
