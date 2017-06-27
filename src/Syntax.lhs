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
              , PostAmble
              , pattern NoPostamble, pattern Postamble, postamble
              , FormSpec(..)
              , pattern FormSpec
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
about how that construct should appear.
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

P \land Q \land R

\rho : \mathbb N^*

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

\subsection{Specifying Forms}

We assume all forms are built from basic components of four kinds:
variables; types, expressions; and predicates.
\begin{eqnarray*}
   c \in BasicComp &::=& X | V | T | E | P
\end{eqnarray*}
where $V$, $T$, $E$ and $P$ stand for the four basic component kinds,
and $X$ is a wildcard allowing any kind of term.
\begin{code}
data BasicComp = CX | CV | CT | CE | CP deriving (Eq,Ord,Show,Read)
pattern AnySyn   =  CX
pattern VarSyn   =  CV
pattern TypeSyn  =  CT
pattern ExprSyn  =  CE
pattern PredSyn  =  CP
\end{code}

We want to write form specifications whose semantics are a set of sequences built over basic components that match that form.
We start by defining an ``amble''
to be a non-empty sequence of basic components.
\begin{eqnarray*}
   a \in Amble &::=& c^+
\end{eqnarray*}
Given that the main distinction we seen between forms
is between those of fixed and varying length,
we propose that a form is described as a sequence of two parts:
an preamble of a fixed length, which can be zero, with the component kind at each location fixed;
followed by an optional postamble, which is a list of ``ambles'',
whose minimum length is also specified.
\begin{eqnarray*}
   p \in PostAmble &::=& a^0 | a^{m+}
\end{eqnarray*}
A postamble is either absent ($a^0$)
or we set its minimum permitted length to be $m$ ($a^{m+}$).
\begin{code}
data PostAmble
 = PZ                 -- No Postamble
 | PL Int [BasicComp] -- Postamble Min. length and Amble (non-empty)
 deriving (Eq,Ord,Show,Read)
pattern NoPostamble = PZ
pattern Postamble i cs <- PL i cs
postamble :: Monad m => Int -> [BasicComp] -> m PostAmble
postamble _ []  =  fail "Syntax.postamble: 'amble' cannot be empty."
postamble i cs
 | i < 0      =  return $ PL 0 cs
 | otherwise  =  return $ PL i cs
\end{code}

Our constructor form-specification language is now defined as
a pre-amble, followed by a post-amble,
that we seperate here with a bullet ($\bullet$) for clarity.
\begin{eqnarray*}
   f \in FormSpec &::=&  c^*~\bullet~p
\end{eqnarray*}
\begin{code}
data FormSpec
 = FS [BasicComp]  -- Preamble
      PostAmble
 deriving (Eq,Ord,Show,Read)
pattern FormSpec pre post = FS pre post
\end{code}
Note that it is possible to have a construct with no added terms:
\begin{code}
nullFormSpec :: FormSpec
nullFormSpec = FormSpec [] NoPostamble
\end{code}
To illustrate, here are all the above examples with possible specifications:
$$\begin{array}{c@{\qquad}l}
   P \land Q
 & \bullet~2~P
\\ P \land Q \land R
 & \bullet~2~P
\\ \rho : \mathbb N^*
 & V~T~\bullet
\\ \{ 1, 2, 3, 4, 5 \}
 & \bullet~0~E
\\ ~[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]
 & \bullet~0~V~E
\\ P \cond c Q
 & P~E~P~\bullet
\\ \bigcap_{i \in 1 \dots k} R_i
 & V~E~E~P~\bullet
\\ x := e
 & V~E~\bullet
\\ \textbf{while } c \textbf{ do } P
 & E~P~\bullet
\\ \textbf{for } ( i :=0 | i \leq n | \textsf{inc}~i)\textbf{ do } f(i)
 & P~P~E~P~\bullet
\end{array}$$
If no specification is provided for a construct,
then we use the default specification $\seqof{}~X^*$,
namely a list of zero or more arbitrary terms.
\begin{code}
defaultFormSpec :: FormSpec
defaultFormSpec = FormSpec [] $ fromJust $ postamble 0 [AnySyn]
\end{code}

\subsection{Concrete Syntax Specification}

Given a FormSpec, we also want a way to describe its concrete syntax.
In effect this amounts to describing
which lexical tokens can occur ``around'' the terms that make up the construct.
Let us consider the following general construct specification
\[
 c_1~c_2~\dots~c_p~m~c'_1~c'_2~\dots~c'_q
 \qquad p \geq 0, \quad q \geq 1
\]
where $c_i$ are the basic components of the preamble in order,
$m$ is the minimum repetition factor or the postamble,
and the $c'_j$ are the basic components of the post-amble.

A concrete syntax specification simply indicates which tokens get interspersed,
where tokens are basic lexical units, which,
for this purpose at least, may include whitespace.

\def\T{\mathtt{t}}
\[
 \T_{s}~c_1~\T_1~c_2~\T_3~\dots~\T_{p-1}~c_p
 ~\T_{m}~m~
 c'_1~\T'_1~c'_2~\T'_2~\dots~\T'_{q-1}~c'_q~\T_{e}
\]
Here $\T_s$, $\T_m$, $\T_r$ and $\T_e$ are the \textit{start},
\textit{mid}, \textit{repeat} and \textit{end} tokens, respectively.
The $\T_i$ and $\T'_i$ are the tokens
that occurr between the $i$th and $i+1$th components of the preamble
and the post-amble, respectively.
The token $\T_r$ occurs between each repetition of the post-amble.
If the preamble is null, then the $\T_i$ and $\T_m$ are ommitted.
If the postamble is null, then $\T_m$, the $\T'_j$ and $\T_r$ are ommitted.

To illustrate, here are all the above examples with corresponding
concrete syntax elements,
where whitespace tokens are shown as $\textvisiblespace$.
$$\begin{array}{c@{\qquad}l}
   P \land Q
 & \textvisiblespace~\bullet~2~P~\land~\textvisiblespace
\\ P \land Q \land R
 & \textvisiblespace~\bullet~2~P~\land~\textvisiblespace
\\ \rho : \mathbb N^*
 & \textvisiblespace~V~:~T~\bullet~\textvisiblespace
\\ \{ 1, 2, 3, 4, 5 \}
 & \{~\bullet~0~E~,~\}
\\ ~[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]
 & ~[~\bullet~0~V~\mapsto~E~,~]
\\ P \cond c Q
 & \textvisiblespace~P~\lhd~E~\rhd~P~\bullet~\textvisiblespace
\\ \bigcap_{i \in 1 \dots k} R_i
 & \bigcap~._s~V~._s\in~._s~E~._s\dots~._s~E~\textvisiblespace~P~\bullet~\textvisiblespace
\\ x := e
 & \textvisiblespace~V~:=~E~\bullet~\textvisiblespace
\\ \textbf{while } c \textbf{ do } P
 & \textbf{while}~E~\textbf{do}~P~\bullet~\textvisiblespace
\\ \textbf{for } ( i :=0 | i \leq n | \textsf{inc}~i)\textbf{ do } f(i)
 & \textbf{for}(~P~|~P~|~E~)\textbf{do}~P~\bullet~\textvisiblespace
\end{array}$$
We also have tokens $._s$ and $.^s$ that make the following term get rendered
in subscript or superscript form respectively.

\textbf{Hmmm. This looks very ``renderable'', but not at all ``parseable''!!}


\subsection{Complete Construct Specifications}

A complete specification of a construct consists of its \texttt{FormSpec},
and its \texttt{TermKind}.
If it is an expression,
the type associated with it can be arbitrary (\texttt{T}),
or can specify more detail, if required.
\begin{code}
data ConstructSpec = CS TermKind FormSpec deriving (Eq,Ord,Show,Read)
\end{code}
We define a default construct specification, as one that defines a predicate:
\begin{code}
defaultConstructSpec :: ConstructSpec
defaultConstructSpec = CS P defaultFormSpec
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
buildConstruct (CS tk fs) i ts
 | ts `sat` fs  =  return $ Cons tk i ts
 | otherwise    =  fail "Syntax.buildConstruct: construct spec. violation."
\end{code}
Construct satisfaction:
\begin{code}
sat :: [Term] -> FormSpec -> Bool
sat ts (FormSpec pre post)
 = case preWalk ts pre of
     Nothing   ->  False
     Just ts'  ->  case postWalk ts' post of
                     Nothing  ->  False
                     Just _   ->  True
\end{code}
Preamble ``walk'':
\begin{code}
preWalk :: Monad m => [Term] -> [BasicComp] -> m [Term]
preWalk [] []  =  return []
preWalk (t:ts) (c:cs)
 | t `csat` c  =  preWalk ts cs
 | otherwise   =  fail "Syntax.preWalk: preamble component mismatch."
preWalk _ _    =  fail "Syntax.preWalk: preamble length mismatch."
\end{code}
Postamble ``walk'':
\begin{code}
postWalk :: Monad m => [Term] -> PostAmble -> m [Term]
postWalk ts NoPostamble
 | null ts  =  return []
 | otherwise  =  fail "Syntax.postWalk: unexpected postamble."
postWalk ts (Postamble i cs)  =  ambleWalk cs i cs ts
\end{code}
``Amble-walk'':
\begin{code}
ambleWalk _   0 _      []      =  return []
ambleWalk cs0 0 (c:cs) (t:ts)
 | t `csat` c                  =  ambleWalk cs0 0 cs ts
 | otherwise                   =  fail "Syntax.ambleWalk: postamble comp. mismatch."
ambleWalk cs0 0 []     ts      =  ambleWalk cs0 0 cs0 ts
ambleWalk _   _ _      []      =  fail "Syntax.ambleWalk: terms end prematurely."
ambleWalk cs0 n []     ts      =  ambleWalk cs0 (n-1) cs0 ts
ambleWalk cs0 n (c:cs) (t:ts)
 | t `csat` c                  =  ambleWalk cs0 n cs ts
 | otherwise                   =  fail "Syntax.ambleWalk: postamble comp. mismatch."
\end{code}
Component satisfsaction:
\begin{code}
csat :: Term -> BasicComp -> Bool
_          `csat` AnySyn   =  True
(Var _ _)  `csat` VarSyn   =  True
(EVar _ _) `csat` ExprSyn  =  True
(Type _)   `csat` TypeSyn  =  True
t          `csat` ExprSyn  =  isExpr t
t          `csat` PredSyn  =  isPred t
_          `csat` _        =  False
\end{code}

\subsection{Concrete Syntax Specification}

Given an identifer associated with a form specification,
we also want to be able to give a description of a concrete way to
parse and render it.
