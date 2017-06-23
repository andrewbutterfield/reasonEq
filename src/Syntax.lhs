\section{Concrete Syntax}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Syntax (
              ) where
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
In the event of no such cusotm information existing,
a default approach is adopted.

\subsubsection{Diversity of Forms}

In our abstract syntax, we have basically three ways to represent composite terms:
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
(e.g., $\{ 1, 2, 3, 4, 5 \}$), or even arbitrary numbers of some kind of ``term-cluster'' (e.g., $[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]$).

\subsubsection{Specifying Forms}

We assume all forms are built from basic components of four kinds:
variables; types, expressions; and predicates.
We want to write form specifications whose semantics is a set of sequences built over basic components that match that form.
Given that the main distinction we seen between forms
is between those of fixed  and varying length,
we propose that a form is described as a preamble of a fixed length
followed by a postamble that can have either zero or an arbitrary length.
Our constructor form specification language is now defined as:
\begin{eqnarray*}
   c \in BasicComp &::=& V | T | E | P
\\ a \in Amble &::=& c^+
\\ p \in PostAmble &::=& \epsilon | a^* | a^+ | a^{2+}
\\ f \in FormSpec &::=&  c^*~p
\end{eqnarray*}
where $V$, $T$, $E$ and $P$ stand for the four basic component kinds,
while $N$ denotes an empty postamble, while $0$, $1$ and $2$
tag postambles with their minimum permitted length.
To illustrate, here are all the above examples with possible specifications:
$$\begin{array}{c@{\qquad}l}
   P \land Q
 & \seqof{}~P^{2+}
\\ P \land Q \land R
 & \seqof{}~P^{2+}
\\ \rho : \mathbb N^*
 & \seqof{V,T}~\epsilon
\\ \{ 1, 2, 3, 4, 5 \}
 & \seqof{}~E^*
\\ ~[ a \mapsto 97, b \mapsto 98, c \mapsto 99 ]
 & \seqof{}~\seqof{V,E}^*
\\ P \cond c Q
 & \seqof{P,E,P}~\epsilon
\\ \bigcap_{i \in 1 \dots k} R_i
 & \seqof{V,E,E,P}~\epsilon
\\ x := e
 & \seqof{V,E}~\epsilon
\\ \textbf{while } c \textbf{ do } \{ s_1 ; s_2 \}
 & \seqof{E,P}~\epsilon
\\ \textbf{for } ( i :=0 | i \leq n | \textsf{inc}~i)\textbf{ do } f(i)
 & \seqof{P,P,E,P}~\epsilon
\end{array}$$
