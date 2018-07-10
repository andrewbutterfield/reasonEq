\section{Abstract User-Interface}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module AbstractUI
( REqState
, observeLogic, observeTheories, observeCurrTheory, observeCurrConj
, observeLiveProofs, observeCompleteProofs
)
where

import REqState
\end{code}

\subsection{Introduction}

We produce an abstract user-interface layer that wraps
around the proof-state as encapsulated in \texttt{REqState}.
The idea is that these functions are called by all concrete UIs,
either REPL-based or graphical.

There should be no direct link from a concrete UI to \texttt{REqState}.
For now this is a long-term goal.

We can break this abstract user-interface down into two main parts:
the first provides ways to observe the proof-state,
whilst the second supports modifications to that state.

\subsection{Observing Proof-State}

The first issue to address here is in what form such observations
should be returned over an abstract interface,
remembering that the caller might be graphical, textual, or something else.
Possibilities range from returning text of some form,
through to actual data-structures.
However return, for example, a \texttt{Term},
requires the concrete UI to also have access to concrete ways to
handle and render terms.
This may not be an optimal `separation of concerns`.
Given that pretty-printing terms will be important, we may want
some form of structured text.
We also need to allow for the fact that the UI may use the observation structure
as a way to get user input for a subsequent modify operation.

In general we propose that observer functions will support
a number of return formats.

\subsubsection{Observing Current Logic}

\begin{code}
observeLogic :: REqState -> String
observeLogic reqs = showLogic $ logic reqs
\end{code}

\subsubsection{Observing Theories}

\begin{code}
observeTheories :: REqState -> String
observeTheories reqs = showTheories $ theories reqs
\end{code}

\subsubsection{Observing Current Theory}

\begin{code}
observeCurrTheory :: REqState -> String
observeCurrTheory reqs = currTheory reqs
\end{code}

\subsubsection{Observing Current Conjectures}

\begin{code}
observeCurrConj :: REqState -> String
observeCurrConj reqs
  = case getTheoryConjectures currThNm (theories reqs) of
      Nothing ->  ("Invalid current theory: '"++currThNm++"'")
      Just conjs -> showNmdAssns conjs
  where currThNm = currTheory reqs
\end{code}

\subsubsection{Observing Live Proofs}

\begin{code}
observeLiveProofs :: REqState -> String
observeLiveProofs reqs = showLiveProofs $ liveProofs reqs
\end{code}


\subsubsection{Observing Completed Proofs}

\begin{code}
observeCompleteProofs :: REqState -> String
observeCompleteProofs reqs
  = case getTheoryProofs currThNm (theories reqs) of
      Nothing ->  ("Invalid current theory: '"++currThNm++"'")
      Just proofs -> showProofs proofs
  where currThNm = currTheory reqs
\end{code}

\subsection{Modifying Proof-State}