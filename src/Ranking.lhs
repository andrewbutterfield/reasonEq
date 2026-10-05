\chapter{Term and Match Ranking}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2017--26
           Saqib Zardari (c) 2023

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Ranking
  ( Ranking
  -- exported Filters
  , acceptAll, acceptNone -- used in ProofSettings
  , isTrivialMatch-- used in ProofSettings
  , onlyTrivialLVarMatches -- used in ProofSettings
  , anyTrivialSubstitutions -- used in ProofSettings
  , hasFloatingVariables -- used in ProofSettings
  -- exported Orderings
  , sizeOrd -- not used
  , favourDefLHSOrd -- used in ProverTUI
  -- exported rankings
  , filterAndSort -- used in ProverTUI
  , sizeRanking -- not used
  , favouriteRanking -- not used
  , termSize
  , Direction(..), ClassifiedLaws(..), nullClassifiedLaws
  , catClassyLaws
  , addClassyLaws
  , checkIsComp, checkIsSimp, checkIsFold, checkIsUnFold
  )
where

import Data.List (sortOn)
import qualified Data.Set as S

import Utilities
import Variables
import LexBase
import AST
import Binding
import Assertions
import Laws
import Proofs
import Instantiate
import ProofMatch
import TestRendering

import Debugger
mtdbg msg mtchs = trc (msg++":\n"++unlines (map mdetails mtchs)) mtchs
mdetails mtch
   = mName mtch
     ++ " @ " ++ showMatchClass (mClass mtch)
     ++ " -->  " ++ trTerm 0 (mRepl mtch)
\end{code}

\section{Ranking Types}

Ranking involves two phases: filtering, and ordering.
Filtering is using a predicate to decide what matches to consider
for ranking.
Ordering is done by computing a $n$-tuple of values ($n \geq 1$),
to be used in sorting comparisons.
The values should belong to a type that has an instance of \texttt{Ord},
so that the tuple itself is also an instance of \texttt{Ord}.
All filtering and ordering is done with access to matching contexts.
\begin{code}
type Ranking = Matches -> Matches
\end{code}


\newpage
\section{Filters}

\subsection{Accept All/None}

\begin{code}
acceptAll, acceptNone :: ProofMatch -> Bool
acceptAll  _  =  True
acceptNone _  =  False
\end{code}



\subsection{Pathological Cases}

Some matches are quite pathological in character,
and usually we want to suppress these.
Sometimes, however, they are useful.

We provide some predicates here that identify specific pathologies.
All of these are disabled by default.

\subsubsection{Trivial Matches}

Matches against a single predicate variable
\begin{code}
isTrivialMatch :: ProofMatch -> Bool
isTrivialMatch m
  = trivial $ mClass m
  where
     trivial (MatchEqvVar _)  =  True
     trivial _                =  False
\end{code}

\subsubsection{Vanishing List Variables}

All pattern list-variables
are mapped to empty sets or lists.
\begin{code}
onlyTrivialLVarMatches :: ProofMatch -> Bool
onlyTrivialLVarMatches mtch
  =  onlyTrivialListVarBindings (mBind mtch)
\end{code}

\subsubsection{Accept Empty Substitutions}

Matches that contain empty substitutions ($t[/]$).
\begin{code}
anyTrivialSubstitutions :: ProofMatch -> Bool
anyTrivialSubstitutions  =  anyTrivialSubstitution . mRepl
\end{code}

\subsection{Accept Floating Matches}

Some matches to one part of a law will not cover all the variables
in the other (replacement) part.
Sometimes we need these matches, sometimes they are a distraction.
\begin{code}
hasFloatingVariables :: ProofMatch -> Bool
hasFloatingVariables  =  any isFloatingGVar . mentionedVars . mRepl
\end{code}
If floating variables are enabled (the default),
they will also be subject to the screening above for pathological matches.


\newpage
\section{Orderings}

In orderings, smaller is better.

\subsection{Term Size}

Term Sizes
\begin{code}
termSize :: Term -> Int
termSize (Val _ _)            =  1
termSize (Var _ _)            =  1
termSize (Cons _ _ _ ts)      =  1 + sum (map termSize ts)
termSize (Bnd _ _ vs t)       =  2 + S.size vs + termSize t
termSize (Lam _ _ vl t)       =  2 + length vl + termSize t
termSize (Cls _ t)            =  1 + termSize t
termSize (Sub _ t subs)       =  1 + termSize t + subsSize subs
termSize (Iter _ _ _ _ _ vl)  =  3 + length vl
termSize (VTyp _ _)           =  2

subsSize (Substn ts lvs)      =  3 * S.size ts + 2 * S.size lvs
\end{code}



Simple ranking by replacement term size,
after the binding is applied:
\begin{code}
sizeOrd :: ProofMatch ->  Int
sizeOrd  =  termSize . mRepl 
\end{code}


\subsection{Favour LHS and Definitions}

Show matches to laws named as definitions first,
then those matching LHS of equivalence laws,
and then the rest.
Key exceptions: replacement \h{true} trumps definitions.
\begin{code}
favourDefLHSOrd :: ProofMatch ->  (Int,Int,Int,Int)
favourDefLHSOrd m
  = ( subMatchRepl $ mRepl m
    , subMatchDef $ mName m
    , subMatchOrd $ mClass m
    , sizeOrd m
    )

subMatchRepl :: Term -> Int
subMatchRepl term
  | term == theTrue  =  0
  | term == theFalse =  0
  | otherwise        =  1


subMatchDef :: String -> Int
subMatchDef lawname
 | take 4 (reverse lawname) == "fed_"  =  0
 | otherwise                           =  1

subMatchOrd :: MatchClass -> Int
subMatchOrd MatchAll         =  0
subMatchOrd MatchEqvLHS      =  1
subMatchOrd MatchEqvRHS      =  2
subMatchOrd (MatchEqv _)     =  2
subMatchOrd MatchAnte        =  3
subMatchOrd MatchCnsq        =  3
subMatchOrd (MatchEqvVar _)  =  3
\end{code}

\newpage
\section{Ranking Match Lists}

Simple sorting according to rank,
with duplicate replacements removed
(this requires us to instantiate the replacements).

\begin{code}
filterAndSort :: Ord ord
              => ( ProofMatch -> Bool, ProofMatch ->  ord )
              -> Matches -> Matches
filterAndSort (ff,rf) ms
  = let fms = filter ff ms
    in remDupRepl $ map snd $ sortOn fst $ zip (map rf fms) fms
  where  
    mshow m = 
      mName m 
      ++ "(" 
      ++ show (mClass m)
      ++ ")  --  "
      ++ trTerm 0 (mRepl m)
\end{code}

Note: given the same instantiated replacement from different laws,
we want the most general law, 
which is found in the theory furthest down the theory SDAG
(closest to \h{Equiv}).
We do this because ``lower'' theories are more stable so lessening the risk
that the proof will break%
\footnote{
 This will only matter when we get to the point of replaying proofs to check them
 }%
.
\begin{code}
remDupRepl :: Matches -> Matches
remDupRepl []       =  []
remDupRepl [m]  =  [m]
remDupRepl (m1:rest@(m2:ms))
  | sameRepl m1 m2  =       remDupRepl (m2:ms) -- prefer "earlier" laws
  | otherwise       =  m1 : remDupRepl rest

sameRepl :: ProofMatch -> ProofMatch -> Bool
sameRepl m1 m2 = mRepl m1 == mRepl m2
\end{code}

\section{Rankings}

\subsection{Size Matters}

\begin{code}
sizeRanking :: Ranking
sizeRanking = filterAndSort ( acceptAll, sizeOrd )
\end{code}

\subsection{No Vanishing Q, favour LHS}

\begin{code}
favouriteRanking  :: Ranking
favouriteRanking = filterAndSort ( onlyTrivialLVarMatches, favourDefLHSOrd )
\end{code}


\section{Classifiers}

There are many ways to classify laws into groups.
The most obvious one, 
used in the structuring of theories in \reasonEq\
is to group those about a particular logical operator,
or some well-defined collection of such operators.
This classification focusses on what the laws are \emph{about}.
A different approach is to ignore what laws are about,
and instead to focus on their \emph{structure}.
A useful concept of structure distinguishes 
between laws that \emph{define} things, 
and laws that \emph{simplify} things.

The reason this second classification is interesting is 
that there are many proofs, 
or segements of proofs, 
that take the form:
\begin{itemize}
  \item expand/unfold some definitions
  \item perform some simplifications
  \item pack/fold some definitions
\end{itemize}


The original work that inspires this was reported in 
\cite{DBLP:conf/utp/Butterfield16}. 
This talks about 
\emph{simplifiers}, 
\emph{reducers}, 
\emph{conditional-reducers}, 
and \emph{loop-unrolling}.
Reducers are steps that perform one or more definition unfolds 
with perhaps a bit of simplification.
Conditional reducers deal with cases where the precise outcome
depends on some condition ($C$) over variables, 
and what is returned is of the form
 $(C\implies P) \land (\lnot C \implies Q)$.
 Rather than automate the evaluation of $C$, 
 the user is asked to do so, 
 and hence determine which of $P$ or $Q$ should be chosen.
 Loop unrolling allows a while-loop $\whl c P$ 
 to be replaced by $(P;\whl c P) \cond c \Skip$,
 and also specifies how many unrollings should be done.


\section{Classifier Declarations}

For now we identify two kinds of laws:
those that are simplifiers; 
and those that represent definitions.
For now, both have the general shape $P \equiv Q$ or $P = Q$.

A simplifier is such a form where the ``size'' of $P$ and $Q$ are different%
\footnote{Most laws are simplifiers by this definition!}%
,
and simplification involves matching against the larger, 
and replacing it with the smaller.
We also need to note in which direction the simplification occurs:
is to left-to-right, or right-to-left?

A definition is a law where the lefthand side $P$ itself 
has the form $N(v_1,\dots,v_n)$ where $N$ is a name, 
and the $v_i$ are variables of any class (observable, expression,predicate).
Typically the righthand side $Q$ is a term involving the $v_i$.
We always assume the thing being defined is the lefthand one,
so working left-to-right is unfolding the definition,
while the other direction as a fold.

All laws are identified by the name associated with their assertion statement.


\subsection{Classifier Types}

\begin{code}
data Direction 
    = Left2Right 
    | Right2Left 
    deriving (Eq,Show,Read)

data ClassifiedLaws = ClassifiedLaws
  { simps    :: [(AssnName, Direction)]
  , folds    :: [AssnName]
  }
  deriving (Eq,Show,Read)

nullClassifiedLaws  = ClassifiedLaws { simps = [], folds = [] }
\end{code}


\section{Classifier Operations}

\subsection{Identify Simplifiers}

Given a law $P \equiv Q$ (or $e = f$),
we compare the sizes of $P$ and $Q$.
If $P$ is larger that $Q$, 
then using the law left-to-right is a simplification.
If $Q$ is larger, then right-to-left simplifies.
For now any size difference at all is used to classify laws.
\textbf{
A possible future modification might require a size difference threshold.
This could also be based on either absolute or relative differences.
It might make sense for this to be a setting at the level of individual theories.
}
\begin{code}
isSimp :: String -> Term -> Term -> (Bool,Direction)
isSimp nme p q 
  = let sizeP = termSize p
        sizeQ = termSize q
    in   if sizeP > sizeQ then (True, Left2Right) 
    else if sizeP < sizeQ then (True, Right2Left)
    else (False,error "isSimp: direction undefined if not a simplifier")

checkSimp :: String -> Term -> Term -> [(String,Direction)]
checkSimp nme p q
  = let (issimp,direction) = isSimp nme p q 
    in if issimp then [(nme,direction)] else  []
\end{code}

\begin{code}
addSimp :: String -> Term -> [(String, Direction)]
addSimp nme (Cons _ _ (Identifier "eqv" 0) (p:q:[]))  =  checkSimp nme p q
addSimp nme (Cons _ _ (Identifier "eq" 0) (e:f:[]))   =  checkSimp nme e f
addSimp _   _                                         =  []
\end{code}

\subsection{Identify Folds}

\begin{code}
isFold :: Term -> Bool
isFold (Cons _ _ _ xs@(_:_))
            | all isVar xs && allUnique xs = True
            | otherwise = False
isFold _ = False

allUnique :: (Eq a) => [a] -> Bool
allUnique []     = True
allUnique (x:xs) = x `notElem` xs && allUnique xs
\end{code}

\begin{code}
addFold :: String -> Term -> [String]
addFold nme (Cons _ sb (Identifier "eqv" 0) (p:q:[])) 
  =  if isFold p
     then if checkQ q (getN p)
          then [nme] 
          else []
     else []
addFold nme _ = []

getN :: Term -> Identifier
getN (Cons _ _ n _) = n

checkQ :: Term -> Identifier -> Bool
checkQ (Cons _ _ n _) i  =  n /= i
checkQ _ _ = True
\end{code}


\subsection{Reconcile Folds and  Simplifiers}

Many definitions have the same shape as a 
(typically right-to-left) simplifier.
We want any classified law to only have one classification,
so we usually decide they are classified as definitions,
and not simplifiers.
However, some logical operators satisfy a number of laws,
each of which satisfies the requirements to be a definition.
For example, logical implication satisfies the following laws:
\begin{eqnarray*}
   P \implies Q &\equiv& \lnot P \lor Q
\\ P \implies Q &\equiv& (P \land Q \equiv P)
\\ P \implies Q &\equiv& (P \lor Q \equiv Q)
\end{eqnarray*}
The first is a commonly used definition,
while the second is used in \cite{gries.93}.
The second and third capture the fact 
that implication is an complete lattice ordering.


Right now, all three laws above are classified as definitions,
and ``reconciliation'' just removes simplification status
from anything judged to be a definition.
What we need to do is to let the one used as an axiom be the definition,
while the other get classified as simplifiers.

Another aspect is that the law-name could be used 
to distinguish \emph{the} definition from other laws of similar structure
(``def`` vs. ``altdef''?).

\begin{code}
-- needs rework!
reconcileFoldSimps :: ClassifiedLaws -> ClassifiedLaws
reconcileFoldSimps cls 
  = ClassifiedLaws { simps = removeSimpsList (folds cls) (simps cls)
                   , folds = folds cls }

removeSimpsList :: [AssnName] -> [(AssnName, Direction)] 
                -> [(AssnName, Direction)]
removeSimpsList [] nds = nds
removeSimpsList (n:ns) nds = removeSimpsList ns $ removeSimp n nds

removeSimp :: AssnName -> [(AssnName, Direction)] -> [(AssnName, Direction)]
removeSimp _ [] = []
removeSimp n (nd@(n',_):nds) | n == n'    =       removeSimp n nds
                             | otherwise  =  nd : removeSimp n nds
\end{code}


\newpage
\section{Combining Classifications}

Some general code for collecting stuff together
(too verbose --- needs rework!)

\begin{code}
combineTwoAuto :: ClassifiedLaws -> ClassifiedLaws -> ClassifiedLaws
combineTwoAuto a b = ClassifiedLaws {  simps = simps a ++ simps b
                              , folds = folds a ++ folds b
                              }

catClassyLaws :: [ClassifiedLaws] -> ClassifiedLaws
catClassyLaws [] = nullClassifiedLaws
catClassyLaws (alws:alwss) = combineTwoAuto alws (catClassyLaws alwss)
\end{code}


\subsection{Adding Classification}

\begin{code}
addLawClassifier :: Law -> ClassifiedLaws -> ClassifiedLaws
addLawClassifier ((nme, assn),provenance) cls 
  = reconcileFoldSimps 
      $ ClassifiedLaws
          {  simps   = simps cls  ++  addSimp nme (assnT assn)
          ,  folds   = folds cls  ++  addFold nme (assnT assn)  }
\end{code}

\begin{code}
addClassyLaws :: [Law] -> ClassifiedLaws -> ClassifiedLaws
addClassyLaws []     cls  =  cls 
addClassyLaws (x:xs) cls  =  addClassyLaws (xs) (addLawClassifier x cls)
\end{code}

\newpage
\section{Checking Classifier Matches}

Given a match made against a classified law,
we supply predicates that check that the match fits with what is being specified.

\subsection{Checking Simplifiers}

Given $P\equiv Q$, 
we need to have matched either $P$ or $Q$,
in a way that is  consistent with the specified direction.
\begin{code}
checkIsSimp :: (AssnName, Direction) -> MatchClass -> Bool
checkIsSimp (_, Right2Left) MatchEqvRHS = True
checkIsSimp (_, Left2Right)  MatchEqvLHS = True
checkIsSimp _               _           = False

checkIsComp :: (AssnName, Direction) -> MatchClass -> Bool
checkIsComp (_, Right2Left) MatchEqvLHS  = True
checkIsComp (_, Left2Right)  MatchEqvRHS  = True
checkIsComp (_, _)      (MatchEqvVar _)  = True
checkIsComp _            _               = False
\end{code}


\subsection{Checking Fold/Unfold}

Given $N(v_1,\dots,v_n) \equiv Q$,
we need to have matched $Q$ to do a fold, 
and $N(v_1,\dots,v_n)$ to perform an unfold.
\begin{code}
checkIsFold :: MatchClass -> Bool
checkIsFold  MatchEqvRHS = True
checkIsFold  MatchEqvLHS = False
checkIsFold  _ = False

checkIsUnFold :: MatchClass -> Bool
checkIsUnFold MatchEqvLHS = True
checkIsUnFold MatchEqvRHS = False
checkIsUnFold _ = False 
\end{code}

\newpage
