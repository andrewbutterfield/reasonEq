\chapter{Classifier}
\begin{verbatim}
Copyright  Saqib Zardari (c) 2023
           Andrew Butterfield (c) 2024--25

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Classifier 
  ( Direction(..), ClassifiedLaws(..), nullClassifiedLaws, showClassyLaws
  , catClassyLaws
  , addClassyLaws
  , checkIsComp, checkIsSimp, checkIsFold, checkIsUnFold
  ) where

import qualified Data.Set as S
import Utilities
import Laws
import AST
import Assertions
import LexBase
import Proofs

import Debugger
\end{code}

\section{Introduction}

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
    = Leftwards 
    | Rightwards 
    deriving (Eq,Show,Read)

data ClassifiedLaws = ClassifiedLaws
  { simps    :: [(AssnName, Direction)]
  , folds    :: [AssnName]
  }
  deriving (Eq,Show,Read)

nullClassifiedLaws  = ClassifiedLaws { simps = [], folds = [] }
\end{code}

\subsubsection{Classifier Display}

\begin{code}
showDir :: Direction -> String
showDir Leftwards  = "Leftwards"
showDir Rightwards = "Rightwards"

simpStr :: (String, Direction) -> String
simpStr sim = "(" ++ fst sim ++ "," ++ showDir (snd sim) ++ ")"

showSimps :: [(String, Direction)] -> Int -> String
showSimps [] _ = ""
showSimps (x:[]) n = "\n\t" ++ show n ++ ". " ++ simpStr x
showSimps (x:xs) n = "\n\t" ++ show n ++ ". " 
                     ++ simpStr x ++ showSimps xs (n + 1)

showFolds :: [String] -> Int -> String
showFolds [] _ = ""
showFolds (x:[]) n = "\n\t" ++ show n ++ ". " ++ x
showFolds (x:xs) n = "\n\t" ++ show n ++ ". " ++ x ++ showFolds xs (n + 1)

showClassyLaws alaws = unlines'
  [ "  simplifiers:"  ++ showSimps (simps alaws) 1
  , "  folds/unfolds:"  ++ showFolds (folds alaws) 1 ]
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
    in   if sizeP > sizeQ then (True, Leftwards) 
    else if sizeP < sizeQ then (True, Rightwards)
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
checkIsSimp (_, Rightwards) MatchEqvRHS = True
checkIsSimp (_, Leftwards)  MatchEqvLHS = True
checkIsSimp _               _           = False

checkIsComp :: (AssnName, Direction) -> MatchClass -> Bool
checkIsComp (_, Rightwards) MatchEqvLHS  = True
checkIsComp (_, Leftwards)  MatchEqvRHS  = True
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
