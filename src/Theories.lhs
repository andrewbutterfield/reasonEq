\section{Theories}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
{-# LANGUAGE PatternSynonyms #-}
module Theories
 ( Theory(..)
 , thName__, thName_
 , thDeps__, thDeps_
 , known__, known_
 , laws__, laws_
 , proofs__, proofs_
 , pausedProofs__, pausedProofs_
 , conjs__, conjs_
 , nullTheory
 , Theories
 , writeTheories, readTheories
 , noTheories
 , addTheory, getTheory
 , getTheoryDeps, getTheoryDeps'
 , listTheories, getTheoryConjectures, getTheoryProofs
 , updateTheory, replaceTheory
 , addTheoryProof, upgradeConj2Law
 , showTheories, showNamedTheory, showTheoryLong, showTheoryShort
 ) where

import Data.Map (Map)
import qualified Data.Map as M
import Data.List

import Utilities
import StratifiedDAG
import VarData
import Laws
import Proofs

import TestRendering

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for single theories,
and structured collections of same.


\newpage
\subsection{Types for Theories}

A theory is a collection of laws linked
to information about which variables in those laws are deemed as ``known''.
In addition we also keep a list of conjectures,
that will become laws if they ever have a proof.
Any such proofs are also retained.
We also allow a theory to depend on other theories,
so long as there are no dependency cycles.
\begin{code}
data Theory
  = Theory {
      thName       :: String
    , thDeps       :: [String]
    , known        :: VarTable
    , laws         :: [Law]
    , proofs       :: [Proof]
    , pausedProofs :: [Proof]
    , conjs        :: [NmdAssertion]
    }
  deriving (Eq,Show,Read)

-- composable updaters
thName__ f r = r{thName = f $ thName r} ; thName_ = thName__ . const
thDeps__ f r = r{thDeps = f $ thDeps r} ; thDeps_ = thDeps__ . const
known__ f r = r{known = f $ known r} ; known_ = known__ . const
laws__ f r = r{laws = f $ laws r} ; laws_ = laws__ . const
proofs__ f r = r{proofs = f $ proofs r} ; proofs_ = proofs__ . const
pausedProofs__ f r = r{pausedProofs = f $ pausedProofs r}
pausedProofs_ = pausedProofs__ . const
conjs__ f r = r{conjs = f $ conjs r} ; conjs_ = conjs__ . const
\end{code}

It can be useful to have a null theory%
\footnote{hypothesis?}%
:
\begin{code}
nullTheory
  = Theory { thName       = "0"
           , thDeps       = []
           , known        = newVarTable
           , laws         = []
           , proofs       = []
           , pausedProofs = []
           , conjs        = []
           }
\end{code}

We keep a collection of theories as
a directed acyclic graph (DAG) of same,
where a link from one theory to another
means that the first depends on the second.
We represent the DAG in a way that keeps it ``stratified'' (SDAG),
so that we can easily sequence theories so that any theory in
the list occurs before all those theories on which it depends,
directly, or transitively.
In the implementation, the SDAG is built over theory names,
with a seperate mapping linking those names to the corresponding theories.
\begin{code}
data Theories
  = Theories { tmap :: Map String Theory
             , sdag :: SDAG String }
  deriving (Show,Read)

-- composable updaters
tmap__ f r = r{tmap = f $ tmap r} ; tmap_ = tmap__ . const
sdag__ f r = r{sdag = f $ sdag r} ; sdag_ = sdag__ . const
\end{code}

\subsection{Writing and Reading Theories}

\begin{code}
theories = "THEORIES"
thryHDR = "BEGIN "++theories ; thryTRL ="END "++theories

tmapKEY = "TMAP = "
sdagKEY = "SDAG = "

writeTheories :: Theories -> [String]
writeTheories theories
  = [ thryHDR
    , tmapKEY ++ show (tmap theories)
    , sdagKEY ++ show (sdag theories)
    , thryTRL ]

readTheories :: Monad m => [String] -> m (Theories,[String])
readTheories [] = fail "readTheories: no text."
-- readTheories txts
--   = do rest1       <- readThis thryHDR txts
--        (tmp,rest2) <- readKey  tmapKEY read rest1
--        (sdg,rest3) <- readKey  sdag_KEY read rest2
--        rest4       <- readThis thryTRL rest3
--        return (Theories tmp sdg, rest4)
\end{code}

\subsection{No Theories}

We start by defining a state of zero knowledge:
\begin{code}
noTheories = Theories{ tmap = M.empty, sdag = [] }
\end{code}

\newpage
\subsection{Adding a New Theory}

A key principle in adding a new theory is that it can
only be inserted if its dependencies are already present.
This guarantees that we construct a DAG.
Here we use the SDAG component to check this,
by trying to add to that component first.
If that succeeds,
then we just add to the map component without any further checks.
\begin{code}
addTheory :: Monad m => Theory -> Theories -> m Theories
addTheory thry theories
  = do let nm = thName thry
       sdag' <- insSDAG nm (thDeps thry) $ sdag theories
       let tmap' = M.insert nm thry $ tmap theories
       return Theories{ tmap = tmap', sdag = sdag' }
\end{code}

\subsection{Retrieving a Theory}

\begin{code}
getTheory :: Monad m => String -> Theories -> m Theory
getTheory thnm thrys
 = case M.lookup thnm $ tmap thrys of
     Nothing    ->  fail ("Theory '"++thnm++"' not found.")
     Just thry  ->  return thry
\end{code}

\subsection{Getting all Theory Dependencies}

We also need to generate a list of theories from the mapping,
given a starting point:
\begin{code}
getTheoryDeps :: Monad m => String -> Theories -> m [Theory]
getTheoryDeps nm theories
  = case getSDAGdeps nm $ sdag theories of
      []  ->  fail ("No such theory: '"++nm++"'")
      deps  ->  sequence $ map (lookin $ tmap theories) deps
  where
    lookin mapt nm
      = case M.lookup nm mapt of
          Nothing ->  fail ("Dep. '"++nm++"' not found.")
          Just t  -> return t
\end{code}
Sometimes we don't want to distinguish failure  and having no laws:
\begin{code}
getTheoryDeps' :: String -> Theories -> [Theory]
getTheoryDeps' nm theories
  = case getTheoryDeps nm theories of
      Nothing     ->  []
      Just thrys  ->  thrys
\end{code}

\subsection{Various Lookups}

\subsubsection{List all theories}

\begin{code}
listTheories :: Theories -> [String]
listTheories thrys = M.keys $ tmap thrys
\end{code}

\subsubsection{Get Conjectures of current theory}

\begin{code}
getTheoryConjectures :: Monad m => String -> Theories -> m [NmdAssertion]
getTheoryConjectures thNm thrys
  = do case M.lookup thNm (tmap thrys) of
         Nothing    ->  fail ("Conjectures: theory '"++thNm++", not found")
         Just thry  ->  return $ conjs thry
\end{code}

\subsubsection{Get Proofs for current theory}

\begin{code}
getTheoryProofs :: Monad m => String -> Theories -> m [Proof]
getTheoryProofs thNm thrys
  = do case M.lookup thNm (tmap thrys) of
         Nothing    ->  fail ("Proofs: theory '"++thNm++", not found")
         Just thry  ->  return $ proofs thry
\end{code}

\subsection{Various Updates}

\subsubsection{Generic Theory Updats}

\begin{code}
updateTheory :: String -> (Theory -> Theory) -> Theories -> Theories
updateTheory thnm thryF theories@(Theories tmap sdag)
  = case M.lookup thnm tmap of
      Nothing    ->  theories -- silent 'fail'
      Just thry  ->  Theories (M.insert thnm (thryF thry) tmap) sdag
\end{code}

\begin{code}
replaceTheory :: Theory -> Theories -> Theories
replaceTheory thry theories  =  updateTheory (thName thry) (const thry) theories
\end{code}

\subsubsection{Add Proof to Theory}

\begin{code}
addTheoryProof :: String -> Proof -> Theories -> Theories
addTheoryProof thname prf = updateTheory thname (proofs__ (prf:))
  -- = case M.lookup thname tmap of
  --     Nothing    ->  theories -- silent 'fail'
  --     Just thry  ->  Theories (M.insert thname (proofs__ (prf:) thry) tmap) sdag
\end{code}

\begin{code}
upgradeConj2Law  :: String -> String -> Theories -> Theories
upgradeConj2Law thnm cjnm thrys@(Theories tmap sdag)
  = case M.lookup thnm tmap of
      Nothing  ->  thrys
      Just thry
       -> case upgrade cjnm thry [ ]$ conjs thry of
            Nothing -> thrys
            Just thry' -> Theories (M.insert thnm thry' tmap) sdag

upgrade _ _ _ [] = Nothing
upgrade cjnm thry sjc (cj@(nm,asn):cjs)
 | cjnm /= nm  =  upgrade cjnm thry (cj:sjc) cjs
 | otherwise   =  Just ( conjs_ (reverse sjc ++ cjs)
                       $ laws__ (++[prf]) thry )
 where prf = labelAsProof cj cjnm
\end{code}

\newpage
\subsection{Showing Theories}

\textbf{This should all be done via proper generic rendering code}


\begin{code}
showTheories thrys = showTheories' $ M.assocs $ tmap thrys
showTheories' [] = "No theories present."
showTheories' thrys = unlines' $ map (showTheoryShort . snd) thrys

showTheoryShort thry
  = thName thry
    ++ if null deps
        then ""
        else "("++intercalate " " (thDeps thry)++")"
  where deps = thDeps thry

showNamedTheory thnm thrys
  = case M.lookup thnm $ tmap thrys of
      Nothing -> ("No such theory: "++thnm)
      Just thry -> showTheoryLong thry

showTheoryLong thry
  = unlines' (
      ( "Theory '"++thName thry++"'" )
      : ( if null deps
        then []
        else [ "depends on: "++intercalate "," deps] )
      ++
      [ trVarTable (known thry)
      , showLaws (laws thry) ]
    )
  where deps = thDeps thry
\end{code}
