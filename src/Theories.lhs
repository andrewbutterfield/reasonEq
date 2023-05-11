\section{Theories}
\begin{verbatim}
Copyright (c) Andrew Buttefield 2018-22
              Saqib Zardari     2023

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
 , conjs__, conjs_
 , auto__, auto_
 , nullTheory
 , writeTheory, readTheory
 , TheoryMap, Theories
 , NamedTheoryTexts, writeTheories, readTheories1, readTheories2
 , noTheories
 , addTheory, getTheory
 , getTheoryDeps, getTheoryDeps', getAllTheories
 , listTheories, getTheoryConjectures, getTheoryProofs
 , replaceTheory, replaceTheory'
 , updateTheory
 , newTheoryConj
 , assumeConj, assumeDepConj, lawDemote
 , addTheoryProof, upgradeConj2Law
 , showTheories, showNamedTheory
 , showTheoryLong, showTheoryShort, showTheoryLaws
 , showTheoryKnowns
 , lawClassify, lawDepClassify
 ) where

import Data.Map (Map)
import qualified Data.Map as M
import Data.List
import Data.Maybe (catMaybes)

import Utilities
import StratifiedDAG
import Substitution
import VarData
import Assertions
import Laws
import Proofs
import Classifier

import TestRendering
import WriteRead

import Debug.Trace
dbg msg x = trace (msg++show x) x
\end{code}

We define types for single theories,
and structured collections of same.


\newpage
\subsection{Types for Theories}

A theory is a collection of laws linked
to information about which variables in those laws are deemed as ``known'',
as well as information about the ``substitutability''
of constructors introduced in the theory.
In addition we also keep a list of conjectures,
that will become laws if they ever have a proof.
Any such proofs are also retained.
We also allow a theory to depend on other theories,
so long as there are no dependency cycles.
\begin{code}
data Theory
  = Theory {
      thName      :: String
    , thDeps      :: [String]
    , known       :: VarTable
    , laws        :: [Law]
    , proofs      :: [Proof]
    , auto        :: AutoLaws
    , conjs       :: [NmdAssertion]
    }
  deriving (Eq,Show,Read)

-- composable updaters
thName__ f r = r{thName = f $ thName r}    ; thName_ = thName__ . const
thDeps__ f r = r{thDeps = f $ thDeps r}    ; thDeps_ = thDeps__ . const
known__ f r = r{known = f $ known r}       ; known_ = known__ . const
laws__ f r = r{laws = f $ laws r}          ; laws_ = laws__ . const
proofs__ f r = r{proofs = f $ proofs r}    ; proofs_ = proofs__ . const
auto__ f r = r{auto = f $ auto r}          ; auto_ = auto__ . const
conjs__ f r = r{conjs = f $ conjs r}       ; conjs_ = conjs__ . const
\end{code}

We use a null theory as a base to build other theories.
\begin{code}
nullTheory
  = Theory { thName   =  "0"
           , thDeps   =  []
           , known    =  newVarTable
           , laws     =  []
           , proofs   =  []
           , auto     =  nullAutoLaws
           , conjs    =  []
           }
\end{code}

\newpage
\subsection{Writing and Reading a Theory}

\begin{code}
thry = "THEORY"
thryHDR thnm = "BEGIN " ++ thry ++ " " ++ thnm
thryTRL thnm = "END "   ++ thry ++ " " ++ thnm

depsKEY = "DEPS = "
knwnKEY = "KNOWN = "
sbblKEY = "SUBABLE = "
lawsKEY = "LAWS"
prfsKEY = "PROOFS"
simpKEY = "SIMPLIFIERS"
foldKEY = "DEFFOLD"
unflKEY = "DEFUNFOLD"
conjKEY = "CONJECTURES"

writeTheory :: Theory -> [String]
writeTheory thry
  = [ thryHDR nm
    , depsKEY ++ show (thDeps thry)
    , knwnKEY ++ show (known thry) ] ++
    writePerLine lawsKEY show (laws thry) ++
    writePerLine prfsKEY show (proofs thry) ++
    writePerLine simpKEY show (simps $ auto thry) ++
    writePerLine foldKEY id (folds $ auto thry) ++
    writePerLine unflKEY id (unfolds $ auto thry) ++
    writePerLine conjKEY show (conjs thry) ++
    [ thryTRL nm ]
  where nm = thName thry

readTheory :: (Monad m, MonadFail m) => [String] -> m (Theory,[String])
readTheory [] = fail "readTheory: no text."
readTheory txts
  = do (nm,  rest1) <- readKey (thryHDR "") id txts
       (deps,rest2) <- readKey depsKEY read     rest1
       (knwn,rest3) <- readKey knwnKEY read     rest2
       (lws, rest4) <- readPerLine lawsKEY read rest3
       (prfs,rest5) <- readPerLine prfsKEY read rest4
       (simp,rest6) <- readPerLine simpKEY read rest5
       (fold,rest7) <- readPerLine foldKEY id   rest6
       (unfl,rest8) <- readPerLine unflKEY id   rest7
       (conj,rest9) <- readPerLine conjKEY read rest8
       rest10       <- readThis (thryTRL nm)    rest9
       return ( Theory { thName   =  nm
                       , thDeps   =  deps
                       , known    =  knwn
                       , laws     =  lws
                       , proofs   =  prfs
                       , auto     =  AutoLaws simp fold unfl
                       , conjs    =  conj
                       }
              , rest10 )
\end{code}

\newpage
\subsection{Theory Collections}

We keep a collection of theories as
a directed acyclic graph (DAG) of same,
where a link from one theory to another
means that the first depends on the second.
We represent the DAG in a way that keeps it ``stratified'' (SDAG),
so that we can easily sequence theories so that any theory in
the list occurs before all those theories on which it depends,
directly, or transitively.
In the implementation, the SDAG is built over theory names,
with a separate mapping linking those names to the corresponding theories.
\begin{code}
type TheoryMap = Map String Theory
data Theories
  = Theories { tmap :: TheoryMap
             , sdag :: SDAG String }
  deriving (Show,Read)

-- composable updaters
tmap__ f r = r{tmap = f $ tmap r} ; tmap_ = tmap__ . const
sdag__ f r = r{sdag = f $ sdag r} ; sdag_ = sdag__ . const
\end{code}

\subsection{Writing and Reading Theory Collections}

\begin{code}
thrys = "THEORIES"
thrysHDR = "BEGIN "++thrys ; thrysTRL ="END "++thrys

thnmsKEY = "THNAMES = "
sdagKEY = "SDAG = "

type NamedTheoryText  =  ( String      -- Theory Name
                         , [String] )  -- Theory text
type NamedTheoryTexts = [ NamedTheoryText ]

writeTheories :: Theories
              -> ( [String]           -- Theories text
                 , [ ( String         -- Theory Name
                     , [String] ) ] ) -- Theory text
writeTheories theories
  = ( [ thrysHDR
      , thnmsKEY ++ show (M.keys tmp)
      , sdagKEY  ++ show (sdag theories)
      , thrysTRL ]
    , map genThryText (M.assocs tmp) )
  where
    tmp = tmap theories
    genThryText (nm,thry) = (nm, writeTheory thry)

-- we split theory reading into two phases.
-- First get the list of theories.
readTheories1 :: (Monad m, MonadFail m) => [String] -> m ([String],[String])
readTheories1 [] = fail "readTheories1: no text."
readTheories1 txts
  = do rest1         <- readThis thrysHDR      txts
       (thnms,rest2) <- readKey thnmsKEY read rest1
       return (thnms, rest2)
-- Second get rest
readTheories2 :: (Monad m, MonadFail m) => [(String,Theory)] -> [String]
              -> m (Theories,[String])
readTheories2 _ [] = fail "readTheories2: no text."
readTheories2 tmp txts
  = do (sdg,rest1)  <- readKey  sdagKEY read  txts
       rest2        <- readThis thrysTRL     rest1
       return (Theories (M.fromList tmp) sdg, rest2)
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
addTheory :: (Monad m, MonadFail m) => Theory -> Theories -> m Theories
addTheory thry theories
  = do let nm = thName thry
       sdag' <- insSDAG "theory" "theory dependencies"
                        nm (thDeps thry) $ sdag theories
       let tmap' = M.insert nm thry $ tmap theories
       return Theories{ tmap = tmap', sdag = sdag' }
\end{code}

\subsection{Retrieving a Theory}

\begin{code}
getTheory :: (Monad m, MonadFail m) => String -> Theories -> m Theory
getTheory thnm thrys
 = case M.lookup thnm $ tmap thrys of
     Nothing    ->  fail ("Theory '"++thnm++"' not found.")
     Just thry  ->  return thry
\end{code}


\subsection{Getting all Theory Dependencies}

We also need to generate a list of theories from the mapping,
given a starting point:
\begin{code}
getTheoryDeps :: (Monad m, MonadFail m) => String -> Theories -> m [Theory]
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
Sometimes we don't want to distinguish failure  and having no theories:
\begin{code}
getTheoryDeps' :: String -> Theories -> [Theory]
getTheoryDeps' nm theories
  = case getTheoryDeps nm theories of
      Nothing     ->  []
      Just thrys  ->  thrys
\end{code}

Sometimes we just want all the theories in dependency order:
\begin{code}
getAllTheories :: Theories -> [Theory]
getAllTheories theories
 = let thryNms = topDownSDAG $ sdag theories
   in catMaybes $ map (lookin $ tmap theories) thryNms
 where lookin tmp nm = M.lookup nm tmp
\end{code}

\newpage
\subsection{Various Lookups}

\subsubsection{List all theories}

\begin{code}
listTheories :: Theories -> [String]
listTheories thrys = M.keys $ tmap thrys
\end{code}

\subsubsection{Get Conjectures of current theory}

\begin{code}
getTheoryConjectures :: (Monad m, MonadFail m) => String -> Theories -> m [NmdAssertion]
getTheoryConjectures thNm thrys
  = do case M.lookup thNm (tmap thrys) of
         Nothing    ->  fail ("Conjectures: theory '"++thNm++", not found")
         Just thry  ->  return $ conjs thry
\end{code}

\subsubsection{Get Proofs from current theory}

\begin{code}
getTheoryProofs :: (Monad m, MonadFail m) => String -> Theories -> m [Proof]
getTheoryProofs thNm thrys
  = do case M.lookup thNm (tmap thrys) of
         Nothing    ->  fail ("Proofs: theory '"++thNm++", not found")
         Just thry  ->  return $ proofs thry
\end{code}

\subsection{Various Changes}

\subsubsection{Generic Theory Replacement}

We insist, for now at least,
that the dependencies do not change.
\begin{code}
replaceTheory :: (Monad m, MonadFail m) 
              => String -> (Theory -> Theory) -> Theories -> m Theories
replaceTheory thnm thryF (Theories tmap sdag)
  = case M.lookup thnm tmap of
      Nothing    ->  fail ("replaceTheory: '"++thnm++"' not found.")
      Just thry  ->  let thry' = thryF thry
                     in if thDeps thry' == thDeps thry
                        then return $ Theories (M.insert thnm (thryF thry) tmap)
                                               sdag
                        else fail ( "replaceTheory: '"
                                    ++ thnm ++ "' dependencies have changed" )
\end{code}

This code is a total version,
in that it ``fails'' silently,
by simply returning its input.
\begin{code}
replaceTheory' :: Theory -> Theories -> Theories
replaceTheory' thry theories
 = case replaceTheory (thName thry) (const thry) theories of
     Nothing         ->  theories
     Just theories'  ->  theories'
\end{code}

\subsubsection{Theory Update}

\begin{code}
updateTheory :: (Monad m, MonadFail m) => String -> Theory -> Bool -> Theories -> m Theories
updateTheory thnm thry0 force (Theories tmap sdag)
  = case M.lookup thnm tmap of
      Nothing    ->  fail ("updateTheory: '"++thnm++"' not found.")
      Just thry  ->
        do let (remL,eqL,updL,newL) 
                            = keyListDiff (fst . fst) (laws thry)  (laws thry0)
           let (remC,eqC,updC,newC) 
                            = keyListDiff fst         (conjs thry) (conjs thry0)
           -- need to do this for VarTable ?
           -- need to do this for SubAbilityMap ?
           -- or are these *necessary* updates?
           -- they can invalidate proofs.
           if null updL && null updC
           then
             do  let thry' = addLaws thry newL
                 let thry'' = addConjs thry' newC
                 return $ Theories (M.insert thnm thry'' tmap) sdag
           else
             fail $ unlines
              [ "updateTheory: can't handle law/conj. updates right now"
              , "remL: " ++ show (map (fst . fst) remL)
              , " eqL: " ++ show (map (fst . fst)  eqL)
              , "updL: " ++ show (map (fst . fst) updL)
              , "newL: " ++ show (map (fst . fst) newL)
              , "remC: " ++ show (map fst remC)
              , " eqC: " ++ show (map fst  eqC)
              , "updC: " ++ show (map fst updC)
              , "newC: " ++ show (map fst newC)
              ]

addLaws  thry newL  =  laws__ (++ newL) thry
addConjs thry newC  =  conjs__ (++ newC) thry
\end{code}


\subsubsection{Monadic Theory Component Updates}

We have some updates that are monadic
\begin{code}
newTheoryConj :: (Monad m, MonadFail m) => NmdAssertion -> Theory -> m Theory
newTheoryConj nasn@(nm,_) thry
  | nm `elem` map (fst . fst) (laws thry) = fail "name in use in laws!"
  | nm `elem` map fst  (conjs thry) = fail "name in use in conjectures!"
  | otherwise = return $ conjs__ (nasn:) thry
\end{code}

\begin{code}
assumeConj :: (Monad m, MonadFail m) => String -> Theory -> m Theory
assumeConj cjnm thry
 | null cjs     =  return thry
 | cjnm == "."  =  return $ conjs_ []
                          $ laws__ (++(map labelAsAssumed cjs)) thry
 | null cnj1    =  fail ("assumeConj '"++cjnm++"': not found")
 | otherwise    =  return $ conjs_ (before++after)
                          $ laws__ (labelAsAssumed cnj:) thry
 where
   cjs = conjs thry
   (before,cnj1,after) = extract ((cjnm ==) . fst) cjs
   cnj = head cnj1
\end{code}

\begin{code}
assumeDepConj :: (Monad m, MonadFail m) => String -> Theories -> m Theories
assumeDepConj thnm thys
  = do depthys <- fmap ttail $ getTheoryDeps thnm thys
       assumeDepConj' thys depthys

assumeDepConj' thys [] = return thys
assumeDepConj' thys (depthy:depthys)
  = do  depthy' <- assumeConj "." depthy
        thys' <- replaceTheory (thName depthy) (const depthy') thys
        assumeDepConj' thys' depthys
\end{code}

currTh = currTheory reqs
getCurrConj reqs = fromJust $ getTheoryConjectures currTh thys
thys = theories reqs
thylist = fromJust $ getTheoryDeps currTh thys

\begin{code}
lawDemote :: (Monad m, MonadFail m) => String -> Theory -> m Theory
lawDemote lnm thry
 | null lws        =  fail ("lawDemote '"++lnm++"': no laws")
 | lnm == "*"      =  if null assl
                      then fail "lawDemote *: no assumed laws"
                      else return $ laws_ othrl
                                  $ conjs__ (++(map fst assl)) thry
 | lnm == "[]"     =  if null prfl
                      then fail "lawDemote []: no proven laws"
                      else return $ laws_ (axml++assl)
                                  $ conjs__ (++(map fst prfl)) thry
 | null law1       =  fail ("lawDemote '"++lnm++"': not found")
 | isAxiom theLaw  =  fail ("lawDemote '"++lnm++"' is an axiom")
 | otherwise       =  return $ laws_ (before++after)
                             $ conjs__ ((fst theLaw):) thry
 where
   lws = laws thry
   (assl,othrl) = partition isAssumed lws
   (prfl,axml) = partition isProven othrl
   (before,law1,after) = extract (((lnm==) . fst) .fst) lws
   theLaw = head law1
\end{code}

\subsubsection{Add Proof to Theory}

This code also ``fails'' silently.
\begin{code}
addTheoryProof :: String -> Proof -> Theories -> Theories
addTheoryProof thname prf thrys
  = case replaceTheory thname (proofs__ (prf:)) thrys of
      Nothing      ->  thrys
      Just thrys'  ->  thrys'
\end{code}

\newpage
\subsubsection{Upgrade (proven) Conjecture to Law}

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

\subsubsection{Classifying}

\begin{code}
lawClassify :: MonadFail m => [Law] -> Theory -> m Theory
lawClassify lw thry = return $ auto_ (addLawsClass (lw) (auto thry)) thry

lawDepClassify :: MonadFail m => String -> Theories -> m Theories
lawDepClassify thnm thys
  = do depthys <- fmap ttail $ getTheoryDeps thnm thys
       lawDepClassify' thys depthys

lawDepClassify' thys [] = return thys
lawDepClassify' thys (depthy:depthys)
  = do  let lws = laws depthy
        depthy' <- lawClassify lws depthy
        thys' <- replaceTheory (thName depthy) (const depthy') thys
        lawDepClassify' thys' depthys
\end{code}


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
        else "( "++intercalate " ; " (thDeps thry)++" )"
  where deps = thDeps thry

showTheoryLaws dm thry
  = unlines' (
      [ "Theory '"++thName thry++"'"
      , "Knowns:", trVarTable (known thry)
      , "Laws:", showLaws dm (laws thry)
      , "Conjectures:", showConjs dm (conjs thry)
      , "AutoLaws:", showAuto (auto thry)
      ] )

showNamedTheory dm thnm thrys
  = case M.lookup thnm $ tmap thrys of
      Nothing -> ("No such theory: "++thnm)
      Just thry -> showTheoryLong dm thry

showTheoryLong dm thry
  = unlines' (
      ( "Theory '"++thName thry++"'" )
      : ( if null deps
        then []
        else [ "depends on: "++intercalate "," deps] )
      ++
      [ "Knowns:", trVarTable (known thry)
      , "Laws:", showLaws dm (laws thry)
      , "Conjectures:", showConjs dm (conjs thry) 
      , "AutoLaws:", showAuto (auto thry)]
    )
  where deps = thDeps thry
\end{code}


\begin{code}
showTheoryKnowns :: Theory -> String
showTheoryKnowns thry = trVarTable (known thry)
\end{code}
