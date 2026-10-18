\chapter{Proof Settings}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module ProofSettings ( 
  MatchOrder(..)
, matchOrderShorthands
, ProofSettings(..) -- used elsewhere
, proofSettingsCount, proofShowAllMatches
, initProofSettings     -- used elsewhere
, renderProofSettings   -- used elsewhere
, parseProofSettings    -- used elsewhere
, showPrfSettings       -- used elsewhere
, changePrfSettings     -- used elsewhere
, changeMatchOrder
, enableAllSpecialMatches
, disableAllSpecialMatches
)
where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Utilities
import WriteRead
import Ranking
import ProofMatch

import Debugger
\end{code}

\newpage
\section{Proof Settings Datatype}

We first define a match ordering mode,
which allows fine-tuning of match display depending on the phase of a proof:
\begin{code}
data MatchOrder
  =  SizeMatters  -- we rank matches by size only
  |  ExpandDefs   -- we give priority to matches that unfold definitions
  |  CollapseDefs -- we give priority to matches that fold definitions
  deriving (Eq,Ord,Show,Read)
\end{code}
All of these apply to the instantiated replacement term.

\begin{code}
data ProofSettings
  = PrfSet {
     -- Section 1 - standalone settings
       maxMatchDisplay :: Int -- mm, maxmatches
     , maxStepDisplay :: Int -- ms, maxsteps
     , showBindings :: Bool -- bd, showbinds
     -- Section 2 - settings that specify behaviour
     , matchOrder :: MatchOrder -- specifies how to order matches
     , showTrivialMatches :: Bool -- tm, trivialmatch --> matchFilter
     , showTrivialListVars :: Bool -- tq, trivialquant --> matchFilter
     , showTrivialSubst :: Bool -- ts, trivialsubst --> matchFilter
     , showFloatingVariables :: Bool -- fv, floatvars --> matchFilter
     -- Section 3 - settings that implement behaviour from Section 2
     , matchSort   :: [ProofMatch] -> [ProofMatch]
     , matchFilter :: ProofMatch -> Bool
     }

-- metadata about the above
proofSettingsCount = (8::Int)
proofShowAllMatches = (11::Int)
prfSettingTypes 
  =  replicate 2 "Number" 
  ++ ["Bool"]
  ++ ["MatchOrder"]
  ++ replicate 4 "Bool"
\end{code}

Display functions
\begin{code}
settablePS prfset = 
  [ "maxMatchDisplay       - " ++ show (maxMatchDisplay prfset)
  , "maxStepDisplay        - " ++ show (maxStepDisplay prfset)
  , "showBindings          - " ++ show (showBindings prfset)
  , "matchOrder            - " ++ show (matchOrder prfset)
  , "showTrivialMatches    - " ++ show (showTrivialMatches prfset)
  , "showTrivialListVars   - " ++ show (showTrivialListVars prfset)
  , "showTrivialSubst      - " ++ show (showTrivialSubst prfset)
  , "showFloatingVariables - " ++ show (showFloatingVariables prfset)
  ]
derivedPS prfset =
  [ "matchSort             - sorter"
  , "matchFilter           - predicate"
  ]

menuPS = zip [1..] . settablePS 

instance Show ProofSettings where
  show prfset  
    = unlines ( "PROOFSETTINGS:" 
                : settablePS prfset ++ derivedPS prfset ) 
\end{code}

\subsection{Section 1 Updaters}

\begin{code}
maxMatchDisplay__ f r  =  r{maxMatchDisplay = f $ maxMatchDisplay r}
maxMatchDisplay_       =  maxMatchDisplay__ . const
maxStepDisplay__ f r   =  r{maxStepDisplay = f $ maxStepDisplay r}
maxStepDisplay_        =  maxStepDisplay__ . const
showBindings__ f r     =  r{showBindings = f $ showBindings r}
showBindings_          =  showBindings__ . const
\end{code}

\newpage
\subsection{Section 2 Updaters}

\begin{code}
matchOrder__ f r
  =  matchRankingUpdate r{matchOrder = f $ matchOrder r}
matchOrder_   =  matchOrder__ . const

showTrivialMatches__ f r
  =  matchRankingUpdate r{showTrivialMatches = f $ showTrivialMatches r}
showTrivialMatches_   =  showTrivialMatches__ . const

showTrivialListVars__ f r
  =  matchRankingUpdate r{showTrivialListVars = f $ showTrivialListVars r}
showTrivialListVars_   =  showTrivialListVars__ . const

showTrivialSubst__ f r
  =  matchRankingUpdate r{showTrivialSubst = f $ showTrivialSubst r}
showTrivialSubst_   =  showTrivialSubst__ . const

showFloatingVariables__ f r
  =  matchRankingUpdate r{showFloatingVariables = f $ showFloatingVariables r}
showFloatingVariables_   =  showFloatingVariables__ . const
\end{code}


\section{Section 3 Updaters}

Section 3 updater --- not exported, internal use only.


\subsection{Update Map Sorter Function}

We have the followng sorting functions, 
applied to the match replacment, with the match bindings applied.
\begin{description}
\item[Size Matters]
  We sort purely based on \h{termSize} --- smaller is better.
\item[Expand Definitions]
  We rank left-to-right uses of definition laws as better than other laws.
\item[Collapse Definitions]
  We rank right-to-left uses of definition laws as better than other laws.
\end{description}
\textbf{Notes:} 
The replacement \m{true} is always first.
For now, a definition law is one whose name ends in \h{\_def}.
When other ordering criteria have been applied, 
we use \h{termSize} to finalise the ordering.

\begin{code}
matchSort__ f r  =  r{matchSort = f $ matchSort r}
matchSort_       =  matchSort__ . const

matchOrderUpdate :: ProofSettings -> ProofSettings
matchOrderUpdate prfset
  = case matchOrder prfset of
      SizeMatters   ->  matchSort_ (makeSort sizeOrd) prfset
      ExpandDefs    ->  prfset -- not yet implemented
      CollapseDefs  ->  prfset -- not yet implemented
\end{code}

\subsection{Update Map Filter Function}


We identify the following cases where we may want to filter out matches:
\begin{description}
\item[FV]
  The replacement term has floating variables ($?P$).
\item[TM]
  The match is a trivial one in that 
  the focus is matched against a single term variable.
\item[TL]
  All the pattern list-variables are bound to empty variable sets or lists.
\item[TS]
  All substitutions in the replacement term are empty.
\end{description}
All are modelled by a boolean setting,
where $\true$ means that such matches are kept,
means $\false$ states they should be removed.
Using these filters works by 
first asking if the match has the relevant feature,
and if it has, 
then using its setting to determine if is kept or dropped.
A match is dropped if any filter says it should be dropped.

More precisely: if a match has a filter feature $F$, 
and the setting for $F$ is $\false$,
then that match is dropped, regardless of any other settings.

\begin{code}
matchFilterUpdate :: ProofSettings -> ProofSettings
matchFilterUpdate r
  = r{matchFilter = filterSpecs}
  where
    mkFilter ( showit, ff ) mtch  = ff mtch && not showit
    filterTM = mkFilter ( showTrivialMatches r, isTrivialMatch  )
    filterTL = mkFilter ( showTrivialListVars r, onlyTrivialLVarMatches )
    filterTS = mkFilter ( showTrivialSubst r, anyTrivialSubstitutions)
    filterFV = mkFilter ( showFloatingVariables r,hasFloatingVariables   )
    filterSpecs mtch
      = not $ or  [ filterTM mtch
                  , filterTS mtch
                  , filterTL mtch
                  , filterFV mtch ]
\end{code}
Note that \h{proto/Keep.hs} demonstrates that the logic above is sound.

FInally, glue the updaters together
\begin{code}
matchRankingUpdate :: ProofSettings -> ProofSettings
matchRankingUpdate = matchOrderUpdate . matchFilterUpdate
\end{code}


\newpage
\section{Write and Read Proof Settings}

\begin{code}
prfset = "PRFSET"
reqsetHDR = "BEGIN "++prfset ; reqsetTRL = "END "++ prfset
mmKey = "MM = "
msKey = "MS = "
bdKey = "BD = "
moKey = "MO = "
tmKey = "TM = "
tlKey = "TL = "
tsKey = "TS = "  
fvKey = "FV = "

renderProofSettings :: ProofSettings -> [String]
renderProofSettings rqset
  = [ reqsetHDR
    , mmKey ++ show (maxMatchDisplay rqset)
    , msKey ++ show (maxStepDisplay rqset)
    , bdKey ++ show (showBindings rqset)
    , moKey ++ show (matchOrder rqset)
    , tmKey ++ show (showTrivialMatches rqset)
    , tlKey ++ show (showTrivialListVars rqset)
    , tsKey ++ show (showTrivialSubst rqset)
    , fvKey ++ show (showFloatingVariables rqset)
    , reqsetTRL ]

parseProofSettings :: MonadFail m => [String] -> m (ProofSettings, [String])
parseProofSettings [] = fail "parseProofSettings: no text"
parseProofSettings txts
  = do rest1 <- readThis reqsetHDR txts
       (theMMD,rest2) <- readKey mmKey read     rest1
       (theMSD,rest3) <- readKey msKey read     rest2
       (theSBD,rest4) <- readKey bdKey readBool rest3
       (theMOD,rest5) <- readKey moKey read     rest4
       (theMHT,rest6) <- readKey tmKey readBool rest5
       (theMHQ,rest7) <- readKey tlKey readBool rest6
       (theMHS,rest8) <- readKey tsKey readBool rest7
       (theMHF,rest9) <- readKey fvKey readBool rest8
       rest10 <- readThis reqsetTRL             rest9
       return ( matchRankingUpdate
                 ( PrfSet theMMD
                          theMSD
                          theSBD
                          theMOD
                          theMHT
                          theMHQ
                          theMHS
                          theMHF
                          id
                          acceptAll )
              , rest10 )
\end{code}

\newpage
\section{Settings Management}

\begin{code}
initProofSettings
  = matchRankingUpdate $ PrfSet {
      maxMatchDisplay        = 30
    , maxStepDisplay         = 10
    , showBindings           = False
    , matchOrder             = SizeMatters
    , showTrivialMatches     = False
    , showTrivialListVars    = False 
    , showTrivialSubst       = False
    , showFloatingVariables  = False 
    , matchSort              = id
    , matchFilter            = acceptAll
    }
\end{code}


\subsection{Settings Help}

\begin{code}
showPrfSettings :: ProofSettings -> String
showPrfSettings prfset = numberList id $ settablePS prfset
\end{code}



\subsection{Change Proof Settings}

\begin{code}
changePrfSettings :: MonadFail mf 
                  => Int -> String -> ProofSettings 
                  -> mf ProofSettings
changePrfSettings setno valstr rqset
  = case setno of
      1 -> return $ maxMatchDisplay_       (readNat  valstr) rqset 
      2 -> return $ maxStepDisplay_        (readNat  valstr) rqset 
      3 -> return $ showBindings_          (readBool valstr) rqset 
      4 -> changeMatchOrder                          valstr  rqset 
      5 -> return $ showTrivialMatches_    (readBool valstr) rqset 
      6 -> return $ showTrivialListVars_   (readBool valstr) rqset 
      7 -> return $ showTrivialSubst_      (readBool valstr) rqset 
      8 -> return $ showFloatingVariables_ (readBool valstr) rqset 
      _ -> return rqset -- fail silently with no change

matchOrderShorthands = ["sm","ed","cd"]

changeMatchOrder :: MonadFail mf 
                 => String -> ProofSettings 
                 -> mf ProofSettings
changeMatchOrder "sm" rqset = return $ matchOrder_ SizeMatters  rqset
changeMatchOrder "ed" rqset = return $ matchOrder_ ExpandDefs   rqset
changeMatchOrder "cd" rqset = return $ matchOrder_ CollapseDefs rqset
changeMatchOrder valstr rqset = fail ("invalid order spec: "++valstr)

enableAllSpecialMatches :: ProofSettings -> ProofSettings
enableAllSpecialMatches prfset
  = showTrivialMatches_    True $
    showTrivialListVars_   True $
    showTrivialSubst_      True $
    showFloatingVariables_ True $ prfset

disableAllSpecialMatches :: ProofSettings -> ProofSettings
disableAllSpecialMatches prfset
  = showTrivialMatches_    False $
    showTrivialListVars_   False $
    showTrivialSubst_      False $
    showFloatingVariables_ False $ prfset
\end{code}
