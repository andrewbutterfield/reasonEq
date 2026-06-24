\chapter{Proof Settings}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module ProofSettings ( 
  ProofSettings(..) -- used elsewhere
, proofSettingsCount, proofShowAllMatches
, initProofSettings     -- used elsewhere
, renderProofSettings   -- used elsewhere
, parseProofSettings    -- used elsewhere
, showPrfSettings       -- used elsewhere
, changePrfSettings     -- used elsewhere
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

\begin{code}
data ProofSettings
  = PrfSet {
     -- Section 1 - standalone settings
       maxMatchDisplay :: Int -- mm, maxmatches
     , maxStepDisplay :: Int -- ms, maxsteps
     , showBindings :: Bool -- bd, showbinds
     -- Section 2 - settings that specify behaviour
     , showTrivialMatches :: Bool -- tm, trivialmatch --> matchFilter
     , showTrivialListVars :: Bool -- tq, trivialquant --> matchFilter
     , showTrivialSubst :: Bool -- ts, trivialsubst --> matchFilter
     , showFloatingVariables :: Bool -- fv, floatvars --> matchFilter
     -- Section 3 - settings that implement behaviour from Section 2
     , matchFilter :: FilterFunction
     }

-- metadata about the above
proofSettingsCount = (7::Int)
proofShowAllMatches = (10::Int)
prfSettingTypes = replicate 2 "Number" ++ replicate 5 "Bool"
\end{code}

Display functions
\begin{code}
settablePS prfset = 
  [ "maxMatchDisplay       - " ++ show (maxMatchDisplay prfset)
  , "maxStepDisplay        - " ++ show (maxStepDisplay prfset)
  , "showBindings          - " ++ show (showBindings prfset)
  , "showTrivialMatches    - " ++ show (showTrivialMatches prfset)
  , "showTrivialListVars   - " ++ show (showTrivialListVars prfset)
  , "showTrivialSubst      - " ++ show (showTrivialSubst prfset)
  , "showFloatingVariables - " ++ show (showFloatingVariables prfset)
  ]
derivedPS prfset =
  [ "matchFilter           - function"
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
showTrivialMatches__ f r
  =  matchFilterUpdate r{showTrivialMatches = f $ showTrivialMatches r}
showTrivialMatches_   =  showTrivialMatches__ . const

showTrivialListVars__ f r
  =  matchFilterUpdate r{showTrivialListVars = f $ showTrivialListVars r}
showTrivialListVars_   =  showTrivialListVars__ . const

showTrivialSubst__ f r
  =  matchFilterUpdate r{showTrivialSubst = f $ showTrivialSubst r}
showTrivialSubst_   =  showTrivialSubst__ . const

showFloatingVariables__ f r
  =  matchFilterUpdate r{showFloatingVariables = f $ showFloatingVariables r}
showFloatingVariables_   =  showFloatingVariables__ . const
\end{code}


\section{Section 3 Updater}

Section 3 updater --- not exported, internal use only.

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
-- FilterFunction = [MatchContext] -> ProofMatch -> Bool
matchFilterUpdate r
  = r{matchFilter = filterSpecs}
  where
    mkFilter ( showit, ff ) (ctxts,mtch)  = ff ctxts mtch && not showit
    filterTM = mkFilter ( showTrivialMatches r, isTrivialMatch  )
    filterTL = mkFilter ( showTrivialListVars r, onlyTrivialLVarMatches )
    filterTS = mkFilter ( showTrivialSubst r, anyTrivialSubstitutions)
    filterFV = mkFilter ( showFloatingVariables r,hasFloatingVariables   )
    filterSpecs ctxts mtch
      = not $ or  [ filterTM cm
                  , filterTS cm
                  , filterTL cm
                  , filterFV cm ]
      where cm = (ctxts,mtch)
\end{code}
Note that \h{proto/Keep.hs} demonstrates that the logic above is sound.


\newpage
\section{Write and Read Proof Settings}

\begin{code}
prfset = "PRFSET"
reqsetHDR = "BEGIN "++prfset ; reqsetTRL = "END "++ prfset
mmKey = "MM = "
msKey = "MS = "
bdKey = "BD = "
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
       (theMHT,rest5) <- readKey tmKey readBool rest4
       (theMHQ,rest6) <- readKey tlKey readBool rest5
       (theMHS,rest7) <- readKey tsKey readBool rest6
       (theMHF,rest8) <- readKey fvKey readBool rest7
       rest9 <- readThis reqsetTRL              rest8
       return ( matchFilterUpdate
                 ( PrfSet theMMD
                          theMSD
                          theSBD
                          theMHT
                          theMHQ
                          theMHS
                          theMHF
                          acceptAll )
              , rest9 )
\end{code}

\newpage
\section{Settings Management}

\begin{code}
initProofSettings
  = matchFilterUpdate $ PrfSet {
      maxMatchDisplay        = 30
    , maxStepDisplay         = 10
    , showBindings           = False
    , showTrivialMatches     = False
    , showTrivialListVars    = False 
    , showTrivialSubst       = False
    , showFloatingVariables  = False 
    , matchFilter = acceptAll
    }
\end{code}


\subsection{Settings Help}

\begin{code}
showPrfSettings :: ProofSettings -> String
showPrfSettings prfset = numberList id $ settablePS prfset
\end{code}



\subsection{Change Proof Settings}

\begin{code}
changePrfSettings :: MonadFail m 
                  => Int -> String -> ProofSettings 
                  -> m ProofSettings
changePrfSettings setno valstr rqset
  = case setno of
      1 -> return $ maxMatchDisplay_       (readNat  valstr) rqset 
      2 -> return $ maxStepDisplay_        (readNat  valstr) rqset 
      3 -> return $ showBindings_          (readBool valstr) rqset 
      4 -> return $ showTrivialMatches_    (readBool valstr) rqset 
      5 -> return $ showTrivialListVars_   (readBool valstr) rqset 
      6 -> return $ showTrivialSubst_      (readBool valstr) rqset 
      7 -> return $ showFloatingVariables_ (readBool valstr) rqset 
      _ -> return rqset -- fail silently with no change

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
