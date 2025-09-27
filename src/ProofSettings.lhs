\chapter{Proof Settings}
\begin{verbatim}
Copyright  Andrew Butterfield (c) 2025

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module ProofSettings ( ProofSettings(..)
                , maxMatchDisplay__, maxMatchDisplay_
                , showBindings__, showBindings_
                , initProofSettings
                , renderProofSettings, parseProofSettings
                , prfSettingStrings, showPrfSettingStrings
                , showPrfSettings
                , changePrfSettings
                , andIfWanted
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

instance Show ProofSettings where
  show prfset
    = unlines 
        [ "PROOFSETTINGS:"
        , " MMD: " ++ show (maxMatchDisplay prfset)
        , " MSD: " ++ show (maxStepDisplay prfset)
        , " SBD: " ++ show (showBindings prfset)
        ] 
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

\subsection{Section 2 Updaters}

\begin{code}
showTrivialMatch__ f r
  =  matchFilterUpdate r{showTrivialMatches = f $ showTrivialMatches r}
showTrivialMatch_   =  showTrivialMatch__ . const

showTrivialQuantifiers__ f r
  =  matchFilterUpdate r{showTrivialListVars = f $ showTrivialListVars r}
showTrivialQuantifiers_   =  showTrivialQuantifiers__ . const

showTrivialSubst__ f r
  =  matchFilterUpdate r{showTrivialSubst = f $ showTrivialSubst r}
showTrivialSubst_   =  showTrivialSubst__ . const

showFloatingVariables__ f r
  =  matchFilterUpdate r{showFloatingVariables = f $ showFloatingVariables r}
showFloatingVariables_   =  showFloatingVariables__ . const
\end{code}

\newpage
\section{Section 3 Updater}

Section 3 updater --- not exported, internal use only.
STLL WORKS INCORRECTLY !!!! 

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


The following code, 
given list \m{\seqof{(e_1,p_1),\dots,(e_n,p_n)}}
where boolean \m{e_i} enables check denoted by predicate \m{p_i},
results in the following outcome: 
\m{(e_1 \implies p_1)\land\dots\land(e_n \implies p_n)}.
Any false \m{e_j} render the corresponding check as \true.
\begin{code}
andIfWanted :: Bool -- True means we want to apply newf
            -> (ctx -> mtc -> Bool)  -- newf
            -> (ctx -> mtc -> Bool)  -- currf
            -> (ctx -> mtc -> Bool)  -- resulting filter
andIfWanted wanted newf currf ctxt mtch
 | wanted     =  currf ctxt mtch && newf ctxt mtch
 | otherwise  =  currf ctxt mtch
\end{code}

\newpage
\section{Startup/Default Settings}

Here we keep verbosity and complexity to a minimum.

\begin{code}
initProofSettings
  = matchFilterUpdate $ PrfSet {
      maxMatchDisplay        = 30
    , maxStepDisplay         = 6
    , showBindings           = False
    , showTrivialMatches     = False
    , showTrivialListVars    = False 
    , showTrivialSubst       = False
    , showFloatingVariables  = True 
    , matchFilter = acceptAll
    }
\end{code}


\subsection{Settings Help}

For every setting we provide both a short and long string,
the first for use in commands, the second for display
\begin{code}
type PrfSettingStrings = (String,String,String) -- short,type,long
prfSettingStrings = [ ("mm","Number","Max. Match Display")
                    , ("ms","Number","Max. Step Display")
                    , ("bd","Bool","Show Bindings")
                    , ("tm","Bool","Show Trivial Matches")
                    , ("tl","Bool","Show Trivial List-Variables")
                    , ("ts","Bool","Show Trivial Substitutions")
                    , ("fv","Bool","Show Floating Variables")
                    ]
showPrfSettingStrings (short,typ,long)
  = short ++ ":" ++ typ ++ " '" ++ long ++ "'"
\end{code}

\begin{code}
showPrfSettings :: ProofSettings -> String
showPrfSettings rsettings
  = unlines' $ displayPrfSettings rsettings prfSettingStrings
  where
    displayPrfSettings r =  map (disp r)

    disp r (code@"mm",_,text) = disp2 code text $ show (maxMatchDisplay r)
    disp r (code@"ms",_,text) = disp2 code text $ show (maxStepDisplay r)
    disp r (code@"bd",_,text) = disp2 code text $ show (showBindings r)
    disp r (code@"tm",_,text) = disp2 code text $ show (showTrivialMatches r)
    disp r (code@"tl",_,text) = disp2 code text $ show (showTrivialListVars r)
    disp r (code@"ts",_,text) = disp2 code text $ show (showTrivialSubst r)
    disp r (code@"fv",_,text) = disp2 code text $ show (showFloatingVariables r)

    disp2 code text shown = text ++ " ("++code++") "++shown
\end{code}

\newpage
\section{Change Proof Settings}

\begin{code}
changePrfSettings :: MonadFail m 
                  => String -> String -> ProofSettings 
                  -> m ProofSettings
changePrfSettings name valstr rqset
  = case lookupPrfSettingShort name prfSettingStrings of
      Nothing -> fail ("No such setting: "++name)
      Just sss -> changePrfSetting sss valstr rqset

lookupPrfSettingShort n []  =  Nothing
lookupPrfSettingShort n (sss@(s,_,_):ssss)
  | n == s               =  Just sss
  | otherwise            =  lookupPrfSettingShort n ssss
\end{code}

\begin{code}
changePrfSetting :: MonadFail m 
                 => PrfSettingStrings  -> String -> ProofSettings
                 -> m ProofSettings
changePrfSetting (short,typ,_) valstr reqs
 | typ == "Bool"    =  changeBoolPrfSetting short (readBool valstr) reqs
 | typ == "Number"  =  changeNumberPrfSetting short (readNat valstr) reqs
 | otherwise        =  fail ("changePrfSetting - unknown type: "++typ)
\end{code}

\begin{code}
changeBoolPrfSetting :: MonadFail m 
                     => String  -> Bool -> ProofSettings 
                     -> m ProofSettings
changeBoolPrfSetting name value reqs
 | name == "bd"  =  return $ showBindings_ value reqs
 | name == "tm"  =  return $ showTrivialMatch_ value reqs
 | name == "tl"  =  return $ showTrivialQuantifiers_ value reqs
 | name == "ts"  =  return $ showTrivialSubst_ value reqs
 | name == "fv"  =  return $ showFloatingVariables_ value reqs
 | otherwise     =  fail ("changeBoolPrfSetting - unknown field: "++name)
\end{code}

\begin{code}
changeNumberPrfSetting :: MonadFail m 
                       => String  -> Int -> ProofSettings 
                       -> m ProofSettings
changeNumberPrfSetting name value reqs
 | name == "mm"  =  return $ maxMatchDisplay_ value reqs
 | name == "ms"  =  return $ maxStepDisplay_ value reqs
 | otherwise        =  fail ("changeNumberPrfSetting - unknown field: "++name)
\end{code}

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

