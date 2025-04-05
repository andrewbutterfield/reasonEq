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

import Debugger
\end{code}


\section{Proof Settings Datatype}

\begin{code}
data ProofSettings
  = PrfSet {
     -- Section 1 - standalone settings
       maxMatchDisplay :: Int -- mm, maxmatches
     , showBindings :: Bool -- bd, showbinds
     -- Section 2 - settings that specify behaviour
     , showTrivialMatches :: Bool -- tm, trivialmatch --> matchFilter
     , showTrivialQuantifiers :: Bool -- tq, trivialquant --> matchFilter
     , showTrivialSubst :: Bool -- ts, trivialsubst --> matchFilter
     , showFloatingVariables :: Bool -- fv, floatvars --> matchFilter
     -- Section 3 - settings that implement behaviour from Section 2
     , matchFilter :: FilterFunction
     }
\end{code}

\subsection{Section 1 Updaters}

\begin{code}
maxMatchDisplay__ f r = r{maxMatchDisplay = f $ maxMatchDisplay r}
maxMatchDisplay_      = maxMatchDisplay__ . const
showBindings__ f r    = r{showBindings = f $ showBindings r}
showBindings_         = showBindings__ . const
\end{code}

\subsection{Section 2 Updaters}

\begin{code}
showTrivialMatch__ f r
  =  matchFilterUpdate r{showTrivialMatches = f $ showTrivialMatches r}
showTrivialMatch_   =  showTrivialMatch__ . const

showTrivialQuantifiers__ f r
  =  matchFilterUpdate r{showTrivialQuantifiers = f $ showTrivialQuantifiers r}
showTrivialQuantifiers_   =  showTrivialQuantifiers__ . const

showTrivialSubst__ f r
  =  matchFilterUpdate r{showTrivialSubst = f $ showTrivialSubst r}
showTrivialSubst_   =  showTrivialSubst__ . const

showFloatingVariables__ f r
  =  matchFilterUpdate r{showFloatingVariables = f $ showFloatingVariables r}
showFloatingVariables_   =  showFloatingVariables__ . const
\end{code}

\section{Section 3 Updater}


Section 3 updater --- not exported, internal use only.
NOW WORKS INCORRECTLY (hide became show in field names but not HERE)

\begin{code}
matchFilterUpdate r
  = r{matchFilter = mfu}
  where
    mfu = foldl mfuMrg acceptAll filterSpecs
    mfuMrg fltsofar (enabled,flt) = andIfWanted enabled flt fltsofar
    filterSpecs
      = [ ( not $ showTrivialMatches r,     isNonTrivial          )
        , ( not $ showTrivialQuantifiers r, nonTrivialQuantifiers )
        , ( not $ showTrivialSubst r,       nonTrivialSubstitution)
        , ( not $ showFloatingVariables r,  noFloatingVariables   )
        ]
\end{code}

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


\begin{code}
initProofSettings
  = matchFilterUpdate $ PrfSet {
      maxMatchDisplay        = 30
    , showBindings           = False
    , showTrivialMatches     = False
    , showTrivialQuantifiers = False 
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
                    , ("bd","Bool","Show Bindings")
                    , ("tm","Bool","Show Trivial Matches")
                    , ("tq","Bool","Show Trivial Quantifiers")
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
    displayPrfSettings _ []        =  []
    displayPrfSettings r (rs:rss)  =  disp r rs : displayPrfSettings r rss

    disp r ("mm",_,text) = text ++ " = " ++ show (maxMatchDisplay r)
    disp r ("bd",_,text) = text ++ " = " ++ show (showBindings r)
    disp r ("tm",_,text) = text ++ " = " ++ show (showTrivialMatches r)
    disp r ("tq",_,text) = text ++ " = " ++ show (showTrivialQuantifiers r)
    disp r ("ts",_,text) = text ++ " = " ++ show (showTrivialSubst r)
    disp r ("fv",_,text) = text ++ " = " ++ show (showFloatingVariables r)
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
 | name == "tq"  =  return $ showTrivialQuantifiers_ value reqs
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
 | otherwise        =  fail ("changeNumberPrfSetting - unknown field: "++name)
\end{code}

\newpage
\section{Write and Read Proof Settings}

\begin{code}
prfset = "PRFSET"
reqsetHDR = "BEGIN "++prfset ; reqsetTRL = "END "++ prfset
mmKey = "MM = "
bdKey = "BD = "
tmKey = "TM = "
tqKey = "TQ = "
tsKey = "TS = "  
fvKey = "FV = "

renderProofSettings :: ProofSettings -> [String]
renderProofSettings rqset
  = [ reqsetHDR
    , mmKey ++ show (maxMatchDisplay rqset)
    , bdKey ++ show (showBindings rqset)
    , tmKey ++ show (showTrivialMatches rqset)
    , tqKey ++ show (showTrivialQuantifiers rqset)
    , tsKey ++ show (showTrivialSubst rqset)
    , fvKey ++ show (showFloatingVariables rqset)
    , reqsetTRL ]

parseProofSettings :: MonadFail m => [String] -> m (ProofSettings, [String])
parseProofSettings [] = fail "parseProofSettings: no text"
parseProofSettings txts
  = do rest1 <- readThis reqsetHDR txts
       (theMMD,rest2) <- readKey mmKey read rest1
       (theSBD,rest3) <- readKey bdKey readBool rest2
       (theMHT,rest4) <- readKey tmKey readBool rest3
       (theMHQ,rest5) <- readKey tqKey readBool rest4
       (theMHS,rest6) <- readKey tsKey readBool rest5
       (theMHF,rest7) <- readKey fvKey readBool rest6
       rest8 <- readThis reqsetTRL rest7
       return ( matchFilterUpdate
                 ( PrfSet theMMD
                          theSBD
                          theMHT
                          theMHQ
                          theMHS
                          theMHF
                          acceptAll )
              , rest8 )
\end{code}

