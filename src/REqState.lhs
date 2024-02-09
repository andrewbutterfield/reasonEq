\chapter{\reasonEq\ State}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--22

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module REqState ( REqSettings(..)
                , maxMatchDisplay__, maxMatchDisplay_
                , initREqSettings
                , rEqSettingStrings, showSettingStrings, showSettings
                , changeSettings
                , REqState(..)
                , projectDir__, projectDir_
                , modified__, modified_, changed
                , theories__, theories_
                , settings__, settings_
                , currTheory__, currTheory_, liveProofs__, liveProofs_
                , writeREqState
                , readREqState1, readREqSettings, readREqState2
                , module TermZipper
                , module Laws
                , module Proofs
                , module Theories
                , module Sequents
                , module LiveProofs
                )
where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import Utilities
import Control
import WriteRead
import TermZipper
import Laws
import Proofs
import Theories
import Sequents
import LiveProofs
import Ranking

import Debugger
\end{code}

\section{Settings}

We divide settings into three types:
\begin{enumerate}
  \item
    Standalone settings,
    whose associated behaviour is directly implemented
    at the relevant point in the code.
  \item
   Specification settings, that specify more complex behaviour tuning,
   for which it is worth to compute behaviour once when they are changed.
  \item
   Implementation settings,
   are related to the specification settings above.
   These are never directly set by the user,
   but are computed from user-changes to the specification settings above.
   The relationship is not one-to-one.
   In particular,
   a given implementation setting may be a blend
   of several related specification settings.
\end{enumerate}

\subsection{Settings Record}

\begin{code}
data REqSettings
  = REqSet {
     -- Section 1 - standalone settings
       maxMatchDisplay :: Int -- mmd
     -- Section 2 - settings that specify behaviour
     , hideTrivialMatch :: Bool -- mht --> matchFilter
     , hideTrivialQuantifiers :: Bool -- mhq --> matchFilter
     , hideFloatingVariables :: Bool -- mhf --> matchFilter
     -- Section 3 - settings that implement behaviour from Section 2
     , matchFilter :: FilterFunction
     }

-- Section 1 updaters
maxMatchDisplay__ f r = r{maxMatchDisplay = f $ maxMatchDisplay r}
maxMatchDisplay_      = maxMatchDisplay__ . const

-- Section 2 updaters
hideTrivialMatch__ f r
  =  matchFilterUpdate r{hideTrivialMatch = f $ hideTrivialMatch r}
hideTrivialMatch_   =  hideTrivialMatch__ . const

hideTrivialQuantifiers__ f r
  =  matchFilterUpdate r{hideTrivialQuantifiers = f $ hideTrivialQuantifiers r}
hideTrivialQuantifiers_   =  hideTrivialQuantifiers__ . const

hideFloatingVariables__ f r
  =  matchFilterUpdate r{hideFloatingVariables = f $ hideFloatingVariables r}
hideFloatingVariables_   =  hideFloatingVariables__ . const


-- Section 3 updaters -- not exported, internal use only

matchFilterUpdate r
  = r{matchFilter = mfu}
  where
    mfu = foldl mfuMrg acceptAll filterSpecs
    mfuMrg fltsofar (enabled,flt) = andIfWanted enabled flt fltsofar
    filterSpecs
      = [ ( hideTrivialMatch r,       isNonTrivial )
        , ( hideTrivialQuantifiers r, nonTrivialQuantifiers )
        , ( hideFloatingVariables r,  noFloatingVariables )
        ]
\end{code}

\begin{code}
andIfWanted :: Bool -> (ctx -> mtc -> Bool) -> (ctx -> mtc -> Bool)
                    -> ctx -> mtc -> Bool
andIfWanted wanted newf currf ctxt mtch
 | wanted     =  currf ctxt mtch && newf ctxt mtch
 | otherwise  =  currf ctxt mtch
\end{code}


\subsection{Startup/Default Settings}


\begin{code}
initREqSettings
  = matchFilterUpdate $ REqSet {
      maxMatchDisplay = 20
    , hideTrivialMatch = True
    , hideTrivialQuantifiers = True 
    , hideFloatingVariables = False 
    , matchFilter = acceptAll
    }
\end{code}

\subsection{Settings Help}

For every setting we provide both a short and long string,
the first for use in commands, the second for display
\begin{code}
type SettingStrings = (String,String,String) -- short,type,long
rEqSettingStrings = [ ("mmd","Number","Max. Match Display")
                    , ("mht","Bool","Hide Trivial Matches")
                    , ("mhq","Bool","Hide Trivial Quantifiers")
                    , ("mhf","Bool","Hide Floating Variables")
                    ]
showSettingStrings (short,typ,long)
  = short ++ ":" ++ typ ++ " '" ++ long ++ "'"
\end{code}

\begin{code}
showSettings :: REqSettings -> String
showSettings rsettings
  = unlines' $ displaySettings rsettings rEqSettingStrings
  where
    displaySettings _ []        =  []
    displaySettings r (rs:rss)  =  disp r rs : displaySettings r rss

    disp r ("mmd",_,text) = text ++ " = " ++ show (maxMatchDisplay r)
    disp r ("mht",_,text) = text ++ " = " ++ show (hideTrivialMatch r)
    disp r ("mhq",_,text) = text ++ " = " ++ show (hideTrivialQuantifiers r)
    disp r ("mhf",_,text) = text ++ " = " ++ show (hideFloatingVariables r)
\end{code}

\begin{code}
changeSettings :: (Monad m, MonadFail m) => String -> String -> REqSettings -> m REqSettings
changeSettings name valstr rqset
  = case lookupSettingShort name rEqSettingStrings of
      Nothing -> fail ("No such setting: "++name)
      Just sss -> changeSetting sss valstr rqset

lookupSettingShort n []  =  Nothing
lookupSettingShort n (sss@(s,_,_):ssss)
  | n == s               =  Just sss
  | otherwise            =  lookupSettingShort n ssss
\end{code}

\begin{code}
changeSetting :: (Monad m, MonadFail m) => SettingStrings  -> String -> REqSettings
                         -> m REqSettings
changeSetting (short,typ,_) valstr reqs
 | typ == "Bool"    =  changeBoolSetting short (readBool valstr) reqs
 | typ == "Number"  =  changeNumberSetting short (readNat valstr) reqs
 | otherwise        =  fail ("changeSetting - unknown type: "++typ)
\end{code}

\begin{code}
changeBoolSetting :: (Monad m, MonadFail m) => String  -> Bool -> REqSettings -> m REqSettings
changeBoolSetting name value reqs
 | name == "mht"  =  return $ hideTrivialMatch_ value reqs
 | name == "mhq"  =  return $ hideTrivialQuantifiers_ value reqs
 | name == "mhf"  =  return $ hideFloatingVariables_ value reqs
 | otherwise      =  fail ("changeBoolSetting - unknown field: "++name)
\end{code}

\begin{code}
changeNumberSetting :: (Monad m, MonadFail m) => String  -> Int -> REqSettings -> m REqSettings
changeNumberSetting name value reqs
 | name == "mmd"  =  return $ maxMatchDisplay_ value reqs
 | otherwise        =  fail ("changeNumberSetting - unknown field: "++name)
\end{code}


\begin{code}
reqset = "REQSET"
reqsetHDR = "BEGIN "++reqset ; reqsetTRL = "END "++ reqset
mmdKey = "MMD = "
mhtKey = "MHT = "
mhqKey = "MHQ = "
mhfKey = "MHF = "

writeREqSettings :: REqSettings -> [String]
writeREqSettings rqset
  = [ reqsetHDR
    , mmdKey ++ show (maxMatchDisplay rqset)
    , mhtKey ++ show (hideTrivialMatch rqset)
    , mhqKey ++ show (hideTrivialQuantifiers rqset)
    , mhfKey ++ show (hideFloatingVariables rqset)
    , reqsetTRL ]

readREqSettings :: (Monad m, MonadFail m) => [String] -> m (REqSettings, [String])
readREqSettings [] = fail "readREqSettings: no text"
readREqSettings txts
  = do rest1 <- readThis reqsetHDR txts
       (theMMD,rest2) <- readKey mmdKey read rest1
       (theMHT,rest3) <- readKey mhtKey readBool rest2
       (theMHQ,rest4) <- readKey mhqKey readBool rest3
       (theMHF,rest5) <- readKey mhfKey readBool rest4
       rest6 <- readThis reqsetTRL rest5
       return ( matchFilterUpdate
                 ( REqSet theMMD
                          theMHT
                          theMHQ
                          theMHF
                          acceptAll )
              , rest6 )
\end{code}

\newpage
\section{Prover State Type}

Here we simply aggregate the semantic equational-reasoning prover state

\begin{code}
data REqState
 = REqState {
      inDevMode :: Bool -- true if in development mode
    , projectDir  ::  FilePath -- current workspace directory
    , modified    ::  Bool -- True if anything modified but not saved
    -- all below are saved
    , settings    ::  REqSettings
    , theories    ::  Theories
    , currTheory  ::  String
    , liveProofs  ::  LiveProofs
    }

projectDir__ f r = r{projectDir = f $ projectDir r}
projectDir_      = projectDir__ . const
modified__ f r = r{modified = f $ modified r}
modified_      = modified__ . const
changed = modified_ True
settings__ f r = r{settings = f $ settings r}
settings_      = settings__ . const
theories__ f r = r{theories = f $ theories r}
theories_ = theories__ . const
currTheory__ f r = r{currTheory = f $ currTheory r}
currTheory_      = currTheory__ . const
liveProofs__ f r = r{liveProofs = f $ liveProofs r}
liveProofs_      = liveProofs__ . const
\end{code}

\newpage
\section{Writing and Reading State}

\begin{code}
reqstate = "REQSTATE"
reqstateHDR = "BEGIN "++reqstate ; reqstateTLR ="END "++reqstate
currThKEY = "CURRTHEORY = "
\end{code}

\subsection{Write State}

\begin{code}
writeREqState :: REqState -> ([String],[String],NamedTheoryTexts)
writeREqState reqs
  = ( [ reqstateHDR ] ++
      -- writeREqSettings (settings reqs) ++
      thrysTxt ++
      [currThKEY ++ (currTheory reqs)] ++
      writeLiveProofs (liveProofs reqs) ++
      [ reqstateTLR ]
    , writeREqSettings (settings reqs)
    , nmdTxts )
  where (thrysTxt,nmdTxts) = writeTheories (theories reqs)
\end{code}

\subsection{Read State}

We have to split this into two phases:
\begin{code}
readREqState1 :: (Monad m, MonadFail m) => [String]
              -> m ([String],[String])
readREqState1 [] = fail "readREqState1: no text."
readREqState1 txts
  = do rest1 <- readThis reqstateHDR txts
       (thryNms,rest2) <- readTheories1 rest1
       return (thryNms,rest2)

readREqState2 :: (Monad m, MonadFail m) => REqSettings ->  [(String,Theory)]
              -> [String] -> m REqState
readREqState2 _ _ [] = fail "readREqState2: no text."
readREqState2 theSet thMap txts
  = do (thrys,rest1) <- readTheories2 thMap txts
       (cThNm,rest2) <- readKey currThKEY id rest1
       let thylist = fromJust $ getTheoryDeps cThNm thrys
       (lPrfs,rest3) <- readLiveProofs thylist rest2
       readThis reqstateTLR rest3 -- ignore any junk after trailer.
       return $ REqState { inDevMode = False
                         , projectDir = ""
                         , modified = False
                         , settings = theSet
                         , theories = thrys
                         , currTheory = cThNm
                         , liveProofs = lPrfs }
\end{code}

\section{Test Functions}

For \texttt{andIfWanted}

\begin{code}
yes _ _ = True
oddt _ = odd
event _ = even
small _ n = n < 5
big _ n = n > 10

preds     = [  oddt, event, small,   big ]

oddsmall  = [  True, False,  True, False ]
oddbig    = [  True, False, False, True  ]
evensmall = [ False,  True,  True, False ]
evenbig   = [ False,  True, False, True  ]
evens     = [ False,  True, False, False ]
contra    = [ True,   True, False, False ]

litteodd  = run $ zip oddsmall  preds
bigodd    = run $ zip oddbig    preds
tinyeven  = run $ zip evensmall preds
hugeeven  = run $ zip evenbig   preds
justevens = run $ zip evens preds
nope      = run $ zip contra preds

run spec n
 =  f [] n
 where
   f = foldl mrg yes spec
   mrg fltsofar (enabled,flt) = andIfWanted enabled flt fltsofar
\end{code}
