\section{\reasonEq\ State}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--21

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module REqState ( REqSettings(..)
                , maxMatchDisplay__, maxMatchDisplay_
                , rEqSettingStrings, showSettingStrings, showSettings
                , changeSettings
                , REqState(..)
                , modified__, modified_, changed
                , logic__, logic_, theories__, theories_
                , settings__, settings_
                , currTheory__, currTheory_, liveProofs__, liveProofs_
                , writeREqState, readREqState1, readREqState2
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
import WriteRead
import TermZipper
import Laws
import Proofs
import Theories
import Sequents
import LiveProofs
\end{code}

\subsubsection{Settings}

For now,
the only setting is one for the maximum number of matches displayed.

\begin{code}
data REqSettings
  = REqSet {
       maxMatchDisplay :: Int -- mmd
     }

maxMatchDisplay__ f r = r{maxMatchDisplay = f $ maxMatchDisplay r}
maxMatchDisplay_      = maxMatchDisplay__ . const
\end{code}

For every setting we provide both a short and long string,
the first for use in commands, the second for display
\begin{code}
type SettingStrings = (String,String,String) -- short,type,long
rEqSettingStrings = [ ("mmd","Number","Max. Match Display")
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
\end{code}

\begin{code}
changeSettings :: Monad m => String -> String -> REqSettings -> m REqSettings
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
changeSetting :: Monad m => SettingStrings  -> String -> REqSettings
                         -> m REqSettings
changeSetting (short,typ,_) valstr reqs
 | typ == "Number"  =  changeNumberSetting short (readInt valstr) reqs
 | otherwise        =  fail ("changeSetting - unknown type: "++typ)
\end{code}

\begin{code}
changeNumberSetting :: Monad m => String  -> Int -> REqSettings -> m REqSettings
changeNumberSetting name value reqs
 | name == "mmd"  =  return $ maxMatchDisplay_ value reqs
 | otherwise        =  fail ("changeNumberSetting - unknown field: "++name)
\end{code}


\begin{code}
reqset = "REQSET"
reqsetHDR = "BEGIN "++reqset ; reqsetTRL= "END "++ reqset
mmdKey = "MMD = "

writeREqSettings :: REqSettings -> [String]
writeREqSettings rqset
  = [ reqsetHDR
    , mmdKey ++ show (maxMatchDisplay rqset)
    , reqsetTRL ]

readREqSettings :: Monad m => [String] -> m (REqSettings, [String])
readREqSettings [] = fail "readREqSettings: no text"
readREqSettings txts
  = do rest1 <- readThis reqsetHDR txts
       (theMMD,rest2) <- readKey mmdKey read rest1
       rest3 <- readThis reqsetTRL rest2
       return $ (REqSet theMMD, rest3)
\end{code}


\subsection{Prover State Type}

Here we simply aggregate the semantic equational-reasoning prover state

\begin{code}
data REqState
 = REqState {
      inDevMode :: Bool -- true if in development mode
    , projectDir  ::  FilePath -- current workspace directory
    , modified    ::  Bool -- True if anything modified but not saved
    -- all below are saved
    , settings    ::  REqSettings
    , logicsig    ::  LogicSig
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
logic__  f r = r{logicsig = f $ logicsig r}
logic_    = logic__ . const
theories__ f r = r{theories = f $ theories r}
theories_ = theories__ . const
currTheory__ f r = r{currTheory = f $ currTheory r}
currTheory_      = currTheory__ . const
liveProofs__ f r = r{liveProofs = f $ liveProofs r}
liveProofs_      = liveProofs__ . const
\end{code}

\subsection{Writing and Reading State}

\begin{code}
reqstate = "REQSTATE"
reqstateHDR = "BEGIN "++reqstate ; reqstateTLR ="END "++reqstate
currThKEY = "CURRTHEORY = "
\end{code}

\subsubsection{Write State}

\begin{code}
writeREqState :: REqState -> ([String],NamedTheoryTexts)
writeREqState reqs
  = ( [ reqstateHDR ] ++
      writeREqSettings (settings reqs) ++
      writeSignature (logicsig reqs) ++
      thrysTxt ++
      [currThKEY ++ (currTheory reqs)] ++
      writeLiveProofs (liveProofs reqs) ++
      [ reqstateTLR ]
    , nmdTxts )
  where (thrysTxt,nmdTxts) = writeTheories (theories reqs)
\end{code}

\subsubsection{Read State}

We have to split this into two phases:
\begin{code}
readREqState1 :: Monad m => [String]
              -> m ((REqSettings,LogicSig,[String]),[String])
readREqState1 [] = fail "readREqState1: no text."
readREqState1 txts
  = do rest1 <- readThis reqstateHDR txts
       (theSet,rest2) <- readREqSettings rest1
       (theSig,rest3) <- readSignature rest2
       (thryNms,rest4) <- readTheories1 rest3
       return ((theSet,theSig,thryNms),rest4)

readREqState2 :: Monad m => REqSettings ->  LogicSig -> [(String,Theory)]
              -> [String] -> m REqState
readREqState2 _ _ _ [] = fail "readREqState2: no text."
readREqState2 theSet theSig thMap txts
  = do (thrys,rest1) <- readTheories2 thMap txts
       (cThNm,rest2) <- readKey currThKEY id rest1
       let thylist = fromJust $ getTheoryDeps cThNm thrys
       (lPrfs,rest3) <- readLiveProofs thylist rest2
       readThis reqstateTLR rest3 -- ignore any junk after trailer.
       return $ REqState { inDevMode = False
                         , projectDir = ""
                         , modified = False
                         , settings = theSet
                         , logicsig = theSig
                         , theories = thrys
                         , currTheory = cThNm
                         , liveProofs = lPrfs }
\end{code}
