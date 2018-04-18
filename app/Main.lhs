\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2017--18

LICENSE: BSD3, see file LICENSE at reasonEq root
\end{verbatim}
\begin{code}
module Main where

import System.Environment
import System.Console.Haskeline
import Control.Monad.IO.Class
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List
import Data.Maybe
import Data.Char

import NiceSymbols hiding (help)

import Utilities
import LexBase
import Variables
import AST
import VarData
import SideCond
import Binding
import TermZipper
import Proof
import Propositions
import Instantiate
import TestRendering
\end{code}

\begin{code}
name = "reasonEq"
version = "0.5.1.0"
\end{code}

\begin{code}
main :: IO ()
main
  = do args <- getArgs
       if "-g" `elem` args
       then do putStrLn "starting GUI..."
               gui (args \\ ["-g"])
       else do putStrLn "starting REPL..."
               repl args
\end{code}

\newpage
\subsection{System State}

Currently in prototyping mode,
so this is one large record.
Later we will nest things.
In order to support nested records properly,
for every record field \texttt{f :: Rec -> T},
we define \texttt{f\_\_ :: (T -> T) -> Rec -> Rec}
and derive \texttt{f\_ :: T -> Rec -> Rec}.
\begin{code}
data REqState
 = ReqState {
      logic :: TheLogic
    , known :: [VarTable]
    , laws :: [(String,Assertion)]
    , conj :: [(String,Assertion)]
    , goal :: Maybe (String,Assertion)
    , proof :: Maybe LiveProof
    , proofs :: [Proof]
    , focus :: TermZip
    }
logic__  f r = r{logic  = f $ logic r}  ; logic_   = logic__  . const
known__  f r = r{known  = f $ known r}  ; known_   = known__  . const
laws__   f r = r{laws   = f $ laws r}   ; laws_    = laws__   . const
conj__   f r = r{conj   = f $ conj r}   ; conj_    = conj__   . const
goal__   f r = r{goal   = f $ goal r}   ; goal_    = goal__   . const
proof__  f r = r{proof  = f $ proof r}  ; proof_   = proof__  . const
proofs__ f r = r{proofs = f $ proofs r} ; proofs_  = proofs__ . const
focus__  f r = r{focus  = f $ focus r}  ; focus_   = focus__  . const
\end{code}

\begin{code}
initState :: [String] -> IO REqState
initState ["user"]
  = do putStrLn "Running in normal user mode."
       return
         $ ReqState thePropositionalLogic [] [] [] Nothing Nothing [] focusTest
initState []
  = do putStrLn "Running in development mode."
       let reqs = ReqState thePropositionalLogic [propKnown]
                           propLaws propConjs Nothing Nothing [] focusTest
       return reqs

focusTest
  = mkTZ $ f  [ pP === pQ
              , pP ==> pQ
              , Cons P (i _lor) [pR,pQ,pP]
              , pP /\ h [pR, pQ]
              , lnot pR
              , lnot ( ( pP \/ ( pQ === pR ) ) /\ ( pQ ==> pP ) )
              , ( ( pP ==> ( pQ \/ pR ) ) === ( pQ /\ lnot pP ) )
              ]
  where
    i n = fromJust $ ident n
    f ts = Cons P (i "F") ts
    g ts = Cons P (i "G") ts
    h ts = Cons P (i "H") ts
    p n = fromJust $ pVar (Vbl (fromJust $ident n) PredV Static)
    pP = p "P" ; pQ = p "Q" ; pR = p "R"
    t1 === t2  =  Cons P (i _equiv) [t1,t2]
    t1 ==> t2  =  Cons P (i _implies) [t1,t2]
    t1 \/ t2  =  Cons P (i _lor) [t1,t2]
    t1 /\ t2  =  Cons P (i _land) [t1,t2]
    lnot t = Cons P (i _lnot) [t]


summariseREqS :: REqState -> String
summariseREqS reqs
 = intcalNN ":" [ show $ length $ known reqs
                , show $ length $ laws reqs
                , show $ length $ conj reqs
                , case goal reqs of
                   Nothing -> ""
                   _ -> "!"
                , case proof reqs of
                   Nothing -> ""
                   _ -> "!"
                ]
\end{code}

\subsubsection{The Show Command}

Showing logic:
\begin{code}
showLogic logic
  = unlines [ "Truth: "   ++ trTerm 0 (theTrue logic)
            , "Equivalence: " ++ trId (theEqv  logic)
            , "Implication: " ++ trId (theImp  logic)
            , "Conjunction: " ++ trId (theAnd  logic) ]
\end{code}


Showing known variables:
\begin{code}
showKnown vts = unlines $ map trVarTable $ vts
\end{code}


A common idiom si to show a list of items as a numbered list
to make selecting them easier:
\begin{code}
numberList showItem list
  =  unlines $ map (numberItem showItem) $  zip [1..] list
numberItem showItem (i,item)
  =  pad 4 istr ++ istr ++ ". " ++ showItem item
  where istr = show i

pad w str
  | ext > 0    =  replicate ext ' '
  | otherwise  =  ""
  where ext = w - length str
\end{code}


Showing laws:
\begin{code}
showLaws lws  =  numberList (showLaw $ nameWidth lws) lws

nameWidth lws = maximum $ map (length . getName) lws
getName (nm,_) = nm
showLaw w (nm,(t,sc))
  =    ldq ++ nm ++ rdq ++ pad w nm
    ++ "  " ++ trTerm 0 t ++ "  "++trSideCond sc
\end{code}

Showing Goal:
\begin{code}
showGoal Nothing = "no Goal."
showGoal (Just goal) = showLaw 0 goal
\end{code}

Showing Proof:
\begin{code}
showLivePrf Nothing = "no Proof."
showLivePrf (Just proof) = dispLiveProof proof
\end{code}

Showing Proofs:
\begin{code}
showProofs = unlines' . map ( ('\n':) . displayProof )
\end{code}


\newpage
\subsection{GUI Top-Level}
\begin{code}
gui :: [String] -> IO ()
gui args = putStrLn $ unlines
         [ "Welcome to "++name++" "++version
         , "GUI N.Y.I.!"
         , "Goodbye" ]
\end{code}

\newpage
\subsection{REPL Top-Level}
\begin{code}
repl :: [String] -> IO ()
repl args = runInputT defaultSettings
                                 (banner >> (liftIO $ initState args) >>= loop)
banner :: InputT IO ()
banner = outputStrLn $ unlines
 [ "Welcome to the "++name++" "++version++" REPL"
 , "Type '?' for help."
 ]

loop :: REqState -> InputT IO ()
loop reqs = do
   minput <- getInputLine ("rEq."++_equiv++" ")
   case minput of
       Nothing      ->  quit reqs
       Just "quit"  ->  quit reqs
       Just input   ->  docommand reqs (words input) >>= loop

-- may ask for user confirmation, and save? stuff..
quit reqs = outputStrLn "Goodbye!"
\end{code}

REPL command repository types and lookup:
\begin{code}
type Command = [String] -> REqState -> InputT IO REqState
type CommDescr = ( String     -- command name
                 , String     -- short help for this command
                 , String     -- long help for this command
                 , Command )  -- command function
type Commands = [CommDescr]

clookup _ []  =  Nothing
clookup s (cd@(n,_,_,_):rest)
 | s == n     =  Just cd
 | otherwise  =  clookup s rest
\end{code}

Command dispatch:
\begin{code}
docommand reqs [] = return reqs
docommand reqs ("?":what)
 = help reqs what
docommand reqs (cmd:args)
 = case clookup cmd commands of
     Nothing -> outputStrLn ("unknown cmd: '"++cmd++"', '?' for help.")
                 >> return reqs
     Just (_,_,_,c)  ->  c args reqs
\end{code}

Command Help
\begin{code}
help reqs []
  = do outputStrLn "Commands:"
       outputStrLn "'?'     -- this help message"
       outputStrLn "'? cmd' -- help for 'cmd'"
       outputStrLn "Control-D or 'quit'  -- exit program."
       outputStrLn $ unlines $ map shorthelp commands
       return reqs
  where shorthelp (cmd,sh,_,_) = cmd ++ "  -- " ++ sh

help reqs (what:_)
  = case clookup what commands of
     Nothing -> outputStrLn ("unknown cmd: '"++what++"'") >> return reqs
     Just (_,_,lh,_) -> outputStrLn lh >> return reqs
\end{code}


\newpage
\subsection{Command Repository}
\begin{code}
commands :: Commands
commands = [cmdShow,cmdSet,cmdProve,cmdFocus]
\end{code}

\subsubsection{Show Command }
\begin{code}
cmdShow :: CommDescr
cmdShow
  = ( "sh"
    , "show parts of the prover state"
    , unlines
        [ "sh "++shLogic++" - show current logic"
        , "sh "++shKnown++" - show known variables"
        , "sh "++shLaws++" - show current laws"
        , "sh "++shConj++" - show current conjectures"
        , "sh "++shGoal++" - show current goal"
        , "sh "++shLivePrf++" - show current proof"
        , "sh "++shProofs++" - show completed proofs"
        , "sh "++shFocus++" - show current test focus state"
        ]
    , showState )

shLogic = "="
shKnown = "k"
shLaws  = "l"
shConj = "c"
shGoal = "g"
shLivePrf = "p"
shProofs = "P"
shFocus = "f"

showState [cmd] reqs
 | cmd == shLogic  =  doshow reqs $ showLogic $ logic reqs
 | cmd == shKnown  =  doshow reqs $ showKnown $ known reqs
 | cmd == shLaws   =  doshow reqs $ showLaws  $ laws  reqs
 | cmd == shConj   =  doshow reqs $ showLaws  $ conj  reqs
 | cmd == shGoal   =  doshow reqs $ showGoal  $ goal  reqs
 | cmd == shLivePrf  =  doshow reqs $ showLivePrf $ proof reqs
 | cmd == shProofs =  doshow reqs $ showProofs $ proofs reqs
 | cmd == shFocus  =  doshow reqs $ trTermZip $ focus reqs
showState _ reqs   =  doshow reqs "unknown 'show' option."

doshow reqs str
 = do outputStrLn str
      return reqs
\end{code}

\subsubsection{Set Command}
\begin{code}
cmdSet
  = ( "set"
    , "set parts of prover state"
    , unlines
       [ "set goal name - set goal to named conjecture"]
    , setState )

setState [what,name] reqs
 | what == "goal"  =  setgoal reqs name
setState _ reqs = doshow reqs "unknown 'set' option"

setgoal reqs arg
  | all isDigit arg
    = case nlookup (read arg) $ conj reqs of
        Nothing -> doshow reqs ("conjecture no."++arg++" not found.")
        Just cnj -> return $ goal_ (Just cnj) reqs
  | otherwise
    = case alookup arg $ conj reqs of
        Nothing -> doshow reqs ("conjecture '"++name++"' not found.")
        Just cnj -> return $ goal_ (Just cnj) reqs

-- list lookup by number [1..]
nlookup i things
 | i < 1 || null things  =  Nothing
nlookup 1 (thing:rest)   =  Just thing
nlookup i (thing:rest)   =  nlookup (i-1) rest

-- association list lookup
alookup name [] = Nothing
alookup name (thing@(n,_):rest)
  | name == n  =  Just thing
  | otherwise  =  alookup name rest
\end{code}

\subsubsection{Prove Command}
\begin{code}
cmdProve
  = ( "prove"
    , "do a proof"
    , unlines
       [ "prove - prove current goal"
       , "if no live proof present, then start one,"
       , "otherwise, jump to existing live proof."
       ]
    , doProof )

doProof _ reqs
  = case proof reqs of
      Nothing
       ->  do outputStrLn "No current proof, will try to start one."
              case goal reqs of
                Nothing -> doshow reqs "No goal to prove, please add one."
                Just (nm,cnj)
                 -> do outputStrLn ("Starting Proof of '"++nm++"'")
                       proofREPL reqs (startProof nm cnj)
      Just proof
       ->  do outputStrLn "Back to current proof."
              proofREPL reqs proof
\end{code}

\newpage
\subsubsection{Proof REPL}

This repl runs a proof.
\begin{code}
proofREPL reqs proof
 = do outputStrLn $ dispLiveProof proof
      if proofComplete (logic reqs) proof
       then
         do outputStrLn "Proof Complete"
            let prf = finaliseProof proof
            outputStrLn $ displayProof prf
            return (proofs__ (prf:) reqs)
       else
         do minput <- getInputLine "proof: "
            case minput of
              Nothing -> back reqs proof
              Just "e" -> back reqs proof
              Just "?" -> proofHelp reqs proof
              Just pcmd -> proofCommand reqs proof (words pcmd)

back reqs proof
 = doshow (proof_ (Just proof) reqs) "Back to main REPL, Proof still current."

proofHelp reqs proof
  = do outputStrLn $ unlines
         [ "d n - down n"
         , "u - up"
         , "m - match laws"
         , "a n - apply match n"
         , "i - instantiate a true focus with an axiom"
         , "e - exit to top REPL, keeping proof"
         , "X - abandon proof"
         ]
       proofREPL reqs proof

proofCommand reqs proof ["d",nstr] = goDown reqs proof $ readInt nstr
proofCommand reqs proof ["u"] = goUp reqs proof
proofCommand reqs proof ["m"] = matchLawCommand reqs proof
proofCommand reqs proof ["a",nstr] = applyMatch reqs proof $ readInt nstr
proofCommand reqs proof ["i"] = lawInstantiateProof reqs proof
proofCommand reqs proof ["X"] = abandonProof reqs proof
proofCommand reqs proof pcmds
  = do outputStrLn ("proofCommand '"++unwords pcmds++"' unknown")
       proofREPL reqs proof
\end{code}

Focus movement commands
\begin{code}
goDown reqs proof@(nm, asn, tz, dpath, sc, _, steps ) i
  = let (ok,tz') = downTZ i tz in
    if ok
    then proofREPL reqs (nm, asn, tz', dpath++[i], sc, [], steps)
    else proofREPL reqs proof

goUp reqs proof@(nm, asn, tz, dpath, sc, _, steps )
  = let (ok,tz') = upTZ tz in
    if ok
    then proofREPL reqs (nm, asn, tz', init dpath, sc, [], steps)
    else proofREPL reqs proof
\end{code}

\newpage
Law Matching
\begin{code}
matchLawCommand reqs proof@(nm, asn, tz, dpath, sc, _, steps )
  = do outputStrLn ("Matching "++trTerm 0 goalt)
       let matches = matchLaws (logic reqs) (known reqs) goalt (laws reqs)
       outputStrLn $ displayMatches matches
       proofREPL reqs (nm, asn, tz, dpath, sc, matches, steps)
  where goalt = getTZ tz

applyMatch reqs proof@(nm, asn, tz, dpath, sc, matches, steps ) i
  = case alookup i matches of
     Nothing -> do outputStrLn ("No match numbered "++ show i)
                   proofREPL reqs proof
     Just (_,(lnm,lasn,bind,repl))
      -> case instantiate bind repl of
          Nothing -> do outputStrLn "Apply failed !"
                        proofREPL reqs proof
          Just brepl
            -> do outputStrLn ("Applied law '"++lnm++"' at "++show dpath)
                  proofREPL reqs (nm, asn, (setTZ brepl tz), dpath, sc, []
                                 , (("apply "++lnm,bind,dpath), exitTZ tz):steps)
\end{code}

Replacing \textit{true} by a law, with unknown variables
suitably instantiated.
\begin{code}
lawInstantiateProof reqs proof@(nm, asn, tz, dpath, sc, matches, steps)
  | currt /= true
    = do outputStrLn ("Can only instantiate an law over "++trTerm 0 true)
         proofREPL reqs proof
  | otherwise
    = do outputStrLn $ showLaws $ laws reqs
         minput <- getInputLine "Pick a law : "
         case minput of
           Just str@(_:_) | all isDigit str
             -> case nlookup (read str) $ laws reqs of
                 Just law@(nm,asn)
                   -> do outputStrLn ("Law Chosen: "++nm)
                         instantiateLaw reqs proof law
                 _ -> proofREPL reqs proof
           _ -> proofREPL reqs proof
  where
    currt = getTZ tz; true = theTrue $ logic reqs

instantiateLaw reqs proof@(pnm, asn, tz, dpath, psc, matches, steps)
                    law@(lnm,(lawt,lsc))
 = do lbind <- generateLawInstanceBind (known reqs) (exitTZ tz) psc law
      case instantiateSC lbind lsc of
        Nothing -> do outputStrLn "instantiated law side-cond is false"
                      proofREPL reqs proof
        Just ilsc
          -> do outputStrLn $ trBinding lbind
                case mrgSideCond psc ilsc of
                  Nothing -> do outputStrLn "side-condition merge failed"
                                proofREPL reqs proof
                  Just nsc ->
                    do  ilawt <- instantiate lbind lawt
                        proofREPL reqs ( pnm, asn
                                       , setTZ ilawt tz
                                       , dpath, nsc
                                       , matches
                                       , (("instantiate "++lnm,lbind,dpath)
                                          , exitTZ tz)
                                          :steps)
\end{code}

\newpage

Dialogue to get law instantiation binding.
We want a binding for every unknown variable in the law.
We display all such unknowns, and then ask for instantiations.
\begin{code}
generateLawInstanceBind vts gterm gsc law@(lnm,(lawt,lsc))
 = do let lFreeVars = stdVarSetOf $ S.filter (isUnknownGVar vts)
                                  $ freeVars lawt
      outputStrLn ("Free unknown law variables: "++trVariableSet lFreeVars)
      let subGTerms = reverse $ subTerms gterm
      -- let subGVars = map theVar $ filter isVar subGTerms
      requestInstBindings emptyBinding subGTerms $ S.toList lFreeVars
\end{code}

\begin{code}
requestInstBindings bind gterms []  =  return bind
requestInstBindings bind gterms vs@(v:vrest)
 = do outputStrLn "Goal sub-terms:"
      outputStrLn $ numberList (trTerm 0) gterms
      minput <- getInputLine ("Binding for "++trVar v++" ?")
      case minput of
       Just str@(_:_) | all isDigit str
         -> case nlookup (read str) $ gterms of
             Just gterm
               -> do bind' <- bindVarToTerm v gterm bind
                     requestInstBindings bind' gterms vrest
             _ -> requestInstBindings bind gterms vs
       _ -> requestInstBindings bind gterms vs
\end{code}

\newpage
Abandoning a proof, losing all work so far.
\begin{code}
abandonProof reqs proof
 = do yesno <- getInputLine "Abandon ! Are you sure (Y/n) ? "
      case yesno of
        Just "Y" -> doshow (proof_ Nothing reqs)
                      "Back to main REPL, Proof abandoned."
        _ -> proofREPL reqs proof
\end{code}

\newpage
\subsubsection{Focus test Command}
\begin{code}
cmdFocus
  = ( "f"
    , "focus test"
    , unlines
       [ "Focus Test"
       , "use keys to go up and down"
       ]
    , doFocusTest )

doFocusTest _ reqs
  = do fcs' <- focusREPL $ (False, focus reqs)
       return $ focus_ fcs' reqs

focusREPL fs@(chgd,fcs)
 = do outputStrLn (trTermZip fcs ++ "  changed="++show chgd)
      minput <- getInputLine "u, d n, x :- "
      case minput of
        Nothing -> return fcs
        Just "x" -> return fcs
        Just "u" -> focusREPL (upTZ fcs)
        Just ('d':rest) -> focusREPL (downTZ (s2int rest) fcs)
        _ -> focusREPL fs


s2int str
 | all isDigit str'   =  read str'
 | otherwise          =  0
 where str' = trim str
\end{code}
