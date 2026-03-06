\chapter{Pretty Terms}
\begin{code}
module PrettyTerms (
  ppTermZip
) 
where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
import Data.Maybe
import Symbols
import Debug.Trace
import PrettyPrint
import AST
import TestRendering
-- import CalcTypes
-- import PrettyMark
-- import StdPrecedences
\end{code}

\section{Pretty-printing a Term Zipper}

\begin{code}
ppTermZip ww tz = trTermZip tz
\end{code}

\section{Marking}\label{hb:marking}

\subsection{Marking}

We shall mark predicates with zero or more integers:
\begin{code}
type Mark = Int
type Marks = [Mark]
\end{code}

Marking is done by constructing a tree-structure
that matches the predicate structure:
\begin{code}
data MTree = MT Marks [MTree] deriving (Eq, Ord, Show)
\end{code}

Marked predicates are marks paired with a predicate,
denoted by the \texttt{MTerm} datatype:
\begin{code}
type MTerm = ( Term, MTree )
\end{code}

\begin{code}
buildMarks :: Term -> MTerm
buildMarks term = undefined
-- buildMarks pr@(Comp _ prs)
-- = ( pr, MT [] mts )
--   where mts = map (snd . buildMarks) prs
--buildMarks pr@(PSub spr _)
-- = ( pr, MT [] [mt] )
--   where mt = snd $ buildMarks spr
-- buildMarks pr = ( pr, MT [] [] )
\end{code}



Now, prettiness..

We need a function from markings to styles:
\begin{code}
type MarkStyle = Int -> Maybe Style

noStyles :: MarkStyle
noStyles = const Nothing
\end{code}

\begin{code}
plainShow :: Int -> Dict -> Term -> String
plainShow w d pr = render w $ showp d noStyles 0 pr

type Dict = () -- placeholder

pmdshow :: Int -> Dict -> MarkStyle -> MTerm -> String
pmdshow w d msf mpr = render w $ mshowp d msf 0 mpr

pdshow :: Int -> Dict -> MarkStyle -> Term -> String
pdshow w d msf pr = render w $ mshowp d msf 0 $ buildMarks pr
\end{code}

Pretty-printing predicates.
\begin{code}
mshowp :: Dict -> MarkStyle -> Int -> MTerm -> PP
mshowp d msf p mpr@( pr, MT ms _)
 = sshowp $ catMaybes $ map msf ms
 where
  sshowp []  =  mshowp0 d msf p mpr
  sshowp (s:ss) = pps s $ sshowp ss

mshowp0 :: Dict -> MarkStyle -> Int -> MTerm -> PP
mshowp0 _ _ _ _ = undefined
-- mshowp0 d _ _ (T, _)  = ppa _true
-- mshowp0 d _ _ (F, _)  = ppa _false
-- mshowp0 d _ _ (PVar p, _)  = ppa p
-- mshowp0 d _ p (Equal e1 e2, _)
--   = paren p precEq
--       $ ppopen' (ppa " = ")
--                 [ppa $ edshow d e1, ppa $ edshow d e2]
-- mshowp0 d _ p (Atm e, _) = ppa $ edshow d e
-- mshowp0 d msf p (PSub pr sub, MT _ mts)
--   = pplist $ [ subCompShow msf mts d precSbs 1 pr
--              , ppa $ showSub d sub ]

-- mshowp0 d msf p (Comp cname pargs, MT _ mts)
-- = case plookup cname d of
--    Just (PredEntry _ showf _ _ _)
--       ->  showf (subCompShow msf mts d) d p pargs
 --   _  ->  stdCshow d msf cname mts pargs


type SubCompPrint
 = Int       -- precedence level for sub-component
   -> Int    -- sub-component number
   -> Term -- sub-component
   -> PP

subCompShow :: MarkStyle -> [MTree] -> Dict
            -> SubCompPrint
subCompShow msf mts d p i subpr = undefined
--subCompShow msf mts d p i subpr
-- | 0 < i && i <= length mts
--   = mshowp d msf p (subpr, mts !!(i-1))
-- | otherwise
--   = mshowp d msf p $ buildMarks subpr

stdCshow :: Dict -> MarkStyle -> String -> [MTree] -> [Term]
         -> PP
stdCshow d msf cname mts pargs
 = pplist [ ppa cname
          , ppclosed "(" ")" ","
            $ ppwalk 1 (subCompShow msf mts d 0) pargs ]

ppwalk :: Int -> (Int -> Term -> PP) -> [Term] -> [PP]
ppwalk _ _ []            =  []
ppwalk i sCS (arg:args)  =  (sCS i arg) : ppwalk (i+1) sCS args

showp :: Dict -> MarkStyle -> Int -> Term -> PP
showp d ms p pr = mshowp d ms p $ buildMarks pr

-- ppSuper d e = _supStr $ edshow d e
\end{code}

\section{Debugging Aids}

\begin{code}
dbg str x = trace (str++show x) x
cdbg d str pr = trace (str++plainShow 80 d pr) pr
csdbg d str prs = trace (str++unlines (map (plainShow 80 d) prs)) prs
\end{code}
