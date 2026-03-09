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
import LexBase
import AST
import TermZipper
import SizedStrings
import TestRendering

import Debugger
\end{code}

\newpage
\section{Pretty-printing a Term Zipper}

Top level function definitions for the zipper:
\begin{code}
ppTermZip, ppTermZipU :: Int      -- window width
                      -> TermZip  -- term zipper
                      -> String   -- pretty string
ppTermZip  = pptz trId
ppTermZipU = pptz trIdU

-- if window width is zero, just render the term without linebreaks
pptz trid 0  (t,wayup) = trterm trid    0 $ exitTZ (markfocus t,wayup)
pptz trid ww (t,wayup) = ppterm trid ww 0 $ exitTZ (markfocus t,wayup)
\end{code}

Top level functions for a term,
which basically transforms it to the \h{SS} type,
and then uses the window-width to guide the line layout.
\begin{code}
ppTerm, ppTermU :: Int     -- window width
                -> Int     -- top precendence level
                -> Term    -- term
                -> String  -- pretty string
ppTerm  = ppterm trId
ppTermU = ppterm trIdU

ppterm :: (Identifier -> String) -- renders identifiers as strings
       -> Int -> Int -> Term -> String
ppterm trid ww p t = mklayout ww $ mkss trid p t 
\end{code}

\section{Render as Sized Strings}

\begin{code}
mkss :: (Identifier -> String) -> Int -> Term -> SS
\end{code}

\subsection*{Constructor Terms}

Here we effectively re-implement the definition of \h{TestRendering.trterm}.

We start with some pre-defined \h{SS} values:
\begin{code}
ss_lpar = ssa "(" ; ss_rpar = ssa ")"
\end{code}

$$ \lnot t \quad \lnot (t) \qquad  (-t) \quad -t $$
\begin{code}
mkss trid p (Cons typ sb i@(Identifier nm _) [t])
  | i == focusMark  =  sss styleMagenta $ mkss trid p t
  | nm == "not"     =  mkss_not nm t
  | nm == "neg"     =  mkss_neg nm t
  where
    ss_nm    =  ssa nm
    ss_0_t   =  mkss trid 0  t
    ss_99_t  =  mkss trid 99 t
    mkss_not nm t
      | isAtomic t  =  sslist [ss_nm,ss_99_t]
      | otherwise   =  sslist [ss_nm,ss_lpar,ss_0_t,ss_rpar]
    mkss_neg nm t
      | isAtomic t  =  sslist [ss_lpar,ss_nm,ss_0_t,ss_rpar]      
      | otherwise   =  sslist [ss_nm,ss_99_t]
\end{code}

\subsection{Not Yet Done}
\begin{code}
-- mkss trid p (Bnd  typ n vs tm)          = ssa "B typ n vs tm"
-- mkss trid p (Lam  typ n vl tm)          = ssa "L typ n vl tm"
-- mkss trid p (Cls      n    tm)          = ssa "X n tm"
-- mkss trid p (Sub  typ      tm s)        = ssa "S typ tm s"
-- mkss trid p (Iter typ sa na si ni lvs)  = ssa "I typ sa na si ni lvs"
\end{code}

\subsection*{Basic Terms}
Remaining term cases are atomic, so become \h{SSA}:
\begin{code}
mkss trid p t = ssa (trterm trid p t) 
\end{code}

\section{Perform Width-based Layout}

\begin{code}
mklayout :: Int -> SS -> String
mklayout ww (SS _ (SSA s)) = s -- for now
mklayout ww ss = ss2str [] ss
\end{code}

% \section{Marking}\label{hb:marking}

% \subsection{Marking}

% We shall mark predicates with zero or more integers:
% \begin{code}
% type Mark = Int
% type Marks = [Mark]
% \end{code}

% Marking is done by constructing a tree-structure
% that matches the predicate structure:
% \begin{code}
% data MTree = MT Marks [MTree] deriving (Eq, Ord, Show)
% \end{code}

% Marked predicates are marks paired with a predicate,
% denoted by the \h{MTerm} datatype:
% \begin{code}
% type MTerm = ( Term, MTree )
% \end{code}

% \begin{code}
% buildMarks :: Term -> MTerm
% buildMarks term = undefined
% -- buildMarks pr@(Comp _ prs)
% -- = ( pr, MT [] mts )
% --   where mts = map (snd . buildMarks) prs
% --buildMarks pr@(PSub spr _)
% -- = ( pr, MT [] [mt] )
% --   where mt = snd $ buildMarks spr
% -- buildMarks pr = ( pr, MT [] [] )
% \end{code}



% Now, prettiness..

% We need a function from markings to styles:
% \begin{code}
% type MarkStyle = Int -> Maybe Style

% noStyles :: MarkStyle
% noStyles = const Nothing
% \end{code}

% \begin{code}
% plainShow :: Int -> Dict -> Term -> String
% plainShow w d pr = render w $ showp d noStyles 0 pr

% type Dict = () -- placeholder

% pmdshow :: Int -> Dict -> MarkStyle -> MTerm -> String
% pmdshow w d msf mpr = render w $ mshowp d msf 0 mpr

% pdshow :: Int -> Dict -> MarkStyle -> Term -> String
% pdshow w d msf pr = render w $ mshowp d msf 0 $ buildMarks pr
% \end{code}

% Pretty-printing predicates.
% \begin{code}
% mshowp :: Dict -> MarkStyle -> Int -> MTerm -> SS
% mshowp d msf p mpr@( pr, MT ms _)
%  = sshowp $ catMaybes $ map msf ms
%  where
%   sshowp []  =  mshowp0 d msf p mpr
%   sshowp (s:ss) = pps s $ sshowp ss

% mshowp0 :: Dict -> MarkStyle -> Int -> MTerm -> SS
% mshowp0 _ _ _ _ = undefined
% -- mshowp0 d _ _ (T, _)  = ssa _true
% -- mshowp0 d _ _ (F, _)  = ssa _false
% -- mshowp0 d _ _ (PVar p, _)  = ssa p
% -- mshowp0 d _ p (Equal e1 e2, _)
% --   = paren p precEq
% --       $ ppopen' (ssa " = ")
% --                 [ssa $ edshow d e1, ssa $ edshow d e2]
% -- mshowp0 d _ p (Atm e, _) = ssa $ edshow d e
% -- mshowp0 d msf p (PSub pr sub, MT _ mts)
% --   = pplist $ [ subCompShow msf mts d precSbs 1 pr
% --              , ssa $ showSub d sub ]

% -- mshowp0 d msf p (Comp cname pargs, MT _ mts)
% -- = case plookup cname d of
% --    Just (PredEntry _ showf _ _ _)
% --       ->  showf (subCompShow msf mts d) d p pargs
%  --   _  ->  stdCshow d msf cname mts pargs


% type SubCompPrint
%  = Int       -- precedence level for sub-component
%    -> Int    -- sub-component number
%    -> Term -- sub-component
%    -> SS

% subCompShow :: MarkStyle -> [MTree] -> Dict
%             -> SubCompPrint
% subCompShow msf mts d p i subpr = undefined
% --subCompShow msf mts d p i subpr
% -- | 0 < i && i <= length mts
% --   = mshowp d msf p (subpr, mts !!(i-1))
% -- | otherwise
% --   = mshowp d msf p $ buildMarks subpr

% stdCshow :: Dict -> MarkStyle -> String -> [MTree] -> [Term]
%          -> SS
% stdCshow d msf cname mts pargs
%  = pplist [ ssa cname
%           , ppclosed "(" ")" ","
%             $ ppwalk 1 (subCompShow msf mts d 0) pargs ]

% ppwalk :: Int -> (Int -> Term -> SS) -> [Term] -> [SS]
% ppwalk _ _ []            =  []
% ppwalk i sCS (arg:args)  =  (sCS i arg) : ppwalk (i+1) sCS args

% showp :: Dict -> MarkStyle -> Int -> Term -> SS
% showp d ms p pr = mshowp d ms p $ buildMarks pr

% -- ppSuper d e = _supStr $ edshow d e
% \end{code}

% \section{Debugging Aids}

% \begin{code}
% dbg str x = trace (str++show x) x
% cdbg d str pr = trace (str++plainShow 80 d pr) pr
% csdbg d str prs = trace (str++unlines (map (plainShow 80 d) prs)) prs
% \end{code}
