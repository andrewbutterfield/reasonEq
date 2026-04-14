\chapter{Pretty Terms}
\begin{code}
module PrettyTerms (
  ppTermZip
) 
where
import Utilities
import qualified Data.Set as S
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
We start with some pre-defined \h{SS} values:
\begin{code}
ss_comma  =  ssa ","     ;  ss_semi  =  ssa ";"
ss_bar    =  ssa "|"
ss_lpar   =  ssa "("     ;  ss_rpar  =  ssa ")"
ss_lbrc   =  ssa "{"     ;  ss_rbrc  =  ssa "}"
ss_lngl   =  ssa _langle ;  ss_rngl  =  ssa _rangle
\end{code}


\section{Render as Sized Strings}

\begin{code}
mkss :: (Identifier -> String) -> Int -> Term -> SS
\end{code}
Here we effectively re-implement the definition of \h{TestRendering.trterm}.
In the sequel we use the following notation for terms:
\begin{description}
\item[Arbitrary] $t, t_i, \dots$
\item[Generic Atomic] $a, a_i, \dots$
\item[Non Atomic] $T, T_i, \dots$
\item[Relation] $P, Q, R, \dots P_i, \dots$
\item[State Predicate] $p, p', q, q', r, r',\dots, p_i, \dots$
\item[Expression] $e, f, g, e', f', g',\dots, e_i, \dots$
\item[Boolean] $b, b', c, c', \dots, b_i, \dots$
\end{description}

\subsection{Atomic Terms}

\begin{code}
mkss trid p (Val tk k)  =  ssa $ trValue k
mkss trid p (Var tk v)  =  ssa $ trVar v
mkss trid p (VTyp t v)  =  ssa ( "("++trVar v++":"++trType t++")" )
\end{code}


\subsection{Constructor Terms}

We have a lot of partial special cases, 
depending on the constructor name, and the number of sub-terms.
By partial we mean that we match against specific names and numbers,
but fall through if those matches fail, to try other cases.


\textbf{
May want lookup tables to match \h{Cons Identifier}s to a key string
(e.g. \h{"not"} maps to $\lnot$).
}

\subsubsection{Single Sub-Term}

A \h{Cons}-node with one subterm
may need special handling.
A marked focus term needs highlighting, 
while logic and arithmetic negation require specific handling.
$$ {\h{$t$}} \qquad \lnot a \quad \lnot (T) \qquad  (-a) \quad -T $$
\begin{code}
mkss trid p (Cons _ _ i@(Identifier nm _) [t])
  | i == focusMark  =  sss styleMagenta $ mkss trid p t
  | nm == "not"     =  mkss_not nm t  -- lookup tables here ?
  | nm == "neg"     =  mkss_neg nm t
  where
    ss_nm    =  ssa (trid i)  
    ss_0_t   =  mkss trid 0  t
    ss_99_t  =  mkss trid 99 t
    mkss_not nm t  
      | isAtomic t  =  sslist [ss_nm,ss_99_t]
      | otherwise   =  sslist [ss_nm,ss_lpar,ss_0_t,ss_rpar]
    mkss_neg nm t
      | isAtomic t  =  sslist [ss_lpar,ss_nm,ss_0_t,ss_rpar]      
      | otherwise   =  sslist [ss_nm,ss_99_t]
\end{code}



\subsubsection{Infix-like Ternary Operators}

E.g, the UTP if-then-else:
$$ p \cond b q $$
\begin{code}
mkss trid ctxtp (Cons _ _ opn@(Identifier nm _) [p,b,q])
 | nm == "cond"  
    =  ssBracketIf 
         (opp <= ctxtp)
         (sslist [ ss_opp_p, lif, ss_0_b, rif, ss_opp_q ] )
 where
   lif = ssa $ trid $ jId "lif" ; rif = ssa $ trid $ jId "rif"
   ss_opp_p =  mkss trid opp p
   ss_0_b   =  mkss trid 0   b
   ss_opp_q =  mkss trid opp q
   (opp,_) = opkind nm
\end{code}

% \subsubsection{Infix Binary Operators}

% $$ p \circledast q    \qquad\textit{v.s.} \qquad (p \circledast q) $$

% We ensure that sub-terms are rendered with the infix operator precedence
% as their context precedence.
% \begin{code}
% mkss trid ctxtp (Cons _ _ opi@(Identifier opn _) [t1,t2])
%  | isOp  =  ssBracketIf 
%               (opp <= ctxtp)
%               (sslist [ ss_opp_t1, ss_opn, ss_opp_t2 ] )
%  where
%    ss_opp_t1 = mkss trid opp t1
%    ss_opn    = ssa $ pad $ trid opi
%    ss_opp_t2 = mkss trid opp t2
%    prcs@(opp,fixity) = opkind opn
%    isOp = fixity /= NotInfix
% \end{code}

\subsubsection{Left-Associated Binary Operators}

Rendering a left-infix operator when the first sub-term uses the same operator
$$op(\seqof{op(es)}\cat fs) = op(es\cat fs)$$
\begin{code}
mkss trid ctxtp (Cons tk sub opn@(Identifier nm _) 
                (Cons _ _ opn' ts':ts))
  | isLFix && opn == opn'  =  mkss trid ctxtp $ Cons tk sub opn (ts'++ts)
  where
    prcs@(opp,fixity) = opkind nm
    isLFix = fixity == LAssoc
\end{code}

\newpage

\subsubsection{Right-Associated Binary Operators}

Rendering a right-infix operator when the last sub-term uses the same operator
$$op(es \cat \seqof{op(fs)}) = op(es\cat fs)$$
\begin{code}
mkss trid ctxtp (Cons tk sub opn@(Identifier nm _) ts@(_:_:_))
 | isRFix
   = case tE of
       (Cons _ _ opn' ts') | opn == opn'  
          ->  mkss trid ctxtp $ Cons tk sub opn (tsI++ts')
       _  ->  ssBracketIf (opp <= ctxtp)
                  $ ssopen (pad $ trid opn)
                  $ map (mkss trid opp) ts
 where
   prcs@(opp,fixity)  =  opkind nm
   isRFix             =  fixity == RAssoc
   (tsI,tE)           =  splitAtEnd ts
   splitAtEnd [x,y] = ([x],y)
   splitAtEnd (x:xs) 
     =  let (xs',y) = splitAtEnd xs
        in (x:xs',y)
\end{code}

\subsubsection{Infix with two or more arguments}

$$ p \circledast q \circledast \dots \circledast r
   \qquad\textit{v.s.} \qquad 
   (p \circledast q \circledast \dots \circledast r)
$$
We ensure that sub-terms are rendered with the infix operator precedence
as their context precedence.
\begin{code}
mkss trid ctxtp (Cons tk _ opn@(Identifier nm _) ts@(_:_:_))
 | isOp  =  ssBracketIf (opp <= ctxtp)
                        $ ssopen (pad $ trid opn) 
                        $ map (mkss trid opp) ts
 where
   prcs@(opp,fixity) = opkind nm
   isOp = fixity /= NotInfix
\end{code}

\subsubsection{Containing Constructs}

We have some containers such as sets, lists and UTCP roots:
\begin{code}
mkss trid _ (Cons tk _ n ts)
  | n == jId "set"  =  ssc ss_lbrc ss_rbrc ss_comma mkssts 
  | n == jId "seq"  =  ssc ss_lngl ss_rngl ss_comma mkssts
  | n == jId "r"    =  ssc ssnul ssnul ssnul (ssa "r":(map trRoot ts))
  where
    mkssts =  map (mkss trid 0) ts
    trRoot (Val _ (Integer i))  =  ssa $ show i
    trRoot (Val _ (Boolean b))  =  if b then ssa "!" else ssnul
    trRoot _                    =  ssnul
\end{code}

\subsubsection{Tailored Function Application}

We sometimes tailor standard functional application a little bit,
i.e., $X$ and $A$ in the UTCP theory.
\begin{code}
mkss trid _ (Cons tk _ n ts)
  | n `elem` [jId "A", jId "X"]
  =  sslist [ ssa (trid n), ssc ss_lpar ss_rpar ss_bar mkssts]
  where mkssts = map (mkss trid 99) ts
\end{code}

\subsubsection{Function Application}


Any other constructor is rendered as a standard function call:
$$ f(t_1,\dots,t_n)$$
\begin{code}
mkss trid _ (Cons _ _ fn@(Identifier f _) ts)
  =  sslist [ ssa (trid fn), ssc ss_lpar ss_rpar ss_comma mkssts ]
  where mkssts = map (mkss trid 0) ts
\end{code}

\subsubsection{Quantifiers}

A quantifier has the general form:
$$ \mathcal Q v_1,\dots,v_2 \bullet t$$
The difference between set-oriented binds ($\forall$,$\exists$,\dots)
and list-oriented binds ($\lambda$,\dots) is semantic,
but that is not relevant for pretty-printing.
\begin{code}
mkss trid p (Bnd  typ n vs tm) = mkQuantifier trid p n (S.toList vs) tm
mkss trid p (Lam  typ n vl tm) = mkQuantifier trid p n vl            tm
\end{code}


\subsection*{Not Yet Done}
For now we let these fall through to the atomic term case below.
\begin{code}
-- mkss trid p (Cls      n    tm)          = ssa "X n tm"
-- mkss trid p (Sub  typ      tm s)        = ssa "S typ tm s"
-- mkss trid p (Iter typ sa na si ni lvs)  = ssa "I typ sa na si ni lvs"
\end{code}

\subsection{Atomic Terms}
Remaining term cases are atomic, so become \h{SSA}:
\begin{code}
mkss trid p t = ssa (trterm trid p t) 
\end{code}

\subsection{Support Functions}

\begin{code}
ssBracketIf True  ss  =  sslist [ss_lpar,ss,ss_rpar]
ssBracketIf False ss  =  ss
\end{code}

\begin{code}
mkQuantifier trid p quant vl tm
  = ssc ssq ssnul ssbullet [ssvl,sst]
  where
    ssq = ssa $ trid quant 
    sst = mkss trid p tm 
    ssvl = ssopen "," $ map (ssa . trgvar trid) vl

ssbullet = ssa $ pad _bullet  
\end{code}

\newpage

\section{Perform Width-based Layout}

Given (terminal) width $W$ and and a sized string of size $s$,
if $s \leq W$ then we render as a one-liner,
otherwise we explore how to split over multiple lines.
\begin{code}
mklayout :: Int -> SS -> String
mklayout ww ss@(SS size ss')
  | size <= ww  =  ss'2str [] ss'
  | otherwise   =  unlines' $ splitlayout ww 0 ss
\end{code}

\subsection{Layout Splitting}

First a top-level function that ``peels out'' the \h{SS'} component:
\begin{code}
splitlayout :: Int -> Int -> SS  -> [String]
splitlayout ww i (SS size' ss') = splitlayout' ww size' i ss'
\end{code}

Most of the work is done by \h{splitlayout'}:
\begin{code}
splitlayout' :: Int -> Int -> Int -> SS' -> [String]
-- splitlayout' ww size i ss'  where size = sizeOf ss'
\end{code}

\subsection{Atomic Layout}

If the sized-string is atomic, we cannot split it:
\begin{code}
splitlayout' ww size i (SSA str) = [ind i str]
\end{code}

\subsection{Style Layout}
If we have a style, 
we recurse with it applied,
then prepend the showStyle and append the reset and setStyles stuff.
Note that all the style setting and resetting 
involves zero-width control character sequences.
\begin{code}
splitlayout' ww size i (SSS style ss)
  = let strs = splitlayout ww i ss
    in bracketStrings 
        (showStyle style) 
        strs 
        (resetStyle ++ setStyle [])
\end{code}

\subsection{General List Layout}

In general we have the form:
$$
ldelim~rdelim~sep~\seqof{itm_1,itm_2,\dots,itm_k}
$$
which should render as:
$$
ldelim~itm_1~sep~itm_2~sep \dots sep~itm_k~rdelim
$$
The $ldelim$, $rdelim$, and $sep$ can themselves be general sized-strings.
However they are usually simple strings, and can also be empty, 
or are often of length 1.
A key issue here is that each of the $itm_i$ may itself be a general list,
so what we are really dealing with is a tree-like structure.
\begin{code}
splitlayout' ww size i  ssc@( SSC ldelim@(SS lw ldelim')
                              rdelim@(SS rw rdelim') 
                              sep@(SS spw sep')
                              items )                           
  | i+size  <= ww  =  [ind i $ ss'2str [] ssc]
\end{code}


\subsubsection{Plan 2}

We fuse delimiters with first and last items, 
and separators with the preceding items.
Each fuse result after the first is rendered on a new line with an indent.

\begin{code}
  | otherwise  -- i+size > ww
    = concat $ concat (map (map (splitlayout rw (i+1))) fittings)
  where
    sslist = ldelim : intercalate [sep] (map singleton items) ++ [rdelim]
    rw = ww-i  -- "ribbon" width
    fittings = breakAt rw sslist
\end{code}

\subsection{Support Code}

\subsubsection{Breaking at Ribbon Width}

\begin{code}
breakAt :: Int -> [SS] -> [[SS]]
breakAt rw groups = brkAt rw 0 [] groups

brkAt :: Int -> Int -> [SS] -> [SS] -> [[SS]]
brkAt rw sofar sg [] = [reverse sg]
brkAt rw sofar sg gs@(g:gs')
  -- | gsize == 0  =  brkAt rw sofar sg gs'
  | gsize > rw  = flush rw sg g gs'
  | sofar + gsize <= rw  =  brkAt rw (sofar+gsize) (g:sg) gs'
  | otherwise            =  reverse sg : brkAt rw 0 [] gs
  where 
    gsize = sssize g 
    flush rw [] g gs' = [g] : brkAt rw 0 [] gs'
    flush rw sg g gs' = reverse sg : [g] : brkAt rw 0 [] gs'
\end{code}


\subsubsection{Style Bracketing}

This fuses prefix/postfix strings with first/last strings in a list.
This makes sense when the pre/postfix strings only contain zero-width characters.
\begin{code}
bracketStrings :: String -> [String] -> String -> [String]
bracketStrings pres [] posts = [pres,posts]
bracketStrings pres [str] posts = [pres++str,posts]
bracketStrings pres strs posts 
  = premrg pres $ reverse $ pstmrg posts $ reverse strs
  where premrg p (s:ss)  = ((p++s):ss) ; pstmrg p (s:ss) = ((s++p):ss)
\end{code}



\subsection{Pretty Term Tests}

The following tests are intended to be run from within GHCi.

\begin{code}
disp :: SS -> Int -> IO ()
disp thing w = putStrLn $ mklayout w thing
sssh = ssa . show
mullist :: Int -> SS
mullist n = ssc ss0 ss0 (ssa "*") $ take n $ map sssh [1..]

addltree :: Int -> SS
addltree n = mktree $ map sssh [1..n]

mkbranch :: SS -> SS -> SS
mkbranch ss1 ss2 = ssc ss0 ss0 (ssa "+") [ss1,ss2]

mktree :: [SS] -> SS
mktree [] = ss0 
mktree [ss] = ss
mktree [ss1,ss2] = mkbranch ss1 ss2 
mktree sss = mktree $ walk sss

walk :: [SS] -> [SS]
walk [] = []
walk [ss] = [ss]
walk [ss1,ss2] = [mkbranch ss1 ss2]
walk (ss1:ss2:sss) = mkbranch ss1 ss2 : walk sss
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
