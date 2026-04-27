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
import Variables
import Types
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
ppterm trid ww p t = unlines' $ mklayout ww $ mkss trid p t 
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
mkss _    _ (Val tk k)  =  ssa $ trValue k
mkss trid _ (Var tk v)  =  ssVar trid v
mkss trid _ (VTyp t v)  =  ssa ( "("++trvar trid v++":"++trType t++")" )
\end{code}


\subsection{Constructor Terms}

We have a lot of partial special cases, 
depending on the constructor name, and the number of sub-terms.
By partial we mean that we match against specific names and numbers,
but fall through if those matches fail, to try other cases.
We use \h{TestRendering} for symbol generation.


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
                  $ mksss trid opp ts
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
                        $ mksss trid opp ts
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
  | n == jId "r"    =  ssl ssnul (ssa "r":(map trRoot ts))
  where
    mkssts =  mksss trid 0 ts
    trRoot (Val _ (Integer i))  =  ssa $ show i
    trRoot (Val _ (Boolean b))  =  if b then ssa "!" else ssnul
    trRoot _                    =  ssnul
\end{code}

\subsubsection{Tailored Function Application}

We sometimes tailor standard functional application a little bit,
i.e., $X$ and $A$ in the UTCP theory.
$$ X(E|a|N|R) \qquad. A(in|a|out)$$
\begin{code}
mkss trid _ (Cons tk _ n ts)
  | n `elem` [jId "A", jId "X"]
  =  sslist [ ssa (trid n), ssc ss_lpar ss_rpar ss_bar mkssts]
  where mkssts = mksss trid 99 ts
\end{code}

\subsubsection{Function Application}

Any other constructor is rendered as a standard function call:
$$ f(t_1,\dots,t_n)$$
\begin{code}
mkss trid _ (Cons _ _ fn@(Identifier f _) ts)
  =  sslist [ ssa (trid fn), ssc ss_lpar ss_rpar ss_comma mkssts ]
  where mkssts = mksss trid 0 ts
\end{code}

\subsubsection{Quantifiers}

A quantifier has the general form:
$$ \mathcal Q v_1,\dots,v_n \bullet t$$
The difference between set-oriented binds ($\forall$,$\exists$,\dots)
and list-oriented binds ($\lambda$,\dots) is semantic,
but that is not relevant for pretty-printing.
\begin{code}
mkss trid p (Bnd  typ n vs tm) = mkQuantifier trid p n (S.toList vs) tm
mkss trid p (Lam  typ n vl tm) = mkQuantifier trid p n vl            tm
\end{code}

\subsubsection{Closure}

Closures are quantifier terms that cover all free variables:
$$[P] \qquad \langle Q \rangle$$
\begin{code}
mkss trid p (Cls (Identifier c _) tm)
  | c ==  "universal"        
    = ssw (ssa "[") (ssa "]") (mkss trid 99 tm)
  | c ==  "existential"        
    = ssw ss_lngl ss_rngl (mkss trid 99 tm)
\end{code}

\subsubsection{Substitution}

$$ t[e_1,\dots,e_n/v_1,\dots,v_n]$$
\begin{code}
mkss trid p (Sub tk (Var _ (Vbl (Identifier "asg" _) _ _)) 
                    (Substn tsub lvsub) )
  = ssa ( "(" ++ trvl trid (map StdVar tvs ++ map LstVar tlvs) 
              ++ " := " ++
              ( trtl trid 0 "," rts  `mrg` trvl trid (map LstVar rlvs)) 
              ++ ")" )
  where
   (tvs,rts) = unzip $ S.toList tsub
   (tlvs,rlvs)  =  unzip $ S.toList lvsub
   mrg ""  ""   =  ""
   mrg cs  ""   =  cs
   mrg ""  cs   =  cs
   mrg cs1 cs2  =  cs1 ++ ',':cs2

mkss trid p (Sub typ tm s)
  = sslist [mkss trid p tm,mkSubst trid 0 s]
\end{code}

\subsubsection{Iteration}

$$\ii \bigoplus C {lv_1,\dots,lv_n}$$
Here $n$ is the arity of constructor $C$.

For now we let these fall through to the catch-all case below.
\begin{code}
mkss trid p (Iter _ _ na@(Identifier astr _) _ ni@(Identifier istr _) lvs)
  =  sslist [ ssa (mkssiter na ni)
            , ssc ss_lpar ss_rpar ss_semi (map (mklv trid) lvs) ]
  where
    mkssiter na@(Identifier astr _) ni@(Identifier istr _)
      | astr == "and" && istr == "eq"
          =  "("++nicesym "and"++nicesym "eq"++")"
      | otherwise  =  trid na++"\x21bb"++trid ni
\end{code}

\subsubsection{Catch-All}
\begin{code}
mkss trid p t = ssa (trterm trid p t) 
\end{code}

\subsection{Support Functions}

\begin{code}
ssVar trid v = ssa $ trvar trid v

mklv trid lv = ssa $ trlvar trid lv
\end{code}

\begin{code}
ssBracketIf True  ss  =  sslist [ss_lpar,ss,ss_rpar]
ssBracketIf False ss  =  ss
\end{code}

$$t_1,\dots,t_n$$
\begin{code}
mksss :: (Identifier -> String) -> Int -> [Term] -> [SS]
mksss trid p ts = map (mkss trid p) ts
\end{code}

$$ \mathcal Q v_1,\dots,v_n \bullet t$$
The key thing here at top level is that we break the quantifier into the
following two components: 
$\mathcal Q v_1,\dots,v_n \bullet$ and $t$
(remember that $t$ can be very large, which is when prettyprinting matters).
\begin{code}
mkQuantifier trid p quant vl tm  =  sslist [sshdr,sst] 
  where
    ssq = ssa $ trid quant 
    ssvl = mkVarList trid vl
    sshdr = sslist [ssq,ssvl,ssbullet]
    sst = mkss trid p tm 
    
mkVarList trid vl = ssopen "," $ map (ssa . trgvar trid) vl

ssbullet = ssa $ pad _bullet 
\end{code}

$$[e_1,\dots,e_n/v_1,\dots,v_n]$$
\begin{code}
mkSubst trid p sub@(Substn vts lvlvs) 
  = ssclosed "[" "]" "/" [repls,targets]
  where
    (vs,ts) = unzip $ S.toList vts
    ss_vs = map (ssVar trid) vs
    ss_ts = mksss trid p ts
    (tlvs,rlvs) = unzip $ S.toList lvlvs
    ss_tlvs = map (ssLVar trid) tlvs
    ss_rlvs = map (ssLVar trid) rlvs
    targets = ssopen "," (ss_vs ++ ss_tlvs)
    repls   = ssopen "," (ss_ts ++ ss_rlvs)

ssLVar trid lv = ssa $ trlvar trid lv
\end{code}

\newpage

\section{Perform Width-based Layout}


Given (terminal) width $W$ and and a sized string of size $s$,
if $s \leq W$ then we render as a one-liner,
otherwise we explore how to split over multiple lines.
\begin{code}
mklayout :: Int -> SS -> [String]
mklayout ww ss
  | size <= ww  =  [ss2str [] ss]
  | otherwise   =  splitlayout ww 0 ss
  where size = sssize ss
\end{code}
We call \h{splitlayout} when \h{size > ww}.
It looks for a way to break down the rendering into multiple lines.
Those will themselves be further treated using a (mutually) recursive call
back to \h{mklayout}.
\begin{code}
splitlayout :: Int -> Int -> SS -> [String]
-- splitlayout ww i ss 
-- precondition: sssize ss + i > ww
\end{code}

\subsection{Simple Layout}

The \h{SSA} and \h{SSS} variants don't involve any layout determination.

\subsubsection{Atomic Layout}

If the sized-string is atomic, we cannot split it:
\begin{code}
-- precondition: size+i > ww
splitlayout _ i (SSA size str) = [ind i str]
\end{code}

\subsubsection{Style Layout}

If we have a style, 
we recursively layout the \h{SS} component,
and then prepend the showStyle and append the reset and setStyles stuff.
Note that all the style setting and resetting 
will (should!) involve zero-width control-character sequences.
\begin{code}
-- precondition: size+i > ww
splitlayout ww i (SSS size style ss)
  = wrapStyleControl 
      (showStyle style) 
      (splitlayout ww i ss) -- precondition still holds: size == sssize ss
      (resetStyle ++ setStyle [])
\end{code}

\subsection{Complex Layout}

Variants \h{SSW}, \h{SSL}, and \h{SSO} require splitting the output into lines.
This code is designed for the cases that the \h{sep}, \h{ldelim}, and \h{rdelim} components are themselves atomic and short.

\newpage
\subsubsection{Explicit Bracketing}

$$
ldelim~itm~rdelim
$$
In general $itm$ will be composite and multiline, 
best rendered with the delimeters fused at beginning and end.
\begin{verbatim}
(abc..
 ...lmn...
 ...zyz)  
\end{verbatim}
The first is forced if \h{sssize itm + i > ww},
otherwise we prefer the one with the largest delimiter by itself.
\begin{code}
-- precondition: size+i > ww
splitlayout ww i ssW@( SSW size ldelim rdelim itm )
  = map (ind i) $ wmerge ldelimstrs (wmerge itmstrs rdelimstrs)
  where
    rw = ww-i  -- "ribbon" width
    [lsize,rsize,isize] = map sssize [ldelim,rdelim,itm]
    ldelimstrs = mklayout rw ldelim
    rdelimstrs = mklayout rw rdelim
    itmstrs    = mklayout (rw-(lsize+rsize)) itm
    wmerge = strsmerge ""
\end{code}

\subsubsection{General List Layout}

$$
itm_1~sep~itm_2~sep \dots sep~itm_k
$$
Here we treat this as a list and layout accordingly.
\begin{verbatim}
a,..,i
,j,..,r
,s,..,z
\end{verbatim}
\begin{code}
-- precondition: size+i > ww
splitlayout ww i ssL@( SSL size sep items )
  = map (ind  i) $ listpartition rw sepsize sepstr sizeditems
  where
    rw = ww-i  -- "ribbon" width
    sepsize = sssize sep
    sepstr = mklayout rw sep
    itemsizes  = map sssize items
    itemstrs   = map (mklayout rw) items
    sizeditems = zip itemsizes itemstrs
\end{code}

\newpage
\subsubsection{General Infix Operator Layout}

$$
itm_1~inop~itm_2~inop \dots sep~itm_k
$$
Here we treat this as a tree and layout accordingly.
\begin{verbatim}
x+x+x+x+x+x+x+x  x+x+x+x    x+x
                 +x+x+x+x   +x+x
                            +x+x
                            +x+x                           
\end{verbatim}
\begin{code}
-- precondition: size+i > ww
splitlayout ww i ssO@( SSO size op items )
  = map (ind i) $ treepartition rw opsize opstr sizeditems
  where
    rw = ww-i  -- "ribbon" width
    opsize = sssize op
    opstr = mklayout rw op
    itemsizes  = map sssize items
    itemstrs   = map (mklayout rw) items
    sizeditems = zip itemsizes itemstrs
\end{code}

\subsection{Support Code}

\subsubsection{Prefix and Postfix}

Prefix fuses the last string of the 1st argument 
with the first string of the 2nd, with a separating space
\begin{code}
strsmerge :: String -> [String] -> [String] -> [String]
strsmerge _ [] strs2 = strs2
strsmerge _ strs1@[str1] [] = strs1
strsmerge glue [str1] (str2:strs2) = (str1++glue++str2):strs2
strsmerge glue (str1:strs1) strs2 = str1 : strsmerge glue strs1 strs2
\end{code}

\subsubsection{Separated List Partitioning}

\begin{verbatim}
a,..,i
,j,..,r
,s,..,z
\end{verbatim}
\begin{code}
listpartition :: Int -> Int -> [String] -> [(Int,[String])] -> [String]
listpartition _  _       _       []  =  []
listpartition ww sepsize sepstrs ((w,strs):ssstrs)
  =  lstpart w strs ssstrs
  where
    -- lstpart: expecting an item
    lstpart :: Int -> [String] -> [(Int,[String])] -> [String]
    lstpart currsize lines []    =  lines
    lstpart currsize lines ((w,strs):ssstrs)
      | currsize+nextsize <= ww  
         =  lstpart (currsize+nextsize) 
                    (lmerge lines $ lmerge sepstrs strs) 
                    ssstrs
      | otherwise  
         =  lstpart nextsize
                    (lines ++ lmerge sepstrs strs) 
                    ssstrs
      where
        nextsize = sepsize+w
        lmerge = strsmerge ""  
\end{code}

\subsubsection{Tree Partitioning}

\begin{verbatim}
x+x+x+x+x+x+x+x  x+x+x+x    x+x
                 +x+x+x+x   +x+x
                            +x+x
                            +x+x                           
\end{verbatim}
We repeatedly halve the lists until each fits the available space,
and then render them directly.
\begin{code}
treepartition :: Int -> Int -> [String] -> [(Int,[String])] -> [String]
treepartition _ _ _ []          =  []
treepartition _ _ _ [(_,strs)]  =  strs
-- precondition: treesize opsize sizedstrs  > ww  && length sizedstrs >= 2
treepartition ww opsize opstrs sizedstrs
  = if emptyfirst
    then if emptysecond
         then []
         else second
    else if emptysecond
         then first
         else    map (ind indent) first 
              ++ map (ind indent) (tmerge opstrs second)
  where
    (got,leftover) = halve opsize sizedstrs
    indent = 1
    first   =  treerender (ww-indent) opsize opstrs got
    second  =  treerender (ww-indent) opsize opstrs leftover
    emptyfirst   =  emptystrs first
    emptysecond  =  emptystrs second
    tmerge = strsmerge ""

emptystrs :: [String] -> Bool
emptystrs  =  all (all isSpace) 
\end{code}

\begin{code}
treerender :: Int -> Int -> [String] -> [(Int,[String])] -> [String]
treerender ww opsize opstrs sizedstrs
  | size <= ww  
               =  [ ss2str [] (sso (ssa (concat opstrs)) 
                    $ map (ssa . concat . snd) sizedstrs) ]
  | otherwise  =  treepartition ww opsize opstrs sizedstrs
  where
    size = treesize opsize sizedstrs
\end{code}

Halving:
\begin{code}
-- precondition: length sizedstrs >= 2
-- split into two roughly equal size parts
-- postcondition: not null got && not null leftover
halve :: Int -> [(Int,[String])] -> ( [(Int,[String])], [(Int,[String])] )
halve opsize [first,last] = ( [first], [last] )
halve opsize sizedstrs@(first@(fsize,_):others)
  = ( got , leftover )
  where 
    size = treesize opsize sizedstrs
    (got,leftover) 
      = takeUpto opsize (size `div` 2) (opsize+fsize) [first] others

treesize :: Int -> [(Int,[String])] -> Int
treesize _ [] = 0
treesize _ [(size,_)] = size
treesize opsize sizedstrs 
  = (length sizedstrs - 1) * opsize + sum (map fst sizedstrs)

takeUpto :: Int -> Int -> Int -> [(Int,[String])] -> [(Int,[String])] 
         -> ([(Int,[String])],[(Int,[String])])
takeUpto opsize wanted len tog [] = (reverse tog,[]) -- shouldn't come here
takeUpto opsize wanted len tog end@[_] = (reverse tog,end)
takeUpto opsize wanted len tog szs@(sstr@(size,_):sizedstrs)
  | wanted >= newsize  =  takeUpto opsize wanted newsize (sstr:tog) sizedstrs
  | otherwise         =  (reverse tog,szs)
  where
    newsize = len+opsize+size
\end{code}



\subsubsection{Breaking at Ribbon Width}

\begin{code}
breakAt :: Int -> [SS] -> [[SS]]
breakAt rw groups = brkAt rw 0 [] groups

brkAt :: Int -> Int -> [SS] -> [SS] -> [[SS]]
brkAt rw sofar sg [] = [wraprev sg]
brkAt rw sofar sg gs@(g:gs')
  | gsize == 0  =  brkAt rw sofar sg gs'
  | gsize > rw  = flush rw sg g gs'
  | sofar + gsize <= rw  =  brkAt rw (sofar+gsize) (g:sg) gs'
  | otherwise            =  wraprev sg : brkAt rw 0 [] gs
  where 
    gsize = sssize g 
    flush rw [] g gs' = [g] : brkAt rw 0 [] gs'
    flush rw sg g gs' = wraprev sg : [g] : brkAt rw 0 [] gs'

wraprev sg = reverse sg-- [sslist $ reverse sg]

renderFittings :: [[SS]] -> [String]
renderFittings ssss 
  = let strss = map (map (splitlayout 1000 0)) ssss
    in [unlines' $ map concat (map concat strss)]
\end{code}


\subsubsection{Style Control}

This fuses prefix/postfix strings with first/last strings in a list.
This makes sense when the pre/postfix strings only contain zero-width characters.
\begin{code}
wrapStyleControl :: String -> [String] -> String -> [String]
wrapStyleControl pres [] posts = [pres,posts]
wrapStyleControl pres [str] posts = [pres++str,posts]
wrapStyleControl pres strs posts 
  = premrg pres $ reverse $ pstmrg posts $ reverse strs
  where premrg p (s:ss)  = ((p++s):ss) ; pstmrg p (s:ss) = ((s++p):ss)
\end{code}



\subsection{Pretty Term Tests}

The following tests are intended to be run from within GHCi.

\begin{code}
ssdisp :: SS -> Int -> IO ()
ssdisp thing w 
  = putStrLn (replicate w '_' ++ "\n" ++ (unlines' $ mklayout w thing))

sssh = ssa . show
mullist :: Int -> SS
mullist n = ssl (ssa ",") $ take n $ map sssh [1..]

addltree :: Int -> SS
addltree n = mktree $ map sssh [1..n]

mkbranch :: SS -> SS -> SS
mkbranch ss1 ss2 = sso (ssa " + ") [ss1,ss2]

mktree :: [SS] -> SS
mktree [] = ssnul 
mktree [ss] = ss
mktree [ss1,ss2] = mkbranch ss1 ss2 
mktree sss = mktree $ walk sss

walk :: [SS] -> [SS]
walk [] = []
walk [ss] = [ss]
walk [ss1,ss2] = [mkbranch ss1 ss2]
walk (ss1:ss2:sss) = mkbranch ss1 ss2 : walk sss

mkstree :: [String] -> (Int,[(Int,[String])])
mkstree strs = (total,nstrs)
  where
    lw s = (length s,[s])
    nstrs = map lw strs
    total = sum $ map fst nstrs

gmu = ["Good","morning","Universe","!","How","are","you","today","?"]
ssgmu = map ssa gmu
ssogmu = (sso (ssa ".")) ssgmu
sswgmu = ssw (ssa "(") (ssa ")") (ssl (ssa ",") ssgmu)

mksub tvcount lvlvcount
  = jSubstn tvl lvlvl
  where
    tvl = map mktv [1..tvcount]
    lvlvl = map mkvlvl [1..lvlvcount]
    mktv n = (StaticVar $ mkvid n,Val ArbType $ Integer n)
    mkvlvl n = (StaticVars $ mklvid "t" n,StaticVars $ mklvid "r" n)

mkvid n = jId ("x"++show n)
mklvid s n = jId (s++show n)

mkVT v = jpVar $ StaticVar $ jId v

mksubst tvc lvc = Sub ArbType  (mkVT "t") $ mksub tvc lvc

tdisp t ww 
 = putStrLn (replicate ww '_' ++ "\n" ++ ppTerm ww 0 t)
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
