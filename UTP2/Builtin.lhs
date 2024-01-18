\section{Builtin Information}

\begin{code}
module Builtin where
import Utilities
import Tables
import Datatypes
import DSL
import Types
import DataText
--import Heuristics
--import Manipulation
import Proof
import Theories
import RootTheory

import Text.ParserCombinators.Parsec.Expr
\end{code}

This module exports a number of built-in theories:
\begin{description}
  \item[Equality]
    Covers equality, and inequality
  \item[Arithmetic]
    Covers numbers (integer)
  \item[Sets]
    Basic Set Theory
  \item[Lists]
    Basic List Theory
\end{description}

\subsection{Conditioning Laws}

Laws without side-conditions are easily conditioned:
\begin{code}
simpleAssertions :: [(String,Pred)] -> [(String,Assertion)]
simpleAssertions = mapsnd (conditionAsn [] . mkAsnSCtrue)

simpleLaws :: String -> [(String,Pred)] -> [(String,Law)]
simpleLaws pname = map (addBuiltInProv pname) . simpleAssertions

addBuiltInProv :: String -> (String,Assertion) -> (String,Law)
addBuiltInProv pname = wrapProv (FromSOURCE ("Builtin:"++pname))
\end{code}



\subsection{Theory: Equality}

Equality is an equivalence relation,
and all variables are considered as being well-defined.
\begin{code}
typesEquality
 = lbuild
     [ ("=", Tfun (Tprod [t,t]) B)
     , ("/=",Tfun (Tprod [t,t]) B)
     ]

lawsEquality
  = [ ("=-refl",  e1 `equal` e1)
    , ("=-symm",  e1 `equal` e2 === e2 `equal` e1)
    , ("=-trans", (e1 `equal` e2) /\ (e2 `equal` e3) ==> (e1 `equal` e3))
    , ("DEF-ne",  (e1 `neq` e2) === (Not (e1 `equal` e2)))
    , ("/=-symm", (e1 `neq` e2) ===(e2 `neq` e1))
    ]
\end{code}

\subsubsection{And the Result is \ldots}

\begin{code}

equalityName = "Equality"

theoryEquality
  = (nmdNullPrfCtxt equalityName)
    { syntaxDeps = [ rootName ]
    , precs = precsEquality
    , types = typesEquality
    , laws  = simpleLaws equalityName lawsEquality
    }

\end{code}


\newpage
\subsection{Theory: Arithmetic}

First, the basic four arithmetic operations:
\begin{code}


typesArithmetic1
 = [("neg",Tfun Z Z)
   ,("+",tArithBinOp)
   ,("-",tArithBinOp)
   ,("*",tArithBinOp)
   ,("/",tArithBinOp)
   ,("div",tArithBinOp)
   ,("mod",tArithBinOp)
   ]

lawsArithmetic1
 = [("plus-l-unit",(zero `plus` e1) `equalZ` e1)
   ,("plus-r-unit",(e1 `plus` zero) `equalZ` e1)
   ,("plus-comm",(e1 `plus` e2) `equalZ` (e2 `plus` e1))
   ,("plus-assoc",(e1 `plus` (e2 `plus` e3)) `equalZ` ((e1 `plus` e2) `plus` e3))
   ,("plus-inv",(e1 `plus` (neg e1)) `equalZ` zero)
   ,("plus-cancel",(e1 `equalZ` e2)===((e3 `plus` e1) `equalZ` (e3 `plus` e2)))
   ,("minus-as-plus-neg",(e1 `minus` e2) `equalZ` (e1 `plus` (neg e2)))
   ,("minus-l-unit",(e1 `minus` zero) `equalZ` e1)
   ,("mul-l-unit",(one `mul` e1) `equalZ` e1)
   ,("mul-r-unit",(e1 `mul` one) `equalZ` e1)
   ,("mul-l-zero",(zero `mul` e1) `equalZ` zero)
   ,("mul-r-zero",(e1 `mul` zero) `equalZ` zero)
   ,("mul-comm",(e1 `mul` e2) `equalZ` (e2 `mul` e1))
   ,("mul-assoc",(e1 `mul` (e2 `mul` e3)) `equalZ` ((e1 `mul` e2) `mul` e3))
   ,("divd-l-unit",(e1 `divd` one) `equalZ` e1)
   ]

dodArithmetic1
 = [ domOfDefn "/"  (e1 `divd` e2)  (e2 `neq` zero)
   ]

\end{code}

\subsubsection{Arithmetic Relations}

Now, relations on numbers:
\begin{code}

typesArithmetic2
 = [("=",Tfun (Tprod [t,t]) B)
   ,("/=",Tfun (Tprod [t,t]) B)
   ,("<",tArithRel)
   ,("<=",tArithRel)
   ,(">",tArithRel)
   ,(">=",tArithRel)
   ]

lawsArithmetic2
  = [("lt-irr",Not (e1 `lthan` e1))
    ,("lt-trans",Imp (And [e1 `lthan` e2,e2 `lthan` e3]) (e1 `lthan` e3))
    ,("lt-disj",Not (And [e1 `lthan` e2,e2 `lthan` e1]))
    ,("le-refl",e1 `leq` e1)
    ,("le-trans",Imp (And [e1 `leq` e2,e2 `leq` e3]) (e1 `leq` e3))
    ,("le-lt-trans", (e1 `leq` e2) /\ (e2 `lthan` e3) ==> e1 `leq` e3 )
    ,("lt-le-trans", (e1 `lthan` e2) /\ (e2 `leq` e3) ==> e1 `leq` e3 )
    ,("le-anti",Imp (And [e1 `leq` e2,e2 `leq` e1]) (e1 `equalZ` e2))

    ,("gt-irr",Not (e1 `gthan` e1))
    ,("gt-trans",Imp (And [e1 `gthan` e2,e2 `gthan` e3]) (e1 `gthan` e3))
    ,("gt-disj",Not (And [e1 `gthan` e2,e2 `gthan` e1]))
    ,("ge-refl",e1 `geq` e1)
    ,("ge-trans",Imp (And [e1 `geq` e2,e2 `geq` e3]) (e1 `geq` e3))
    ,("ge-gt-trans", (e1 `geq` e2) /\ (e2 `gthan` e3) ==> e1 `geq` e3 )
    ,("gt-ge-trans", (e1 `gthan` e2) /\ (e2 `geq` e3) ==> e1 `geq` e3 )
    ,("ge-anti",Imp (And [e1 `geq` e2,e2 `geq` e1]) (e1 `equalZ` e2))

    ,("swap-le-ge",(e1 `leq` e2) === (e2 `geq` e1))
    ,("swap-lt-gt",(e1 `lthan` e2) === (e2 `gthan` e1))

    ,("le-as-lt",(e1 `leq` e2)   === (e1 `lthan` e2) \/ (e1 `equal` e2))
    ,("lt-as-le",(e1 `lthan` e2) === (e1 `leq` e2) /\ (e1 `neq` e2))

    ,("ge-as-gt",(e1 `geq` e2)   === (e1 `gthan` e2) \/ (e1 `equal` e2))
    ,("gt-as-ge",(e1 `gthan` e2) === (e1 `geq` e2) /\ (e1 `neq` e2))

    ,("plus-one-lt",e1 `lthan` (e1 `plus` one))
    ,("plus-one-gt",(e1 `plus` one) `gthan` e1)
    ,("plus-pos-ge",(e2 `geq` zero) ==> (e1 `plus` e2) `geq` e1)
    ,("plus-neg-le",(e2 `leq` zero) ==> (e1 `plus` e2) `leq` e1)
    ,("plus-pos-gt",(e2 `gthan` zero) ==> (e1 `plus` e2) `gthan` e1)
    ,("plus-neg-lt",(e2 `lthan` zero) ==> (e1 `plus` e2) `lthan` e1)

    ,("minus-one-gt",e1 `gthan` (e1 `minus` one))
    ,("minus-one-lt",(e1 `minus` one) `lthan` e1)
    ,("minus-pos-le",(e2 `geq` zero) ==> (e1 `minus` e2) `leq` e1)
    ,("minus-neg-ge",(e2 `leq` zero) ==> (e1 `minus` e2) `geq` e1)
    ,("minus-pos-lt",(e2 `gthan` zero) ==> (e1 `minus` e2) `lthan` e1)
    ,("minus-neg-ge",(e2 `lthan` zero) ==> (e1 `minus` e2) `gthan` e1)
    ]

dodArithmetic2
 = [ ]

\end{code}

\subsubsection{Arithmetic Induction}

\begin{code}
lawsArithmetic3
  = let
      x = preVar "x" ; vx = Var x; qx = Q[x]
      n = preVar "n"; vn = Var n; qn = Q[n]

      natIndBase  = Sub pP (indSub (Num 0) x)
      natIndHyp   = Sub pP (indSub vn x)
      natIndNext  = Sub pP (indSub (vn `plus` one) x)

      natIndStep  = mkAll qn (natIndHyp ==> natIndNext)

      forallNat = Forall 0 qx ((zero `leq` vx) ==> pP)

      intIndPrev  = Sub pP (indSub (vn `minus` one) x)
      intIndStep  = mkAll qn (natIndHyp ==> intIndPrev)

      forallInt = Forall 0 qx pP
    in
      [ ( "induction-Nat"
        , natIndBase /\ natIndStep ==> forallNat
        )
      , ( "induction-Int"
        , natIndBase /\ natIndStep /\ intIndStep ==> forallInt
        )
      ]
\end{code}


\subsubsection{And the Result is \ldots}

\begin{code}

arithmeticName = "Arithmetic"

theoryArithmetic
  = (nmdNullPrfCtxt arithmeticName)
     { syntaxDeps = [ rootName, equalityName ]
     , precs = lbuild (precsArithmetic1++precsArithmetic2)
     , types = lbuild (typesArithmetic1++typesArithmetic2)
     , laws =  simpleLaws arithmeticName
                    (  lawsArithmetic3
                    ++ lawsArithmetic1 ++ dodArithmetic1
                    ++ lawsArithmetic2 ++ dodArithmetic2 )
     }

\end{code}


\newpage
\subsection{Theory: Set}

\begin{code}

typesSet
 = lbuild
     [("in",Tfun tMmbr B)
     ,("subset",tSetRel)
     ,("subseteq",tSetRel)
     ,("union",tSetBinOp)
     ,("intsct",tSetBinOp)
     ,("\\",tSetBinOp)
     ,("card",Tfun tSet Z)
     ]

lawsSet -- need these !
 = [ ("~-in-{}",Not (e1 `pmof` empty))
   , ("in-singleton",(e1 `pmof` Set [e2])===(e1 `equal` e2))
   , ("in-union",(e1 `pmof` (s1 `unn` s2))===(e1 `pmof` s1) \/ (e1 `pmof` s2))
   , ("in-intersect",(e1 `pmof` (s1 `intsct` s2))===(e1 `pmof` s1) /\ (e1 `pmof` s2))
   , ("in-setdiff",(e1 `pmof` (s1 `sdiff` s2))===(e1 `pmof` s1) /\ Not (e1 `pmof` s2))
   , ("set-extensionality",((s1 `equalS` s2))===mkAll qx ((Var vx `pmof` s1)===(Var vx `pmof` s2)))
   , ("DEF-subseteq",((s1 `psubseteq` s2)===(mkAll qx ((Var vx `pmof` s1)==>(Var vx `pmof` s2)))))
   , ("DEF-subset",((s1 `psubset` s2)===(s1 `psubseteq` s2)/\ Not (s1 `equalS` s2)))
   , ("DEF-card-empty",card empty `equalZ` zero)
   , ("DEF-card-single",card (Set [e1]) `equalZ` one)
   , ("DEF-card-union",( card (e1 `unn` e2) )
                       `equalZ`
                       ( ( card e1 `plus` card e2)  `minus` card ( e1 `intsct` e2) )
     )
   ]

conjsSet
 = [ ("in-self", e1 `pmof` Set [e1])
   , ("union-idem", e1 `unn` e1 `equalS` e1 )
   , ("union-comm", (e1 `unn` e2) `equalS` (e2 `unn` e1) )
   , ("union-assoc", e1 `unn` (e2 `unn` e3) `equalS` ( e1 `unn` e2 ) `unn` e3 )
   , ("intsct-idem", e1 `intsct` e1 `equalS` e1 )
   , ("intsct-comm", e1 `intsct` e2 `equalS` e2 `intsct` e1 )
   , ("intsct-assoc", e1 `intsct` (e2 `intsct` e3) `equalS` ( e1 `intsct` e2 ) `intsct` e3 )
   , ( "union-int-distr"
     , (( e1 `unn` e2 ) `intsct` e3 )
       `equalS`
       ( (e1 `intsct` e3) `unn` (e2 `intsct` e3))
     )
   , ( "int-union-distr"
     , (( e1 `intsct` e2 ) `unn` e3 )
       `equalS`
       ( (e1 `unn` e3) `intsct` (e2 `unn` e3))
     )
   , ("sdiff-self", e1 `sdiff` e1 `equalS` empty )
   , ("union-sdiff-distr"
     ,  (e1 `unn` e2) `sdiff` e3 `equalS` (e1 `sdiff` e3) `unn` (e2 `sdiff` e3)
     )
   , ("int-sdiff-distr"
     ,  (e1 `intsct` e2) `sdiff` e3 `equalS` (e1 `sdiff` e3) `intsct` (e2 `sdiff` e3)
     )
   , ("sdiff-union-distr"
     ,  e1 `sdiff`(e2 `unn` e3) `equalS` (e1 `sdiff` e2) `intsct` (e1 `sdiff` e3)
     )
   , ("sdiff-int-distr"
     ,  e1 `sdiff`(e2 `intsct` e3) `equalS` (e1 `sdiff` e2) `unn` (e1 `sdiff` e3)
     )
   , ("sdiff-twice"
     ,  (e1 `sdiff` e2) `sdiff` e3  `equalS` e1 `sdiff`(e2 `unn` e3)
     )
   ]

dodSet = [  ]


\end{code}

\subsubsection{And the Result is \ldots}

\begin{code}

setsName = "Sets"

theorySets
  = (nmdNullPrfCtxt setsName)
    { syntaxDeps = [ rootName, equalityName, arithmeticName ]
    , precs = lbuild precsSet
    , types = typesSet
    , conjectures = lbuild $ simpleAssertions $ conjsSet
    , laws = simpleLaws setsName (lawsSet ++ dodSet)
    }

\end{code}

\newpage
\subsection{Theory: Lists}

For now, we avoid ``dependent'' types like $T^+$.

\begin{code}

typesList
 = lbuild
     [(":",Tfun (Tprod [t,tSeq]) tSeq)
     ,("null",Tfun tSeq B)
     ,("hd",Tfun tSeq t)
     ,("tl",Tfun tSeq tSeq)
     ,("frnt",Tfun tSeq tSeq)
     ,("lst",Tfun tSeq t)
     ,("len",Tfun tSeq Z)
     ,("++",tSeqBinOp)
     ,("<<",tSeqBinRel)
     ,("<<=",tSeqBinRel)
     ,("--",tSeqBinOp)
     ,("ix",Tfun (Tprod [tSeq,Z]) t)
     ,("elems",Tfun tSeq tSet)
     ]

( lawListInd
 , lawNonnullListInd )
 = let
     (ell,vell,qell,eell) = declPreNVQE "ell"
     (x,vx,qx,ex)         = declPreNVQE "x"
     (xs,vxs,qxs,exs)     = declPreNVQE "xs"

     listIndBase = Sub pP (indSub nil vell)
     listIndHyp  = Sub pP (indSub exs vell)
     listIndNext = Sub pP (indSub (ex `cons` exs) vell)

     listIndStep = mkAll (Q [vx,vxs]) (listIndHyp ==> listIndNext)

     forAllList = mkAll qell pP

     listIndSngl = Sub pP (indSub (sngll ex) vell)

     forAllNonNil = Forall 0 qell ((TypeOf eell tSeqp) ==> pP)
   in
    ( ( "induction-List", listIndBase /\ listIndStep ==> forAllList )
    , ( "induction-Non-Nil", listIndSngl /\ listIndStep ==> forAllNonNil )
    )

lawsList
 = let
     (x,vx,qx,ex)         = declPreNVQE "x"
     (xs,vxs,qxs,exs)     = declPreNVQE "xs"
     (y,vy,qy,ey)         = declPreNVQE "y"
     (ys,vys,qys,eys)     = declPreNVQE "ys"
 in [( "nil-is-List", TypeOf nil tSeq )
    ,( "cons-is-List"
     , (TypeOf ex t) /\ (TypeOf exs tSeq)
        ==> (TypeOf (ex `cons` exs) tSeq) )
    ,( "nil-not-cons", Not (nil `equalL` (ex `cons` exs)) )
    ,( "cons-injective"
     , (ex `equal` ey) /\ (exs `equalL` eys)
        === ((ex `cons` exs) `equalL` (ey `cons` eys)) )
    ,lawListInd

    ,( "DEF-non-nil", (Not (exs `equalL` nil)) === (TypeOf exs tSeqp) )
    ,( "DEF-null", plnull exs === exs `equalL` nil )
    ,( "DEF-singleton-list", (sngll ex) `equalL` (ex `cons` nil) )

    ,( "DEF-hd", (hd (ex `cons` exs) `equal` ex) )
    ,( "DEF-tl", (tl (ex `cons` exs) `equalL` exs) )
    ,( "DEF-cat-nil", (nil `cat` l2) `equalL` l2 )
    ,( "DEF-cat-cons", ((ex `cons` l1) `cat` l2) `equalL` (ex `cons` (l1 `cat` l2)))
    ,( "DEF-len-nil", len nil `equalZ` zero )
    ,( "DEF-len-cons", len (ex `cons` exs) `equalZ` (one `plus` len exs) )
    ,( "DEF-index-one", ix (ex `cons` exs) one `equal` ex )
    ,( "DEF-index-n",   ix (ex `cons` exs) (nn `plus` one) `equal` ix exs nn )
    ,( "DEF-pfx-nil",  nil `ppfx` exs )
    ,( "DEF-pfx-cons", ((ex `cons` exs) `ppfx` (ey `cons` eys))
                       ===
                       (ex `equal` ey) /\ (exs `ppfx` eys) )
    ,( "DEF-not-pfx",  (ex `cons` exs) `ppfx` nil === FALSE )
    ,( "DEF-spfx-nil",  nil `pspfx` (ex `cons` exs) )
    ,( "DEF-spfx-cons", ((ex `cons` exs) `pspfx` (ey `cons` eys))
                       ===
                       (ex `equal` ey) /\ (exs `pspfx` eys) )
    ,( "DEF-not-spfx",  exs `pspfx` nil === FALSE )
    ,( "DEF-ssub-nil", (exs `ssub` nil) `equalL` exs )
    ,( "DEF-ssub-cons",  ((ex `cons` exs) `ssub` (ex `cons` eys))
                         `equalL` (exs `ssub` eys) )
    ,( "DEF-frnt-sngl",  frnt (sngll ex) `equalL` nil )
    ,( "DEF-frnt-cons2",  frnt (ex `cons` ey `cons` eys) `equalL` (ex `cons` (frnt (ey `cons` eys)) ) )
    ,( "DEF-last-sngl",  lst (sngll ex) `equal` ex )
    ,( "DEF-last-cons2",  lst (ex `cons` ey `cons` eys) `equal` (lst (ey `cons` eys)) )

    ,( "DEF-elems-nil", elems nil `equalS` empty )
    ,( "DEF-elems-cons", elems (ex `cons` exs) `equalS` (Set [ex]) `unn` elems exs )

    ]

dodList
  = let
      vxs = Var $ preVar "xs"
      vys = Var $ preVar "ys"
    in [ domOfDefn "--"  (vxs `ssub` vys)  (vys `ppfx` vxs)
       , domOfDefn "hd" vxs (Not (plnull vxs))
       , domOfDefn "tl" vxs (Not (plnull vxs))
       , domOfDefn "frnt" vxs (Not (plnull vxs))
       , domOfDefn "lst" vxs (Not (plnull vxs))
       ]

forAllNonNil' = Forall 0 qell ((Not (vell `equalL` nil)) ==> pP)

conjsList
 = let
     (x,vx,qx,ex)         = declPreNVQE "x"
     (xs,vxs,qxs,exs)     = declPreNVQE "xs"
 in [ ( "nil-is-null", plnull nil )
    , ( "cons-not-null", Not (plnull (ex `cons` exs)) )
    , ( "sngl-not-nil", sngll ex `neqL` nil )
    ,( "len-sngl", len (sngll ex) `equalZ` one )
    -- ,( "index-sngl", ix (sngll ex) one  `equal` ex )

    -- ,lawNonnullListInd

    -- ,( "non-nil-is-List", (TypeOf exs tSeqp) ==> (TypeOf exs tSeq) )
    -- ,( "non-nil-hd-tl"
    -- , (TypeOf exs tSeqp) ==> (exs `equalL` ((hd exs) `cons` (tl exs))))
    -- ,( "cons-not-nil"
    -- , (exs `equalL` ((hd exs) `cons` (tl exs))) === (exs `neqL` nil))

    -- ,( "cat-assoc", (l1 `cat` (l2 `cat` l3)) `equalL` ((l1 `cat` l2) `cat` l3)  )
    ,( "len-cat-morphism",  (len (l1 `cat` l2)) `equalZ` ((len l1) `plus` (len l2)) )
    -- ,("seq-imp-pfx.1",(l1 `equalL` l2) ==> l1 `ppfx` l2)
    -- ,("seq-imp-pfx.2",(l1 `equalL` l2) ==> l2 `ppfx` l1)
    -- ,("spfx-trans",Imp (And [l1 `pspfx` l2,l2 `pspfx` e3]) (l1 `pspfx` e3))
    -- ,("spfx-disj",Not (And [l1 `pspfx` l2,l2 `pspfx` l1]))
    -- ,("spfx-=>-pfx", (exs `pspfx` vys) ==> (exs `ppfx` vys) )
    ,("ssub-inv-cat",(l1 `cat` l2) `ssub` l1  `equalL` l2)
    --  ,("cat-inv-ssub",(l1 `ppfx` l2) ==> (l1 `cat` (l2 `ssub` l1)  `equalL` l2))
    --,( "last-snoc",  lst (exs `cat` (sngll ex)) `equal` ex )
    --,( "last-alt-def", lst exs `equal` hd (exs `ssub` frnt exs) )

    ,( "cat-nil-r-unit", (l1 `cat` nil) `equalL` l1 )

    --,( "index-one-hd",  (exs `neqL` nil) ==> ( ix exs one `equal` hd exs ) )

    ,("pfx-refl",l1 `ppfx` l1)
    -- ,("pfx-trans",Imp (And [l1 `ppfx` l2,l2 `ppfx` l3]) (l1 `ppfx` l3))
    -- ,("pfx-anti",Imp (And [l1 `ppfx` l2,l2 `ppfx` l1]) (l1 `equalL` l2))
    ,("pfx-cat",(l1 `ppfx` (l1 `cat` l2)))

    -- ,( "frnt-snoc",  frnt (exs `cat` (sngll ex)) `equalL` exs )

    -- ,( "frnt-len",  (exs `neq` nil)
    --                 ==>
    --                (len exs `equalZ` (len (frnt exs) `plus` one))  )

    ]

conjsAsLawsList
 = let
     (x,vx,qx,ex)         = declPreNVQE "x"
     (xs,vxs,qxs,exs)     = declPreNVQE "xs"
     (y,vy,qy,ey)         = declPreNVQE "y"
     (ys,vys,qys,eys)     = declPreNVQE "ys"
 in [ ( "index-sngl", ix (sngll ex) one  `equal` ex )

    ,lawNonnullListInd

    ,( "non-nil-is-List", (TypeOf exs tSeqp) ==> (TypeOf exs tSeq) )
    ,( "non-nil-hd-tl"
    , (TypeOf exs tSeqp) ==> (exs `equalL` ((hd exs) `cons` (tl exs))))
    ,( "cons-not-nil"
    , (exs `equalL` ((hd exs) `cons` (tl exs))) === (exs `neqL` nil))

    ,( "cat-assoc", (l1 `cat` (l2 `cat` l3)) `equalL` ((l1 `cat` l2) `cat` l3)  )
    ,("seq-imp-pfx.1",(l1 `equalL` l2) ==> l1 `ppfx` l2)
    ,("seq-imp-pfx.2",(l1 `equalL` l2) ==> l2 `ppfx` l1)
    ,("spfx-trans",Imp (And [l1 `pspfx` l2,l2 `pspfx` e3]) (l1 `pspfx` e3))
    ,("spfx-disj",Not (And [l1 `pspfx` l2,l2 `pspfx` l1]))
    ,("spfx-=>-pfx", (exs `pspfx` eys) ==> (exs `ppfx` eys) )
    ,("cat-inv-ssub",(l1 `ppfx` l2) ==> (l1 `cat` (l2 `ssub` l1)  `equalL` l2))
    ,( "last-snoc",  lst (exs `cat` (sngll ex)) `equal` ex )
    ,( "last-alt-def", lst exs `equal` hd (exs `ssub` frnt exs) )
    ,( "index-one-hd",  (exs `neqL` nil) ==> ( ix exs one `equal` hd exs ) )
    ,("pfx-trans",Imp (And [l1 `ppfx` l2,l2 `ppfx` l3]) (l1 `ppfx` l3))
    ,("pfx-anti",Imp (And [l1 `ppfx` l2,l2 `ppfx` l1]) (l1 `equalL` l2))
    ,( "frnt-snoc",  frnt (exs `cat` (sngll ex)) `equalL` exs )
    ,( "frnt-len",  (exs `neq` nil)
                    ==>
                   (len exs `equalZ` (len (frnt exs) `plus` one))  )

    ]


slottedCircusListConj
 = let
     (x,vx,qx,ex)         = declPreNVQE "x"
     (y,vy,qy,ey)         = declPreNVQE "y"
 in [( "01-Seq:Front-Last:eq"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==>
       (((frnt ss `equalL` frnt tt) /\ (lst ss `equal` lst tt))
        === (ss `equalL` tt)) )
    ,( "02-Seq:LE:prefix"
     , ( ss `ppfx` tt)
       ==>
       (Forall 0 qx ((one `leq` ii /\ ii `leq` (len ss)) ==> (ix ss ii `equal` ix tt ii))) )
    ,( "03a-Seq:Front:len"
     , (ss `neq` nil) ==> ((len (frnt ss)) `equalZ` ((len ss) `minus` one)) )
    ,( "03b-Seq:Front:len'"
     , (ss `neq` nil) ==> ((len ss) `equalZ` ((len (frnt ss)) `plus` one )) )
    ,( "04-Seq:Front:index"
     , (ss `neq` nil)
       ==> ((one `leq` ii /\ ii `leq` (len (frnt ss))) ==> ((ix (frnt ss) ii) `equal` ix ss ii )) )
    ,( "05-Seq:Front:len-index"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==>  ((ix (frnt ss `cat` tt) (len ss) `equal` hd tt ))  )
    ,( "06-Seq:Front:len"
     , (frnt ss `equalL` frnt tt) ==> (len ss `equalZ` len tt) )
    ,( "07-Seq:FrontLT:len"
     , (ss `neq` nil )
       ==> ((frnt ss `pspfx` tt) ==> (len ss `lthan` len tt)) )
    ,( "08-Seq:FrontLT:trans"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==> (((frnt ss `pspfx` tt) /\ (frnt tt `pspfx` uu) ==> (frnt ss `pspfx` uu)) ))
    ,( "09-Seq:FrontLT:eqv"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==> ((frnt ss `pspfx` tt) /\ (frnt tt `pspfx` ss) === (frnt ss `equalL` frnt tt)) )
    ,( "10-Seq:FrontLT:anti"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==> ((frnt ss `pspfx` frnt tt) /\ (frnt tt `pspfx` frnt ss) ==> (frnt ss `equalL` frnt tt)) )
    ,( "11a-Seq:FrontEQ:end"
     , ( frnt (ss `cat` sngll ex) `equalL` frnt (ss `cat` sngll ey `cat` tt))
       === (tt `equalL` nil) )
    ,( "11b-Seq:FrontEQ:end'"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==> (( frnt ss `equalL` frnt tt)
             === (tl (tt `ssub` frnt ss) `equalL` nil)) )
    ,( "12a-Seq:HdSub:index"
     , (tt `pspfx` ss) ==> (hd (ss `ssub` tt) `equal` ix ss ((len tt) `plus` one) ) )
    ,( "12b-Seq:HdSub:index'"
     , (tt `neq` nil)
       ==> ((frnt tt `pspfx` ss) ==> (hd (ss `ssub` frnt tt) `equal` ix ss (len tt) )) )
    ,( "13-Seq:TailSub"
     , (ss `neqL` nil) ==> (tl ss  `equalL` tl (ss `ssub` tt)) === tt `equalL` nil )
    ,( "14-Seq:Front:Cat:Le"
     , ((ss `neq` nil) /\ (tt `neq` nil))
       ==> ((ss `equalL` (frnt tt `cat` uu)) /\ (frnt ss `pspfx` tt)
        ==> (len uu `equalZ` one) ))
    ]

\end{code}

\subsubsection{And the Result is \ldots}

\begin{code}

listsName = "Lists"

theoryLists
  = (nmdNullPrfCtxt listsName)
    { syntaxDeps = [ rootName, equalityName, arithmeticName, setsName ]
    , precs = lbuild precsList
    , types = typesList
    , conjectures = lbuild $ simpleAssertions $ conjsList
    , laws = simpleLaws listsName (lawsList ++ dodList ++ conjsAsLawsList)
    }

theory3BA31Lists
  = (nmdNullPrfCtxt "3BA31Lists")
    { syntaxDeps = [ rootName, equalityName, arithmeticName, setsName ]
    , conjectures = lbuild $ simpleAssertions $ conjsList
    }

\end{code}
We also define a theory stack for test purposes:
\begin{code}

tstTheories
 = [ theoryLists
   , theorySets
   , theoryArithmetic
   , theoryEquality
   ]

tstTypes = map types tstTheories
tstAllTypes = map allthtypes tstTheories

allthtypes thry = (tmap thd3 $ obs thry) `tmerge` types thry

\end{code}

\section{Builtin Maintenance}

Some legacy theories may need adjusting automatically,
or checking, in some way.
