\section{Laws of Logic}

Laws of 2nd order  logic

\begin{code}
module Logic where
import Tables
import Datatypes
import DataText
import Heuristics
import Laws
import Proof
import Theories
import DSL
import RootTheory
import Data.List

import Text.ParserCombinators.Parsec.Expr
\end{code}



\subsection{Useful definitions}

\begin{code}
logicProvenance = FromSOURCE "Logic"
mkLogicLaw = mklaw logicProvenance
freeLogicLaw = freelaw logicProvenance
mkConj nm pr sc = (nm,(pr,sc))
freeConj nm pr = mkConj nm pr SCtrue
\end{code}


\subsection{The Laws}

The parenthesised numbers in inline comments after law definitions
give the the equation number from
``Laws of the Logical Calculi''
by Carroll Morgan and J. W. Sanders,
PRG-78,
September 1989,
Oxford University Computing Laboratory.

\subsubsection{A distributive lattice (2.1)}

\begin{code}
lAndIdem  =  pA /\ pA === pA  -- (1)
lOrIdem   =  pA \/ pA === pA  -- (1)
lAndComm  =  pA /\ pB === pB /\ pA  -- (2)
lOrComm   =  pA \/ pB === pB \/ pA  -- (3)

lAndAssoc = Eqv (And [pA,And[pB,pC]]) (And [And [pA,pB],pC])  -- (4)
lOrAssoc = Eqv (Or [pA,Or[pB,pC]]) (Or [Or [pA,pB],pC])  -- (5)

lAndOrAbsR1 = Eqv (And [pA,Or [pA,pB]]) pA  -- (6)
lAndOrAbsR2 = Eqv (And [pA,Or [pB,pA]]) pA  -- (6)
lAndOrAbsR3 = Eqv (And [Or [pA,pB],pA]) pA  -- (6)
lAndOrAbsR4 = Eqv (And [Or [pB,pA],pA]) pA  -- (6)

lOrAndAbsR1 = Eqv (Or [pA,And [pA,pB]]) pA -- (6)
lOrAndAbsR2 = Eqv (Or [pA,And [pB,pA]]) pA -- (6)
lOrAndAbsR3 = Eqv (Or [And [pA,pB],pA]) pA -- (6)
lOrAndAbsR4 = Eqv (Or [And [pB,pA],pA]) pA -- (6)

lAndOrDistr1 = Eqv (And [pA,Or [pB,pC]]) --(7)
                   (Or [And [pA,pB],And [pA,pC]])
lAndOrDistr2 = Eqv (And [Or [pB,pC],pA]) --(7)
                   (Or [And [pB,pA],And [pC,pA]])

lOrAndDistr1 = Eqv (Or [pA,And [pB,pC]])  -- (8)
                   (And [Or [pA,pB],Or [pA,pC]])
lOrAndDistr2 = Eqv (Or [And [pB,pC],pA])  -- (8)
                   (And [Or [pB,pA],Or [pC,pA]])


laws_2_1
   =   freeLogicLaw "/\\-idem" lAndIdem
   ~:~ freeLogicLaw "/\\-comm" lAndComm
   ~:~ freeLogicLaw "/\\-assoc" lAndAssoc
   ~:~ freeLogicLaw "\\/-idem" lOrIdem
   ~:~ freeLogicLaw "\\/-comm" lOrComm
   ~:~ freeLogicLaw "\\/-assoc" lOrAssoc
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.1" lAndOrAbsR1
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.2" lAndOrAbsR2
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.3" lAndOrAbsR3
   ~:~ freeLogicLaw "/\\-\\/-absorb-R.4" lAndOrAbsR4
   ~:~ freeLogicLaw "/\\-\\/-distr.1" lAndOrDistr1
   ~:~ freeLogicLaw "/\\-\\/-distr.1" lAndOrDistr2
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.1" lOrAndAbsR1
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.2" lOrAndAbsR2
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.3" lOrAndAbsR3
   ~:~ freeLogicLaw "\\/-/\\-absorb-R.4" lOrAndAbsR4
   ~:~ freeLogicLaw "\\/-/\\-distr.1" lOrAndDistr1
   ~:~ freeLogicLaw "\\/-/\\-distr.2" lOrAndDistr2

conj_2_1
   = freeConj "/\\-idem" lAndIdem
   : freeConj "/\\-comm" lAndComm
   : freeConj "/\\-assoc" lAndAssoc
   : freeConj "\\/-idem" lOrIdem
   : freeConj "\\/-comm" lOrComm
   : freeConj "\\/-assoc" lOrAssoc
   : freeConj "/\\-\\/-absorb" lAndOrAbsR1
   : freeConj "/\\-\\/-distr" lAndOrDistr1
   : freeConj "\\/-/\\-absorb" lOrAndAbsR1
   : freeConj "\\/-/\\-distr" lOrAndDistr1
   : []

test_2_1 = [ ( "[/\\-idem]", (Univ 0 lAndIdem,SCtrue))
           , ( "alphaTest1", (alphaTest1,SCtrue))
           , ( "alphaTest2", (alphaTest2,SCtrue))
           , ( "typeTest1",  (typeTest1,SCtrue))
           ] -- for testing
\end{code}

\subsubsection{A Boolean algebra (2.2)}

\begin{code}
lAndUnit1 = Eqv (And [pA,TRUE]) pA  -- (9)
lAndUnit2 = Eqv (And [TRUE,pA]) pA  -- (9)
lOrZero1  = Eqv (Or [pA,TRUE]) TRUE  -- (10)
lOrZero2  = Eqv (Or [TRUE,pA]) TRUE  -- (10)
lAndZero1 = Eqv (And [pA,FALSE]) FALSE  -- (11)
lAndZero2 = Eqv (And [FALSE,pA]) FALSE  -- (11)
lOrUnit1  = Eqv (Or [pA,FALSE]) pA  -- (12)
lOrUnit2  = Eqv (Or [FALSE,pA]) pA  -- (12)

lContradiction1 = Eqv (And [pA,Not pA]) FALSE  -- (13)
lContradiction2 = Eqv (And [Not pA,pA]) FALSE  -- (13)
lNoMiddle1      = Eqv (Or [pA,Not pA]) TRUE  -- (14)
lNoMiddle2      = Eqv (Or [Not pA,pA]) TRUE  -- (14)

lNotNot  = Eqv (Not (Not pA)) pA  -- (15)
lAndDeMorgan = Eqv (And [Not pA,Not pB]) (Not (Or [pA,pB]))  -- (16)
lOrDeMorgan = Eqv (Or [Not pA,Not pB]) (Not (And [pA,pB]))  -- (17)

lOrAndNotAbs1 = Eqv (Or [pA,And [Not pA,pB]]) (Or [pA,pB])  -- (18)
lOrAndNotAbs2 = Eqv (Or [And [Not pA,pB],pA]) (Or [pA,pB])  -- (18)
lAndOrNotAbs1 = Eqv (And [pA,Or [Not pA,pB]]) (And [pA,pB])  -- (19)
lAndOrNotAbs2 = Eqv (And [Or [Not pA,pB],pA]) (And [pA,pB])  -- (19)

laws_2_2
   =   freeLogicLaw "/\\-unit.1" lAndUnit1
   ~:~ freeLogicLaw "/\\-unit.2" lAndUnit2
   ~:~ freeLogicLaw "/\\-zero.1" lAndZero1
   ~:~ freeLogicLaw "/\\-zero.2" lAndZero2
   ~:~ freeLogicLaw "\\/-unit.1" lOrUnit1
   ~:~ freeLogicLaw "\\/-unit.2" lOrUnit2
   ~:~ freeLogicLaw "\\/-zero.1" lOrZero1
   ~:~ freeLogicLaw "\\/-zero.2" lOrZero2
   ~:~ freeLogicLaw "contradiction.1" lContradiction1
   ~:~ freeLogicLaw "contradiction.2" lContradiction2
   ~:~ freeLogicLaw "excluded-middle.1" lNoMiddle1
   ~:~ freeLogicLaw "excluded-middle.2" lNoMiddle2
   ~:~ freeLogicLaw "~~-idem" lNotNot
   ~:~ freeLogicLaw "/\\-deMorgan" lAndDeMorgan
   ~:~ freeLogicLaw "\\/-deMorgan" lOrDeMorgan
   ~:~ freeLogicLaw "\\/-/\\-~-absorb.1" lOrAndNotAbs1
   ~:~ freeLogicLaw "\\/-/\\-~-absorb.2" lOrAndNotAbs2
   ~:~ freeLogicLaw "/\\-\\/-~-absorb.3" lAndOrNotAbs1
   ~:~ freeLogicLaw "/\\-\\/-~-absorb.4" lAndOrNotAbs2
   ~:~ freeLogicLaw "false" (FALSE === Not TRUE)
   ~:~ freeLogicLaw "true" (TRUE === Not FALSE)

conj_2_2
   = freeConj "/\\-unit" lAndUnit1
   : freeConj "/\\-zero" lAndZero1
   : freeConj "\\/-unit" lOrUnit1
   : freeConj "\\/-zero" lOrZero1
   : freeConj "contradiction" lContradiction1
   : freeConj "excluded-middle" lNoMiddle1
   : freeConj "~~-idem" lNotNot
   : freeConj "/\\-deMorgan" lAndDeMorgan
   : freeConj "\\/-deMorgan" lOrDeMorgan
   : freeConj "\\/-/\\-~-absorb" lOrAndNotAbs1
   : freeConj "false" (FALSE === Not TRUE)
   : freeConj "true" (TRUE === Not FALSE)
   : []
\end{code}

\subsubsection{Implication (2.3)}

\begin{code}
lImpDef1 = Eqv (Imp pA pB) (Or [Not pA,pB])  -- (20)
lImpDef2 = Eqv (Imp pA pB) (Or [pB,Not pA])  -- (20)
lImpSelf = Eqv (Imp pA pA) TRUE  -- (21)
lImpAlt11 = Eqv (Imp pA pB) (Not (And [pA,Not pB]))  -- (22)
lImpAlt12 = Eqv (Imp pA pB) (Not (And [Not pB,pA]))  -- (22)
lNotImp1 = Eqv (Not (Imp pA pB)) (And [pA,Not pB])  -- (23)
lNotImp2 = Eqv (Not (Imp pA pB)) (And [Not pB,pA])  -- (23)
lContrapos = Eqv (Imp pA pB) (Imp (Not pB) (Not pA))  -- (24)

lImpTrue = Eqv (Imp pA TRUE) TRUE  -- (25)
lTrueImp = Eqv (Imp TRUE pA) pA  -- (26)
lImpFalse = Eqv (Imp pA FALSE) (Not pA)  -- (27)
lFalseImp = Eqv (Imp FALSE pA) TRUE  -- (28)
lImpNeg = Eqv (Imp pA (Not pA)) (Not pA)  -- (29)
lNegImp = Eqv (Imp (Not pA) pA) pA  -- (30)

lImpAndDistr = Eqv (Imp pC (And [pA,pB])) (And [Imp pC pA,Imp pC pB])  -- (31)
lOrImpDistr = Eqv (Imp (Or [pA,pB]) pC) (And [Imp pA pC,Imp pB pC])  -- (32)

lBoolMeet1 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv (And [pA,pB]) pA)
lBoolMeet2 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv (And [pA,pB]) pA)
lBoolMeet3 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv (And [pB,pA]) pA)
lBoolMeet4 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv (And [pB,pA]) pA)
lBoolMeet5 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv pA (And [pA,pB]))
lBoolMeet6 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv pA (And [pA,pB]))
lBoolMeet7 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv pA (And [pB,pA]))
lBoolMeet8 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv pA (And [pB,pA]))

lBoolJoin1 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv (Or [pA,pB]) pB)
lBoolJoin2 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv (Or [pA,pB]) pB)
lBoolJoin3 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv (Or [pB,pA]) pB)
lBoolJoin4 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv (Or [pB,pA]) pB)
lBoolJoin5 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv pB (Or [pA,pB]))
lBoolJoin6 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv pB (Or [pA,pB]))
lBoolJoin7 = Eqv (Or [Not pA,pB])  -- (33)
                 (Eqv pB (Or [pB,pA]))
lBoolJoin8 = Eqv (Or [pB,Not pA])  -- (33)
                 (Eqv pB (Or [pB,pA]))

lImpMrg1 = Eqv (Imp pA (Imp pB pC)) (Imp (And [pA,pB]) pC)  -- (34)
lImpMrg2 = Eqv (Imp pA (Imp pB pC)) (Imp pB (Imp pA pC))  -- (35)

lImpCases1 = Eqv (And [Imp pA pB,Imp (Not pA) pC])  -- (36)
                 (Or [And [pA,pB],And[Not pA,pC]])
lImpCases2 = Eqv (And [Imp (Not pA) pC,Imp pA pB])  -- (36)
                 (Or [And [pA,pB],And[Not pA,pC]])
lImpCases3 = Eqv (And [Imp pA pB,Imp (Not pA) pC])  -- (36)
                 (Or [And[Not pA,pC],And [pA,pB]])
lImpCases4 = Eqv (And [Imp (Not pA) pC,Imp pA pB])  -- (36)
                 (Or [And[Not pA,pC],And [pA,pB]])

laws_2_3
   =   freeLogicLaw "DEF-=>.1" lImpDef1
   ~:~ freeLogicLaw "DEF-=>.2" lImpDef2
   ~:~ freeLogicLaw "=>-self" lImpSelf
   ~:~ freeLogicLaw "=>-alt1" lImpAlt11
   ~:~ freeLogicLaw "=>-alt2" lImpAlt12
   ~:~ freeLogicLaw "=>-neg.1" lNotImp1
   ~:~ freeLogicLaw "=>-neg.2" lNotImp2
   ~:~ freeLogicLaw "contrapositive" lContrapos
   ~:~ freeLogicLaw "=>-true" lImpTrue
   ~:~ freeLogicLaw "true-=>" lTrueImp
   ~:~ freeLogicLaw "=>-false" lImpFalse
   ~:~ freeLogicLaw "false-=>" lFalseImp
   ~:~ freeLogicLaw "=>-neg" lImpNeg
   ~:~ freeLogicLaw "neg-=>" lNegImp
   ~:~ freeLogicLaw "=>-/\\-distr" lImpAndDistr
   ~:~ freeLogicLaw "\\/-=>-distr" lOrImpDistr
   ~:~ freeLogicLaw "bool-meet.1" lBoolMeet1
   ~:~ freeLogicLaw "bool-meet.2" lBoolMeet2
   ~:~ freeLogicLaw "bool-meet.3" lBoolMeet3
   ~:~ freeLogicLaw "bool-meet.4" lBoolMeet4
   ~:~ freeLogicLaw "bool-meet.5" lBoolMeet5
   ~:~ freeLogicLaw "bool-meet.6" lBoolMeet6
   ~:~ freeLogicLaw "bool-meet.7" lBoolMeet7
   ~:~ freeLogicLaw "bool-meet.8" lBoolMeet8
   ~:~ freeLogicLaw "bool-join.1" lBoolJoin1
   ~:~ freeLogicLaw "bool-join.2" lBoolJoin2
   ~:~ freeLogicLaw "bool-join.3" lBoolJoin3
   ~:~ freeLogicLaw "bool-join.4" lBoolJoin4
   ~:~ freeLogicLaw "bool-join.5" lBoolJoin5
   ~:~ freeLogicLaw "bool-join.6" lBoolJoin6
   ~:~ freeLogicLaw "bool-join.7" lBoolJoin7
   ~:~ freeLogicLaw "bool-join.8" lBoolJoin8
   ~:~ freeLogicLaw "=>-merge.1" lImpMrg1
   ~:~ freeLogicLaw "=>-merge.2" lImpMrg2
   ~:~ freeLogicLaw "=>-cases.1" lImpCases1
   ~:~ freeLogicLaw "=>-cases.2" lImpCases2
   ~:~ freeLogicLaw "=>-cases.3" lImpCases3
   ~:~ freeLogicLaw "=>-cases.4" lImpCases4

conj_2_3
   = freeConj "DEF-=>" lImpDef1
   : freeConj "=>-self" lImpSelf
   : freeConj "=>-alt" lImpAlt11
   : freeConj "=>-neg" lNotImp1
   : freeConj "contrapositive" lContrapos
   : freeConj "=>-true" lImpTrue
   : freeConj "true-=>" lTrueImp
   : freeConj "=>-false" lImpFalse
   : freeConj "false-=>" lFalseImp
   : freeConj "=>-neg" lImpNeg
   : freeConj "neg-=>" lNegImp
   : freeConj "=>-/\\-distr" lImpAndDistr
   : freeConj "\\/-=>-distr" lOrImpDistr
   : freeConj "bool-meet" lBoolMeet1
   : freeConj "bool-join" lBoolJoin1
   : freeConj "=>-merge" lImpMrg1
   : freeConj "=>-cases" lImpCases1
   : []
\end{code}

\subsubsection{Other connectives (2.4)}

\begin{code}
lEqvDef  =  Eqv (Eqv pA pB) (And [Imp pA pB, Imp pB pA])  -- (37)
lEqvAlt11 =  Eqv (Eqv pA pB) (Or [And [pA,pB], Not (Or [pA,pB])])  -- (38)
lEqvAlt12 =  Eqv (Eqv pA pB) (Or [And [pB,pA], Not (Or [pA,pB])])  -- (38)
lEqvAlt2 =  Eqv (Eqv pA pB) (Eqv (Not pA) (Not pB))  -- (39)

lEqvSame   =  Eqv (Eqv pA pA) TRUE  -- (40)
lEqvDiff1   =  Eqv (Eqv pA (Not pA)) FALSE  -- (41)
lEqvDiff2   =  Eqv (Eqv (Not pA) pA) FALSE  -- (41)
lEqvTrue   =  Eqv (Eqv pA TRUE) pA  -- (42)
lEqvFalse  =  Eqv (Eqv pA FALSE) (Not pA)  -- (43)
lImpAlt21   =  Eqv (Imp pA pB) (Eqv pA (And [pA,pB]))  -- (44)
lImpAlt22   =  Eqv (Imp pA pB) (Eqv pA (And [pB,pA]))  -- (44)
lImpAlt23   =  Eqv (Imp pA pB) (Eqv (And [pA,pB]) pA)  -- (44)
lImpAlt24   =  Eqv (Imp pA pB) (Eqv (And [pB,pA]) pA)  -- (44)
lImpAlt31   =  Eqv (Imp pB pA) (Eqv pA (Or [pA,pB]))  -- (45)
lImpAlt32   =  Eqv (Imp pB pA) (Eqv pA (Or [pB,pA]))  -- (45)
lImpAlt33   =  Eqv (Imp pB pA) (Eqv (Or [pA,pB]) pA)  -- (45)
lImpAlt34   =  Eqv (Imp pB pA) (Eqv (Or [pB,pA]) pA)  -- (45)
lOrEqvDistr1  =  Eqv (Or [pA,Eqv pB pC])  -- (46)
                     (Eqv (Or [pA,pB]) (Or [pA,pC]))
lOrEqvDistr2  =  Eqv (Or [Eqv pB pC,pA])  -- (46)
                     (Eqv (Or [pA,pB]) (Or [pA,pC]))
lOrEqvDistr3  =  Eqv (Or [pA,Eqv pB pC])  -- (46)
                     (Eqv (Or [pB,pA]) (Or [pC,pA]))
lOrEqvDistr4  =  Eqv (Or [Eqv pB pC,pA])  -- (46)
                     (Eqv (Or [pB,pA]) (Or [pC,pA]))

lEqvComm  = Eqv (Eqv pA pB) (Eqv pB pA)  -- (47)
lEqvAssoc = Eqv (Eqv pA (Eqv pB pC)) (Eqv (Eqv pA pB) pC)  -- (48)

-- The "Golden Rule"

goldenRule1 = Eqv (Eqv pA pB)  -- (49)
                  (Eqv (And [pA,pB]) (Or [pA,pB]))
goldenRule2 = Eqv (Eqv pA pB)  -- (49)
                  (Eqv (And [pB,pA]) (Or [pA,pB]))
goldenRule3 = Eqv (Eqv pA pB)  -- (49)
                  (Eqv (Or [pA,pB]) (And [pA,pB]))
goldenRule4 = Eqv (Eqv pA pB)  -- (49)
                  (Eqv (Or [pA,pB]) (And [pB,pA]))
goldenRule5 = Eqv (Eqv pB pA)  -- (49)
                  (Eqv (And [pA,pB]) (Or [pA,pB]))
goldenRule6 = Eqv (Eqv pB pA)  -- (49)
                  (Eqv (And [pB,pA]) (Or [pA,pB]))
goldenRule7 = Eqv (Eqv pB pA)  -- (49)
                  (Eqv (Or [pA,pB]) (And [pA,pB]))
goldenRule8 = Eqv (Eqv pB pA)  -- (49)
                  (Eqv (Or [pA,pB]) (And [pB,pA]))

-- laws 50 through 59 regarding Exclusive-Or are not given here.

lCondDef1  =  Eqv (If pC pA pB) (Or [And [pC,pA], And [Not pC,pB]])
lCondDef2 =  Eqv (If pC pA pB) (Or [And [pA,pC], And [Not pC,pB]])
lCondDef3  =  Eqv (If pC pA pB) (Or [And [pC,pA], And [pB,Not pC]])
lCondDef4  =  Eqv (If pC pA pB) (Or [And [pA,pC], And [pB,Not pC]])
lCondDef5  =  Eqv (If pC pA pB) (Or [And [Not pC,pB], And [pC,pA]])
lCondDef6  =  Eqv (If pC pA pB) (Or [And [Not pC,pB], And [pA,pC]])
lCondDef7  =  Eqv (If pC pA pB) (Or [And [pB,Not pC], And [pC,pA]])
lCondDef8  =  Eqv (If pC pA pB) (Or [And [pB,Not pC], And [pA,pC]])

lCondAlt1  =  Eqv (If pC pA pB) (And [Imp pC pA, Imp (Not pC) pB])  -- (60)
lCondAlt2  =  Eqv (If pC pA pB) (And [Imp (Not pC) pB, Imp pC pA])  -- (60)

lCondIdem  =  Eqv  (If pP pA pA) pA  -- (61)
lCondLeftAbs =    Eqv (If pP pA (If pP pB pC)) (If pP pA pC)  -- (62)
lCondRighttAbs =  Eqv (If pP (If pP pA pB) pC) (If pP pA pC)  -- (63)
lCondRightDistr  -- (64)
  = Eqv (If pP pA (If pQ pB pC))
        (If pQ (If pP pA pB) (If pP pA pC))
lCondLeftDistr  -- (65)
  = Eqv (If pQ (If pP pA pB) pC)
        (If pP (If pQ pA pC) (If pQ pB pC))

lCondTrue = Eqv  (If TRUE pA pB) pA  -- (66)
lCondFalse = Eqv (If FALSE pA pB) pB  -- (67)

lAndAsCond1 = Eqv (And [pA,pB]) (If pB pA pB)  -- (68)
lAndAsCond2 = Eqv (And [pB,pA]) (If pB pA pB)  -- (68)

lOrAsCond1 = Eqv (Or [pA,pB]) (If pA pA pB)  -- (69)
lOrAsCond2 = Eqv (Or [pB,pA]) (If pA pA pB)  -- (69)

lNotAsCond = Eqv (Not pA) (If pA FALSE TRUE)  -- (70)
lPredAsCond = Eqv (If pA TRUE FALSE) pA  -- (71)
lCondNest  -- (72)
  = Eqv (If (If pP pB pC) pA pD)
        (If pP (If pB pA pD) (If pC pA pD))

laws_2_4
   =   freeLogicLaw "DEF-==" lEqvDef
   ~:~ freeLogicLaw "==-alt1.1" lEqvAlt11
   ~:~ freeLogicLaw "==-alt1.2" lEqvAlt12
   ~:~ freeLogicLaw "==-alt2" lEqvAlt2
   ~:~ freeLogicLaw "==-same" lEqvSame
   ~:~ freeLogicLaw "==-diff.1" lEqvDiff1
   ~:~ freeLogicLaw "==-diff.2" lEqvDiff2
   ~:~ freeLogicLaw "==-true" lEqvTrue
   ~:~ freeLogicLaw "==-false" lEqvFalse
   ~:~ freeLogicLaw "=>-alt2.1" lImpAlt21
   ~:~ freeLogicLaw "=>-alt2.2" lImpAlt22
   ~:~ freeLogicLaw "=>-alt2.3" lImpAlt23
   ~:~ freeLogicLaw "=>-alt2.4" lImpAlt24
   ~:~ freeLogicLaw "=>-alt3.1" lImpAlt31
   ~:~ freeLogicLaw "=>-alt3.2" lImpAlt32
   ~:~ freeLogicLaw "=>-alt3.3" lImpAlt33
   ~:~ freeLogicLaw "=>-alt3.4" lImpAlt34
   ~:~ freeLogicLaw "\\/-==-distr.1" lOrEqvDistr1
   ~:~ freeLogicLaw "\\/-==-distr.2" lOrEqvDistr2
   ~:~ freeLogicLaw "\\/-==-distr.3" lOrEqvDistr3
   ~:~ freeLogicLaw "\\/-==-distr.4" lOrEqvDistr4
   ~:~ freeLogicLaw "==-comm" lEqvComm
   ~:~ freeLogicLaw "==-assoc" lEqvAssoc
   ~:~ freeLogicLaw "Golden-Rule.1" goldenRule1
   ~:~ freeLogicLaw "Golden-Rule.2" goldenRule2
   ~:~ freeLogicLaw "Golden-Rule.3" goldenRule3
   ~:~ freeLogicLaw "Golden-Rule.4" goldenRule4
   ~:~ freeLogicLaw "Golden-Rule.5" goldenRule5
   ~:~ freeLogicLaw "Golden-Rule.6" goldenRule6
   ~:~ freeLogicLaw "Golden-Rule.7" goldenRule7
   ~:~ freeLogicLaw "Golden-Rule.8" goldenRule8
   ~:~ freeLogicLaw "DEF-<||>.1" lCondDef1
   ~:~ freeLogicLaw "DEF-<||>.2" lCondDef2
   ~:~ freeLogicLaw "DEF-<||>.3" lCondDef3
   ~:~ freeLogicLaw "DEF-<||>.4" lCondDef4
   ~:~ freeLogicLaw "DEF-<||>.5" lCondDef5
   ~:~ freeLogicLaw "DEF-<||>.6" lCondDef6
   ~:~ freeLogicLaw "DEF-<||>.7" lCondDef7
   ~:~ freeLogicLaw "DEF-<||>.8" lCondDef8
   ~:~ freeLogicLaw "<||>-alt.1" lCondAlt1
   ~:~ freeLogicLaw "<||>-alt.2" lCondAlt2
   ~:~ freeLogicLaw "<||>-R-distr" lCondRightDistr
   ~:~ freeLogicLaw "<||>-L-distr" lCondLeftDistr
   ~:~ freeLogicLaw "<|true|>" lCondTrue
   ~:~ freeLogicLaw "<|false|>" lCondFalse
   ~:~ freeLogicLaw "/\\-as-<||>.1" lAndAsCond1
   ~:~ freeLogicLaw "/\\-as-<||>.2" lAndAsCond2
   ~:~ freeLogicLaw "\\/-as-<||>.1" lOrAsCond1
   ~:~ freeLogicLaw "\\/-as-<||>.2" lOrAsCond2
   ~:~ freeLogicLaw "~-as-<||>" lNotAsCond
   ~:~ freeLogicLaw "P-as-<||>" lPredAsCond
   ~:~ freeLogicLaw "<||>-nest" lCondNest

conj_2_4
   = freeConj "DEF-==" lEqvDef
   : freeConj "==-alt1" lEqvAlt11
   : freeConj "==-alt2" lEqvAlt2
   : freeConj "==-same" lEqvSame
   : freeConj "==-diff" lEqvDiff1
   : freeConj "==-true" lEqvTrue
   : freeConj "==-false" lEqvFalse
   : freeConj "=>-alt2" lImpAlt21
   : freeConj "\\/-==-distr" lOrEqvDistr1
   : freeConj "==-comm" lEqvComm
   : freeConj "==-assoc" lEqvAssoc
   : freeConj "Golden-Rule" goldenRule1
   : freeConj "<||>-alt" lCondAlt1
   : freeConj "<||>-R-distr" lCondRightDistr
   : freeConj "<||>-L-distr" lCondLeftDistr
   : freeConj "<|true|>" lCondTrue
   : freeConj "<|false|>" lCondFalse
   : freeConj "/\\-as-<||>" lAndAsCond1
   : freeConj "\\/-as-<||>" lOrAsCond1
   : freeConj "~-as-<||>" lNotAsCond
   : freeConj "P-as-<||>" lPredAsCond
   : freeConj "<||>-nest" lCondNest
   : []
\end{code}

The following isn't worth a sub-section:
\begin{code}
lJoin1 = Imp pA (Or [pA,pB])  -- (73)
lJoin2 = Imp pB (Or [pA,pB])  -- (73)
lMeet1 = Imp (And [pA,pB]) pA  -- (74)
lMeet2 = Imp (And [pA,pB]) pB  -- (74)

laws_3
   =   freeLogicLaw "=>-\\/-join" lJoin1
   ~:~ freeLogicLaw "=>-\\/-join" lJoin2
   ~:~ freeLogicLaw "/\\-=>-meet" lMeet1
   ~:~ freeLogicLaw "/\\-=>-meet" lMeet2

conj_3
   = freeConj "=>-\\/-join" lJoin1
   : freeConj "/\\-=>-meet" lMeet1
   : []
\end{code}

Laws (75) and (76) in Section 4 are not relevant.

\subsubsection{Some predicate laws (4)}

We generalise the laws to use quantifier list-variables where relevant.

\subsubsection{Eliminating quantifiers (4.3)}


The one-point laws as originally stated are missing a side-condition,
namely that the quantified variable must also not be free in the
term with which it is asserted to be equal.
\begin{eqnarray*}
% \nonumber to remove numbering (before each equation)
  (\forall x \cdot x=t \implies A)
  & \equiv \quad A[t/x] \quad \equiv &
  (\exists x \cdot x=t \land A)
\\ & x \mbox{ not free in } t
\end{eqnarray*}

\begin{code}
lForall1Pt1  -- (77)
  = Eqv (mkAll qxxs (Imp (Obs (eqx `Equal` e)) pA))
        (mkAll qxs (Sub pA (Substn [(vx,e)])))
lForall1Pt2  -- (77)
  = Eqv (mkAll qxxs (Imp (Obs (e `Equal` eqx)) pA))
        (mkAll qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt1  -- (77)
  = Eqv (mkAny qxxs (And [(Obs (eqx `Equal` e)),pA]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt2  -- (77)
  = Eqv (mkAny qxxs (And [(Obs (e `Equal` eqx)),pA]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt3  -- (77)
  = Eqv (mkAny qxxs (And [pA,(Obs (eqx `Equal` e))]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))
lEx1Pt4  -- (77)
  = Eqv (mkAny qxxs (And [pA,(Obs (e `Equal` eqx))]))
        (mkAny qxs (Sub pA (Substn [(vx,e)])))

-- we ignore (78) and (79) at this point.

laws_4_3
   = mkLogicLaw "forall-1-pt.1" lForall1Pt1 x_NotFreeIn_e
   ~:~ mkLogicLaw "forall-1-pt.2" lForall1Pt2 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.1" lEx1Pt1 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.2" lEx1Pt2 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.3" lEx1Pt3 x_NotFreeIn_e
   ~:~ mkLogicLaw "exists-1-pt.4" lEx1Pt4 x_NotFreeIn_e

conj_4_3
   = mkConj "forall-1-pt" lForall1Pt1 x_NotFreeIn_e
   : mkConj "exists-1-pt" lEx1Pt1 x_NotFreeIn_e
   : []
\end{code}

\subsubsection{Quantifiers alone (4.4)}

\begin{code}
lForallIdem = Eqv (mkAll qxs (mkAll qxs pA)) (mkAll qxs pA)  -- (80)
lExIdem = Eqv (mkAny qxs (mkAny qxs pA)) (mkAny qxs pA)  -- (81)

lForallDeMorgan = Eqv (Not (mkAll qxs pA)) (mkAny qxs (Not pA))  -- (82)
lExDeMorgan   = Eqv (Not (mkAny qxs pA)) (mkAll qxs (Not pA))  -- (83)

laws_4_4
   =   freeLogicLaw "forall-idem" lForallIdem
   ~:~ freeLogicLaw "exists-idem" lExIdem
   ~:~ freeLogicLaw "forall-deMorgan" lForallDeMorgan
   ~:~ freeLogicLaw "exists-deMorgan" lExDeMorgan

conj_4_4
   = freeConj "forall-idem" lForallIdem
   : freeConj "exists-idem" lExIdem
   : freeConj "forall-deMorgan" lForallDeMorgan
   : freeConj "exists-deMorgan" lExDeMorgan
   : []
\end{code}


\subsubsection{Extending the commutative laws (4.5)}

\begin{code}
lForallComm = Eqv (mkAll qxs (mkAll qys pA))  -- (84)
                (mkAll qys (mkAll qxs pA))
lExComm = Eqv (mkAny qxs (mkAny qys pA))  -- (85)
              (mkAny qys (mkAny qxs pA))

laws_4_5
   = freeLogicLaw "forall-comm" lForallComm
   ~:~ freeLogicLaw "exists-comm" lExComm

conj_4_5
   = freeConj "forall-comm" lForallComm
   : freeConj "exists-comm" lExComm
   : []
\end{code}

\subsubsection{Quantifiers accompanied (4.6)}

\begin{code}
lAndForallDistr1 = Eqv (mkAll qxs (And [pA,pB]))  -- (86)
                       (And [mkAll qxs pA,mkAll qxs pB])
lAndForallDistr2 = Eqv (mkAll qxs (And [pB,pA]))  -- (86)
                       (And [mkAll qxs pA,mkAll qxs pB])

lOrExDistr1 = Eqv (mkAny qxs (Or [pA,pB]))  -- (87)
                  (Or [mkAny qxs pA,mkAny qxs pB])
lOrExDistr2 = Eqv (mkAny qxs (Or [pB,pA]))  -- (87)
                  (Or [mkAny qxs pA,mkAny qxs pB])

lImpExDistr = Eqv (mkAny qxs (Imp pA pB))  -- (88)
                  (Imp (mkAll qxs pA) (mkAny qxs pB))

lForallImpEx = Imp (mkAll qxs pA) (mkAny qxs pA)  -- (89)

lOrForallIDistr1 = Imp (Or [mkAll qxs pA,mkAll qxs pB])  -- (90)
                       (mkAll qxs (Or [pA,pB]))
lOrForallIDistr2 = Imp (Or [mkAll qxs pA,mkAll qxs pB])  -- (90)
                       (mkAll qxs (Or [pB,pA]))

lForallImpImp = Imp (mkAll qxs (Imp pA pB))  -- (91)
                    (Imp (mkAll qxs pA) (mkAll qxs pB))

lAndExIDistr1 = Imp (mkAny qxs (And [pA,pB]))  -- (92)
                    (And [mkAny qxs pA,mkAny qxs pB])
lAndExIDistr2 = Imp (mkAny qxs (And [pB,pA]))  -- (92)
                    (And [mkAny qxs pA,mkAny qxs pB])

lExImpImp = Imp (Imp (mkAny qxs pA) (mkAny qxs pB))  -- (93)
                (mkAny qxs (Imp pA pB))
lExForallSwap = Imp (mkAny qys (mkAll qxs pA))  -- (94)
                    (mkAll qxs (mkAny qys pA))

laws_4_6
   =   freeLogicLaw "/\\-forall-distr.1" lAndForallDistr1
   ~:~ freeLogicLaw "/\\-forall-distr.2" lAndForallDistr2
   ~:~ freeLogicLaw "\\/-exists-distr.1" lOrExDistr1
   ~:~ freeLogicLaw "\\/-exists-distr.2" lOrExDistr2
   ~:~ freeLogicLaw "=>-exists-distr" lImpExDistr
   ~:~ freeLogicLaw "forall-=>-exists" lForallImpEx
   ~:~ freeLogicLaw "\\/:forall-=>-forall:\\/.1" lOrForallIDistr1
   ~:~ freeLogicLaw "\\/:forall-=>-forall:\\/.2" lOrForallIDistr2
   ~:~ freeLogicLaw "forall:=>-=>-=>:forall" lForallImpImp
   ~:~ freeLogicLaw "exists:/\\-=>-/\\:exists.1" lAndExIDistr1
   ~:~ freeLogicLaw "exists:/\\-=>-/\\:exists.2" lAndExIDistr2
   ~:~ freeLogicLaw "=>:exists-=>-exists:=>" lExImpImp
   ~:~ freeLogicLaw "exists:forall-swap" lExForallSwap

conj_4_6
   = freeConj "/\\-forall-distr" lAndForallDistr1
   : freeConj "\\/-exists-distr" lOrExDistr1
   : freeConj "=>-exists-distr" lImpExDistr
   : freeConj "forall-=>-exists" lForallImpEx
   : freeConj "\\/:forall-=>-forall:\\/" lOrForallIDistr1
   : freeConj "forall:=>-=>-=>:forall" lForallImpImp
   : freeConj "exists:/\\-=>-/\\:exists" lAndExIDistr1
   : freeConj "=>:exists-=>-exists:=>" lExImpImp
   : freeConj "exists:forall-swap" lExForallSwap
   : []
\end{code}

\subsubsection{Manipulation of quantifiers (4.7)}

We now have lots of side-conditions regarding free-variables.
\begin{code}
lForallVac = Eqv (mkAll qx pA) pA  -- (95)
lExVac = Eqv (mkAny qx pA) pA  -- (96)
lForallVac' = Eqv (mkAll qxxs pA) (mkAll qxs pA)
lExVac' = Eqv (mkAny qxxs pA) (mkAny qxs pA)

lFreeAndForallDistr1 = Eqv (mkAll qxs (And[pN,pB]))  -- (97)
                           (And [pN,mkAll qxs pB])
lFreeAndForallDistr2 = Eqv (mkAll qxs (And[pB,pN]))  -- (97)
                           (And [pN,mkAll qxs pB])

lFreeOrForallDistr1 = Eqv (mkAll qxs (Or[pN,pB]))  -- (98)
                          (Or [pN,mkAll qxs pB])
lFreeOrForallDistr2 = Eqv (mkAll qxs (Or[pB,pN]))  -- (98)
                          (Or [pN,mkAll qxs pB])

lFreeAnteForallDistr = Eqv (mkAll qxs (Imp pN pB))  -- (99)
                         (Imp pN (mkAll qxs pB))
lFreeCnsqForallDistr = Eqv (mkAll qxs (Imp pA pN))  -- (100)
                         (Imp (mkAny qxs pA) pN)
lFreeCondForallDistr = Eqv (mkAll qxs (If pN pA pB))  -- (101)
                         (If pN (mkAll qxs pA) (mkAll qxs pB))

lFreeAndExDistr1 = Eqv (mkAny qxs (And[pN,pB]))  -- (102)
                       (And [pN,mkAny qxs pB])
lFreeAndExDistr2 = Eqv (mkAny qxs (And[pB,pN]))  -- (102)
                       (And [pN,mkAny qxs pB])

lFreeOrExDistr1 = Eqv (mkAny qxs (Or[pN,pB]))  -- (103)
                      (Or [pN,mkAny qxs pB])
lFreeOrExDistr2 = Eqv (mkAny qxs (Or[pB,pN]))  -- (103)
                      (Or [pN,mkAny qxs pB])

lFreeAnteExDistr = Eqv (mkAny qxs (Imp pN pB))  -- (104)
                       (Imp pN (mkAny qxs pB))
lFreeCnsqExDistr = Eqv (mkAny qxs (Imp pA pN))  -- (105)
                       (Imp (mkAll qxs pA) pN)
lFreeCondExDistr = Eqv (mkAny qxs (If pN pA pB))  -- (106)
                       (If pN (mkAny qxs pA) (mkAny qxs pB))

lForallAlpha = Eqv (mkAll qxxs pA)  -- (107)
                 (mkAll qyxs (Sub pA (Substn [(vx,eqy)])))
lExAlpha = Eqv (mkAny qxxs pA)  -- (108)
               (mkAny qyxs (Sub pA (Substn [(vx,eqy)])))
lForallAlpha' = Eqv (mkAll qxxs (Sub pA (Substn [(vz,eqx)])))  -- (109)
                  (mkAll qyxs (Sub pA (Substn [(vz,eqy)])))
lExAlpha' = Eqv (mkAny qxxs (Sub pA (Substn [(vz,eqx)])))  -- (110)
                (mkAny qyxs (Sub pA (Substn [(vz,eqy)])))

lForallSpec = Imp (mkAll qx pA) (Sub pA (Substn [(vx,e)]))  -- (111)
lExGen    = Imp (Sub pA (Substn [(vx,e)])) (mkAny qx pA)  -- (112)

laws_4_7
   = mkLogicLaw "forall-vac" lForallVac xNFinA
   ~:~ mkLogicLaw "exists-vac" lExVac xNFinA
   ~:~ mkLogicLaw "forall-vac'" lForallVac' xNFinA
   ~:~ mkLogicLaw "exists-vac'" lExVac' xNFinA
   ~:~ mkLogicLaw "free-/\\-forall-distr'.1" lFreeAndForallDistr1 xsNFinN
   ~:~ mkLogicLaw "free-/\\-forall-distr'.2" lFreeAndForallDistr2 xsNFinN
   ~:~ mkLogicLaw "free-\\/-forall-distr'.1" lFreeOrForallDistr1 xsNFinN
   ~:~ mkLogicLaw "free-\\/-forall-distr'.2" lFreeOrForallDistr2 xsNFinN
   ~:~ mkLogicLaw "free-ante-forall-distr'" lFreeAnteForallDistr xsNFinN
   ~:~ mkLogicLaw "free-cnsq-forall-distr'" lFreeCnsqForallDistr xsNFinN
   ~:~ mkLogicLaw "free-cond-forall-distr'" lFreeCondForallDistr xsNFinN
   ~:~ mkLogicLaw "free-/\\-exists-distr'.1" lFreeAndExDistr1 xsNFinN
   ~:~ mkLogicLaw "free-/\\-exists-distr'.2" lFreeAndExDistr2 xsNFinN
   ~:~ mkLogicLaw "free-\\/-exists-distr'.1" lFreeOrExDistr1 xsNFinN
   ~:~ mkLogicLaw "free-\\/-exists-distr'.2" lFreeOrExDistr2 xsNFinN
   ~:~ mkLogicLaw "free-ante-exists-distr'" lFreeAnteExDistr xsNFinN
   ~:~ mkLogicLaw "free-cnsq-exists-distr'" lFreeCnsqExDistr xsNFinN
   ~:~ mkLogicLaw "free-cond-exists-distr'" lFreeCondExDistr xsNFinN
   ~:~ mkLogicLaw "forall-alpha" lForallAlpha yNFinA
   ~:~ mkLogicLaw "exists-alpha" lExAlpha yNFinA
   ~:~ mkLogicLaw "forall-alpha'" lForallAlpha' xyNFinA
   ~:~ freeLogicLaw "forall-spec" lForallSpec
   ~:~ freeLogicLaw "exists-gen" lExGen

conj_4_7
   = mkConj "forall-vac" lForallVac xNFinA
   : mkConj "exists-vac" lExVac xNFinA
   : mkConj "forall-vac'" lForallVac' xNFinA
   : mkConj "exists-vac'" lExVac' xNFinA
   : mkConj "free-/\\-forall-distr'" lFreeAndForallDistr1 xsNFinN
   : mkConj "free-\\/-forall-distr'" lFreeOrForallDistr1 xsNFinN
   : mkConj "free-ante-forall-distr'" lFreeAnteForallDistr xsNFinN
   : mkConj "free-cnsq-forall-distr'" lFreeCnsqForallDistr xsNFinN
   : mkConj "free-cond-forall-distr'" lFreeCondForallDistr xsNFinN
   : mkConj "free-/\\-exists-distr'" lFreeAndExDistr1 xsNFinN
   : mkConj "free-\\/-exists-distr'" lFreeOrExDistr1 xsNFinN
   : mkConj "free-ante-exists-distr'" lFreeAnteExDistr xsNFinN
   : mkConj "free-cnsq-exists-distr'" lFreeCnsqExDistr xsNFinN
   : mkConj "free-cond-exists-distr'" lFreeCondExDistr xsNFinN
   : mkConj "forall-alpha" lForallAlpha yNFinA
   : mkConj "exists-alpha" lExAlpha yNFinA
   : mkConj "forall-alpha'" lForallAlpha' xyNFinA
   : freeConj "forall-spec" lForallSpec
   : freeConj "exists-gen" lExGen
   : []
\end{code}

\subsubsection{Quantifiers over booleans}

Boolean quantification admits the following simplification:
\begin{eqnarray*}
   (\exists b:\Bool @ A) &\equiv& A[True/b] \lor A[False/b]
\\ (\forall b:\Bool @ A) &\equiv& A[True/b] \land A[False/b]
\end{eqnarray*}
Given that we do not yet handle types properly,
we need to use cues from expressions regarding the presence
of booleans, leading to the following laws:
\begin{eqnarray*}
   (\exists b @ A \land b) &\equiv& A[True/b]
\\ (\forall b @ A \land b) &\equiv& False
\\ (\exists b @ A \lor b)  &\equiv& True
\\ (\forall b @ A \lor b)  &\equiv& A[False/b]
\\ (\exists b @ A \implies b) &\equiv& True
\\ (\forall b @ A \implies b) &\equiv& \lnot A[False/b]
\\ (\exists b @ b \implies A) &\equiv& True
\\ (\forall b @ b \implies A) &\equiv& A[True/b]
\\ (\exists b @ b \equiv A) &\equiv& A[True/b] \lor \lnot A[False/b]
\\ (\forall b @ b \equiv A) &\equiv& A[True/b] \land \lnot A[False/b]
\end{eqnarray*}
\begin{code}
lExBoolAnd1  = (mkAny bvxs (bp /\ pA))  === (mkAny qxs (subb pA T))
lExBoolAnd2  = (mkAny bvxs (pA /\ bp))  === (mkAny qxs (subb pA T))

lAllBoolAnd1 = (mkAll bvxs (bp /\ pA))  === FALSE
lAllBoolAnd2 = (mkAll bvxs (pA /\ bp))  === FALSE

lExBoolOr1   = (mkAny bvxs (bp \/ pA))  === TRUE
lExBoolOr2   = (mkAny bvxs (pA \/ bp))  === TRUE

lAllBoolOr1  = (mkAll bvxs (bp \/ pA))  === (subb pA F)
lAllBoolOr2  = (mkAll bvxs (pA \/ bp))  === (subb pA F)

lExBoolPmi   = (mkAny bvxs (pA ==> bp)) === TRUE
lAllBoolPmi  = (mkAll bvxs (pA ==> bp)) === Not (subb pA F)
lExBoolImp   = (mkAny bvxs (bp ==> pA)) === TRUE
lAllBoolImp  = (mkAll bvxs (bp ==> pA)) === (subb pA T)

lExBoolEqv1  = (mkAny bvxs (bp === pA)) === (subb pA T) \/ (Not (subb pA F))
lExBoolEqv2  = (mkAny bvxs (bp === pA)) === (Not (subb pA F)) \/ (subb pA T)

lAllBoolEqv1 = (mkAll bvxs (bp === pA)) === (subb pA T) /\ (Not (subb pA F))
lAllBoolEqv2 = (mkAll bvxs (bp === pA)) === (Not (subb pA F)) /\ (subb pA T)
\end{code}
We also want to handle the cases where the boolean is all that exists:
\begin{eqnarray*}
   (\exists b @ b) &\equiv& True
\\ (\forall b @ b) &\equiv& False
\end{eqnarray*}
\begin{code}
lExBool  = (mkAny bvxs bp)
lAllBool = (mkAll bvxs bp) === FALSE
\end{code}

We can also handle cases where the boolean is negated:
\begin{eqnarray*}
   (\exists b @ A \land \lnot b) &\equiv& A[False/b]
\\ (\forall b @ A \land \lnot b) &\equiv& False
\\ (\exists b @ A \lor \lnot b)  &\equiv& True
\\ (\forall b @ A \lor \lnot b)  &\equiv& A[True/b]
\\ (\exists b @ A \implies \lnot b) &\equiv& True
\\ (\forall b @ A \implies \lnot b) &\equiv& \lnot A[True/b]
\\ (\exists b @ \lnot b \implies A) &\equiv& True
\\ (\forall b @ \lnot b \implies A) &\equiv& A[False/b]
\\ (\exists b @ \lnot b \equiv A) &\equiv& A[False/b] \lor \lnot A[True/b]
\\ (\forall b @ \lnot b \equiv A) &\equiv& A[False/b] \land \lnot A[True/b]
\end{eqnarray*}
\begin{code}
lExNBoolAnd1  = (mkAny bvxs (nbp /\ pA))  === (mkAny qxs (subb pA F))
lExNBoolAnd2  = (mkAny bvxs (pA /\ nbp))  === (mkAny qxs (subb pA F))

lAllNBoolAnd1 = (mkAll bvxs (nbp /\ pA))  === FALSE
lAllNBoolAnd2 = (mkAll bvxs (pA /\ nbp))  === FALSE

lExNBoolOr1   = (mkAny bvxs (nbp \/ pA))  === TRUE
lExNBoolOr2   = (mkAny bvxs (pA \/ nbp))  === TRUE

lAllNBoolOr1  = (mkAll bvxs (nbp \/ pA))  === (subb pA T)
lAllNBoolOr2  = (mkAll bvxs (pA \/ nbp))  === (subb pA T)

lExNBoolPmi   = (mkAny bvxs (pA ==> nbp)) === TRUE
lAllNBoolPmi  = (mkAll bvxs (pA ==> nbp)) === Not (subb pA T)
lExNBoolImp   = (mkAny bvxs (nbp ==> pA)) === TRUE
lAllNBoolImp  = (mkAll bvxs (nbp ==> pA)) === (subb pA F)

lExNBoolEqv1  = (mkAny bvxs (nbp === pA)) === (subb pA F) \/ (Not (subb pA T))
lExNBoolEqv2  = (mkAny bvxs (nbp === pA)) === (Not (subb pA T)) \/ (subb pA F)

lAllNBoolEqv1 = (mkAll bvxs (nbp === pA)) === (subb pA F) /\ (Not (subb pA T))
lAllNBoolEqv2 = (mkAll bvxs (nbp === pA)) === (Not (subb pA T)) /\ (subb pA F)
\end{code}
and when the boolean is all we have got:
\begin{eqnarray*}
   (\exists b @ \lnot b) &\equiv& True
\\ (\forall b @ \lnot b) &\equiv& False
\end{eqnarray*}
\begin{code}
lExNBool  = (mkAny bvxs nbp)
lAllNBool = (mkAll bvxs nbp) === FALSE
\end{code}

Putting it all together:
\begin{code}
laws_boolvar
 =   freeLogicLaw "exist-bv" lExBool
 ~:~ freeLogicLaw "exist-nbv" lExNBool
 ~:~ freeLogicLaw "forall-bv" lAllBool
 ~:~ freeLogicLaw "forall-nbv" lAllNBool
 ~:~ freeLogicLaw "exists-bv-/\\.2" lExBoolAnd2
 ~:~ freeLogicLaw "forall-bv-/\\.1" lAllBoolAnd1
 ~:~ freeLogicLaw "forall-bv-/\\.2" lAllBoolAnd2
 ~:~ freeLogicLaw "exists-bv-\\/.1" lExBoolOr1
 ~:~ freeLogicLaw "exists-bv-\\/.2" lExBoolOr2
 ~:~ freeLogicLaw "forall-bv-\\/.1" lAllBoolOr1
 ~:~ freeLogicLaw "forall-bv-\\/.2" lAllBoolOr2
 ~:~ freeLogicLaw "exists-bv-<==" lExBoolPmi
 ~:~ freeLogicLaw "forall-bv-<==" lAllBoolPmi
 ~:~ freeLogicLaw "exists-bv-==>" lExBoolImp
 ~:~ freeLogicLaw "forall-bv-==>" lAllBoolImp
 ~:~ freeLogicLaw "exists-bv-===.1" lExBoolEqv1
 ~:~ freeLogicLaw "exists-bv-===.2" lExBoolEqv2
 ~:~ freeLogicLaw "forall-bv-===.1" lAllBoolEqv1
 ~:~ freeLogicLaw "forall-bv-===.2" lAllBoolEqv2
 ~:~ freeLogicLaw "exists-nbv-/\\.1" lExNBoolAnd1
 ~:~ freeLogicLaw "exists-nbv-/\\.2" lExNBoolAnd2
 ~:~ freeLogicLaw "forall-nbv-/\\.1" lAllNBoolAnd1
 ~:~ freeLogicLaw "forall-nbv-/\\.2" lAllNBoolAnd2
 ~:~ freeLogicLaw "exists-nbv-\\/.1" lExNBoolOr1
 ~:~ freeLogicLaw "exists-nbv-\\/.2" lExNBoolOr2
 ~:~ freeLogicLaw "forall-nbv-\\/.1" lAllNBoolOr1
 ~:~ freeLogicLaw "forall-nbv-\\/.2" lAllNBoolOr2
 ~:~ freeLogicLaw "exists-nbv-<==" lExNBoolPmi
 ~:~ freeLogicLaw "forall-nbv-<==" lAllNBoolPmi
 ~:~ freeLogicLaw "exists-nbv-==>" lExNBoolImp
 ~:~ freeLogicLaw "forall-nbv-==>" lAllNBoolImp
 ~:~ freeLogicLaw "exists-nbv-===.1" lExNBoolEqv1
 ~:~ freeLogicLaw "exists-nbv-===.2" lExNBoolEqv2
 ~:~ freeLogicLaw "forall-nbv-===.1" lAllNBoolEqv1
 ~:~ freeLogicLaw "forall-nbv-===.2" lAllNBoolEqv2

conj_boolvar
 =   freeConj "exist-bv" lExBool
 : freeConj "exist-nbv" lExNBool
 : freeConj "forall-bv" lAllBool
 : freeConj "forall-nbv" lAllNBool
 : freeConj "exists-bv-/\\.2" lExBoolAnd2
 : freeConj "forall-bv-/\\.1" lAllBoolAnd1
 : freeConj "forall-bv-/\\.2" lAllBoolAnd2
 : freeConj "exists-bv-\\/.1" lExBoolOr1
 : freeConj "exists-bv-\\/.2" lExBoolOr2
 : freeConj "forall-bv-\\/.1" lAllBoolOr1
 : freeConj "forall-bv-\\/.2" lAllBoolOr2
 : freeConj "exists-bv-<==" lExBoolPmi
 : freeConj "forall-bv-<==" lAllBoolPmi
 : freeConj "exists-bv-==>" lExBoolImp
 : freeConj "forall-bv-==>" lAllBoolImp
 : freeConj "exists-bv-===.1" lExBoolEqv1
 : freeConj "exists-bv-===.2" lExBoolEqv2
 : freeConj "forall-bv-===.1" lAllBoolEqv1
 : freeConj "forall-bv-===.2" lAllBoolEqv2
 : freeConj "exists-nbv-/\\.1" lExNBoolAnd1
 : freeConj "exists-nbv-/\\.2" lExNBoolAnd2
 : freeConj "forall-nbv-/\\.1" lAllNBoolAnd1
 : freeConj "forall-nbv-/\\.2" lAllNBoolAnd2
 : freeConj "exists-nbv-\\/.1" lExNBoolOr1
 : freeConj "exists-nbv-\\/.2" lExNBoolOr2
 : freeConj "forall-nbv-\\/.1" lAllNBoolOr1
 : freeConj "forall-nbv-\\/.2" lAllNBoolOr2
 : freeConj "exists-nbv-<==" lExNBoolPmi
 : freeConj "forall-nbv-<==" lAllNBoolPmi
 : freeConj "exists-nbv-==>" lExNBoolImp
 : freeConj "forall-nbv-==>" lAllNBoolImp
 : freeConj "exists-nbv-===.1" lExNBoolEqv1
 : freeConj "exists-nbv-===.2" lExNBoolEqv2
 : freeConj "forall-nbv-===.1" lAllNBoolEqv1
 : freeConj "forall-nbv-===.2" lAllNBoolEqv2
 : []
\end{code}

\subsection{And the Law is \ldots}

\begin{code}

logicLawTable
  = laws_2_1
  ~:~ laws_2_2
  ~:~ laws_2_3
  ~:~ laws_2_4
  ~:~ laws_3
  ~:~ laws_4_3
  ~:~ laws_4_4
  ~:~ laws_4_5
  ~:~ laws_4_6
  ~:~ laws_4_7
  ~:~ laws_boolvar

logicConjectures
  = conj_2_1
  ++ conj_2_2
  ++ conj_2_3
  ++ conj_2_4
  ++ conj_3
  ++ conj_4_3
  ++ conj_4_4
  ++ conj_4_5
  ++ conj_4_6
  ++ conj_4_7
  ++ conj_boolvar

logicProofContext
 = markTheoryDeps ((nmdNullPrfCtxt "Logic")
                     { syntaxDeps = [ rootName ]
                     , types = boolOpTypes
                     , laws = logicLawTable
                     })
logicLawsTheory
 = markTheoryDeps ((nmdNullPrfCtxt "LogicLaws")
                     { syntaxDeps = [ rootName ]
                     , types = boolOpTypes
                     , laws = freeLogicLaw "DEF-<||>.1" lCondDef1 
                     , conjectures = lbuild logicConjectures
                     })
\end{code}
Now some testers:
\begin{code}

alphaTest1 -- forall x @ x = 3 /\ exists x @ x /\ TRUE
 = Forall 0 qx
    (And [ Obs (Equal ex (Num 3))
         , Exists 0 qx (And [ Obs ex
                                  , TRUE
                                  ])
         ])
 where ex = Var vx

alphaTest2 -- x /\ forall x @ x = 3 /\ exists x @ x
 = And [ Obs ex
       , Forall 0 qx
                (And [ Obs (Equal ex (Num 3))
                     , Exists 0 qx (Obs ex)
                     ])
       ]
 where ex = Var vx

typeTest1 = Obs (Equal (Var vx) (Var vy))
\end{code}
