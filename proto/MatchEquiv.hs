{- =============================================================================
 Exploring how to match an equivalence candidate against an equivalence pattern
-}
module MatchEquiv where

{- Unflattening equivalences

 Given a flat equivalence chain  Q1 == Q2 == ... == Qj == Qk,
 we often want to group some of them.

 There are a number of scenarios:

 Left associate all:   ((..(Q1 == Q2) == ..) == Qj) == Qk
 Right associate all:  Q1 == (Q2 == (.. == (Qj == Qk)..))
 Group 1st n:          (Q1 == .. ==   Qn) ==  Qn'   == .. == Qk
 Group last n:          Q1 == .. == Qk-n  == (Qk-n' == .. == Qk)
 Split n :             (Q1 == .. ==   Qn) ==  (Qn'   == .. == Qk)
-}

data P a = A a | E [P a] deriving (Eq,Show)

mkE :: [P a] -> P a
mkE []   =  E []
mkE [p]  =  p
mkE ps   =  E ps

a1,a2,a3,a4,a5,a6 :: P Int
[a1,a2,a3,a4,a5,a6] = map A [1..6]

lassoc :: P a -> P a
lassoc (E [a])            =  a
lassoc (E (a1:a2:arest))  =  lassoc $ E ((E [a1,a2]):arest)
lassoc p                  =  p

rassoc :: P a -> P a
rassoc (E [a]) = a
rassoc (E (a1:arest@(_:_))) = E [a1,rassoc $ E arest]
rassoc p = p

firstn :: Int -> P a -> P a
firstn n e@(E ps)
 | null before || null after  =  e
 | otherwise                  =  E ((mkE before):after)
 where (before,after) = splitAt n ps
firstn n p = p

lastn :: Int -> P a -> P a
lastn n e@(E ps)
 | null erofeb || null retfa  =  e
 | otherwise                  =  E (reverse erofeb ++ [mkE $ reverse retfa])
 where (retfa,erofeb) = splitAt n $ reverse ps
lastn n p = p

splitn :: Int -> P a -> P a
splitn n e@(E ps)
 | null before || null after  =  e
 | otherwise                  =  E [mkE before, mkE after]
 where (before,after) = splitAt n ps
splitn n p = p

{- We abstract the problem of matching:

  C1 == C2 == ... == Cm  ::  P1 == P2 == ... == Pn, for m,n > 1

 by assuming that Ci,Pj : T,
 and we have an abstract matcher m : T x T -> Bool

 We also assume that none of the Ci or Pj are themselves equivalences

 This means that m <= n.
-}

{- One-on-one matching:

 The idea is that we match each Ci against each Pj,
 recording the successes.
 In general we expect the 'matches' relation to be many-many

 From this we construct possible outcomes that satisfy
 the following constraints:

 1. Each Ci matches precisely one Pj and v.v. (so m <= n)
 2. Each Pj in 1 above is matched by one Ci

 In other words, extract out a one-to-one subrelation involving all the Ci.
-}
