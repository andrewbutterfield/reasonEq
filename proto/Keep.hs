module Keep
where


data Feature = FV | TM | TL | TS deriving (Eq,Show)

type Match = [Feature]

decodeMatch :: Int -> Match
decodeMatch n = concat
  [ if n `div` 8             ==  1 then [FV] else []
  , if (n `div` 4) `mod`  2  ==  1 then [TM] else []
  , if (n `div` 2 ) `mod` 2  ==  1 then [TL] else []
  , if n `mod` 2             ==  1 then [TS] else [] ]

allmatches = map decodeMatch [0..15]


type Filter = Match -> Bool

filterFV, filterTM, filterTL, filterTS :: Filter
filterFV m = FV `elem` m
filterTM m = TM `elem` m
filterTL m = TL `elem` m
filterTS m = TS `elem` m

type Settings = (Bool,Bool,Bool,Bool)

decodeBool :: Int -> Settings
decodeBool n = ( n `div` 8            ==  0
               , (n `div` 4) `mod` 2  ==  0
               , (n `div` 2) `mod` 2  ==  0
               , n `mod` 2            ==  0 )

allsettings = map decodeBool [0..15]

type Keep =  Settings -> Match -> Bool
keep, keep2, keep3 :: Keep

keep (fv,tm,tl,ts) m
  | filterFV m && not fv = False
  | filterTM m && not tm = False
  | filterTL m && not tl = False
  | filterTS m && not ts = False
  | otherwise            = True

keep2 (fv,tm,tl,ts) m
  = not (   filterFV m && not fv
         || filterTM m && not tm
         || filterTL m && not tl
         || filterTS m && not ts )

keep3 (fv,tm,tl,ts) m
  =    not (filterFV m && not fv)
    && not (filterTM m && not tm)
    && not (filterTL m && not tl)
    && not (filterTS m && not ts )

type Diff = String

kcompare :: Keep -> Keep -> [[Diff]]
kcompare k1 k2 = map (mcomp k1 k2) allmatches

mcomp :: Keep -> Keep -> Match -> [Diff]
mcomp k1 k2 match = map (scomp k1 k2 match ) allsettings

scomp :: Keep -> Keep -> Match -> Settings -> Diff
scomp k1 k2 match setting
  =  markdiff (k1 setting match) (k2 setting match)

-- showdiff :: Settings -> Settings -> Diff
-- showdiff (fv1,tm1,tl1,ts1) (fv2,tm2,tl2,ts2)
--   = ( markdiff fv1 fv2
--     , markdiff tm1 tm2
--     , markdiff tl1 tl2
--     , markdiff ts1 ts2 )

markdiff :: Bool -> Bool -> String
markdiff b1 b2 = if b1 == b2 then " . " else "???"