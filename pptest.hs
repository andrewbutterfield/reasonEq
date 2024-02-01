@tvM.vts:
[ VD
  ( { ( VR (Id "#" 0, VE, WS)
      , KV (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TG (Id "Z" 0))))
    , ( VR (Id "\\" 0, VE, WS)
      , KV (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TC (Id "powerset" 0) [TV (Id "t" 0)]))))
    , (VR (Id "emptyset" 0, VE, WS)
      , KV (TC (Id "powerset" 0) [TV (Id "t" 0)]))
    , (VR (Id "in" 0, VE, WS), KV (TF (TV (Id "t" 0)) (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TG (Id "B" 0)))))
    , (VR (Id "intsct" 0, VE, WS), KV (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TC (Id "powerset" 0) [TV (Id "t" 0)]))))
    , (VR (Id "subseteq" 0, VE, WS), KV (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TG (Id "B" 0)))))
    , (VR (Id "union" 0, VE, WS), KV (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TF (TC (Id "powerset" 0) [TV (Id "t" 0)]) (TC (Id "powerset" 0) [TV (Id "t" 0)])))) }
  , {}
  , {} )
, VD
  ( {}
  , {}
  , {} )
, VD
  ( { (VR (Id "=" 0, VP, WS), KV (TF (TG (Id "B" 0)) (TF (TG (Id "B" 0)) (TG (Id "B" 0))))) }
  , {}
  , {} )
, VD
  ( { (VR (Id "imp" 0, VP, WS), KV (TF (TG (Id "B" 0)) (TF (TG (Id "B" 0)) (TG (Id "B" 0))))) }
  , {}
  , {} )
, VD
  ( {}
  , {}
  , {} )
, VD
  ( { (VR (Id "and" 0, VP, WS), KV (TF (TG (Id "B" 0)) (TF (TG (Id "B" 0)) (TG (Id "B" 0))))) }
  , {}
  , {} )
, VD
  ( { (VR (Id "or" 0, VP, WS), KV (TF (TG (Id "B" 0)) (TF (TG (Id "B" 0)) (TG (Id "B" 0))))) }
  , {}
  , {} )
, VD
  ( { (VR (Id "not" 0, VP, WS), KV (TF (TG (Id "B" 0)) (TG (Id "B" 0)))) }
  , {}
  , {} )
, VD
  ( { (VR (Id "eqv" 0, VP, WS), KV (TF (TG (Id "B" 0)) (TF (TG (Id "B" 0)) (TG (Id "B" 0))))) }
  , {}
  , {} ) ]
@tvM.vP:
VR (Id "emptyset" 0, VO, WS)
@tvM.vPmr:
UV
