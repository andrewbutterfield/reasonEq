# reasonEq Matching Flow

Call sequences associated with prover matching commands

## Command `m` (Match all)

`matchFocus`

```
AbstractUI.matchFocus theSig liveProof
  matchInContexts theSig ctxts (goalt,scC)
```

## Command `m name` (Match Law "name")

`matchFocusAgainst`

```
AbstractUI.matchFocusAgainst lawnm theSig liveProof
  matchLawByName theSig (goalt,scC) lawnm ctxts
```

## Command `tm name` (Test-Match Law "name")

`tryFocusAgainst`

```
AbstractUI.tryFocusAgainst lawnm parts theSig liveProof
  LiveProofs.tryLawByName theSig (goalt,scC) lawnm parts ctxts
  tryLawByName logicsig asn@(tC,scC) lnm parts mcs
    Match.match vts tC partsP
    Instantiate.autoInstantiate bind tP
    Instantiate.instantiateSC bind scP
    SideCond.scDischarge scC scP'
```


