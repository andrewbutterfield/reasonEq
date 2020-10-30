# reasonEq Matching Flow

Call sequences associated with prover matching commands

## Command `m` (Match all)

`matchFocus`

```
AbstractUI.matchFocus theSig liveProof
  LiveProofs.matchInContexts theSig ctxts (goalt,scC)
    LiveProofs.matchLaws logicsig asn mc
      LiveProofs.domatch logicsig vts asn lw
```

## Command `m name` (Match Law "name")

`matchFocusAgainst`

```
AbstractUI.matchFocusAgainst lawnm theSig liveProof
  LiveProofs.matchLawByName theSig (goalt,scC) lawnm ctxts
    LiveProofs.domatch logicsig vts asn law
```

## Internal Functions doing matches

### `doMatch`

```
LiveProofs.domatch logicsig vts asnC law
  LiveProofs.basicMatch MatchAll vts law (theTrue logicsig) asnC tP
  LiveProofs.doPartialMatch i logicsig vts law asnC tsP
    LiveProofs.doEqvMatch logicsig vts law asnC tsP
      LiveProofs.doEqvMatchC logicsig vts law asnC tsP
        LiveProofs.doEqvMatchC' cLen [1..cLen]             logicsig vts law scC          tsC           tsP       
        LiveProofs.doEqvMatchC' cLen [pLen+1-cLen .. pLen] logicsig vts law scC (reverse tsC) (reverse tsP)
          LiveProofs.basicMatch (MatchEqv is) vts law (eqv tsP'') (eqv tsC,scC) (eqv tsP')
      LiveProofs.doEqvMatchB logicsig vts law asnC [] [] tsP
        LiveProofs.basicMatch (MatchEqv [length sPt + 1]) vts law (eqv (reverse sPt ++ tPs)) asnC tP
        LiveProofs.doEqvMatchB logicsig vts law asnC (mtchs'++mtchs) (tP:sPt) tPs
    LiveProofs.basicMatch MatchAnte vts law (Cons P land [ltP,rtP]) asnC ltP
    LiveProofs.basicMatch MatchCnsq vts law (Cons P lor  [rtP,ltP]) asnC rtP
```

### `basicMatch`

```
LiveProofs.basicMatch mc vts law@((n,asn@(tP,scP)),_) repl asnC@(tC,scC) partsP
  match vts tC partsP
  autoInstantiate bind repl
  instantiateSC bind' scP
  scDischarge scC scPinC
  all isFloatingASC (fst scD)
```

## Command `tm name` (Test-Match Law "name")

`tryFocusAgainst`

```
AbstractUI.tryFocusAgainst lawnm parts theSig liveProof
  LiveProofs.tryLawByName theSig (goalt,scC) lawnm parts ctxts
    Match.match vts tC partsP
    Instantiate.autoInstantiate bind tP
    Instantiate.instantiateSC bind scP
    SideCond.scDischarge scC scP'
```


