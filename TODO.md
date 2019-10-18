# To Do

## Hotfixes

### Substitiution matching bug.

Current state (`test.log`, 18 Oct 2019)

```
@*MatchScenarios> bindLl gO [gok,gS] emptyBinding
BD      { O$ |-> <ok,S$> } -- correct
( {}
, {}
, { ( (Id "O", VO, [], [])
    , BL
      [ GV (VR (Id "ok", VO, WB))
      , GL (LV (VR (Id "S", VO, WB), [], [])) ] ) } )
@*MatchScenarios> bindLSR gOm [tokm] [lSm] emptyBinding
BD     { O$m |-> ( <okm> ; <Sm> )} -- correct
( {}
, { ( "m"
    , "m" ) }
, { ( (Id "O", VO, [], [])
    , BX
      [ V (E (TG (Id "\120121"))) (VR (Id "ok", VO, WD "m")) ]
      [ LV (VR (Id "S", VO, WD "m"), [], []) ] ) } )
@*MatchScenarios> bindLl gO [gok,gS] it
Nothing
```

Mapping O to [G,..] induces mappings of O' to [G',..] and Om to [Gm,..], but this is not the problem.

It's that we have a `O -> [vok,lvS]` as well as `O -> ([tok],[lvS])`

### Filenames

We need to decouple Cons names from external appearance.
If a theory file developed and saved on OS/unix
is opened by a Windows version, then the UTF-8 names will be present.
If done the other way around we see ASCII_art names.
NiceSymbols needs to export an ASCII to pretty-name dictionary.

### Instantiating Side-Conditions

`instantiateASC` is just wrong - it's acting more like discharge should.
Also, `Disjoint` and `IsPre` distribute conjunctively through set union (of sets formed when `vs` and `gv` get instantiated)
However, assume we have `Covers x$ P` where `x$` is mapped to `{a,b,c$}` and `P` to `Q /\ x=1 \/ R` (say).
This cannot be broken down into a conjuction of conditions relating
each of `a`, `b`, and `c$` individually to each of `Q`, `{x}`,
and `R`, also taken individually.
Instead we have to assert that `{a,b} U c$` covers `Q U {x} U R`.

### Unique quantified variables

We need to either have unique q.v.s, or be very careful. Consider matching `[∀ x$ @ P]`  against `[P]` (part 1 of `[]_def`). How do we distinguish this `x$` from the one in the law?


## Next Task(s)

* **Confusion Alert!** The use of "binding" for the outcome of matching gets confused with the notion of "binding" and "bound" associated with various quantifiers. Perhaps we should reconsider re-naming `Binding.Binding`, etc to `?.Mapping` ? or `MMapping` ? or `MMap` ?

 
* LiveProof returns `(bind,local_scC)` - need to get `local_scC` into proof step.


* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

## Quantifier Laws in proofs

## Theory Management

* law renaming

* Generating proof graph as dot/graphviz file.
