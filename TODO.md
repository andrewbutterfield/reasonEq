# To Do

## Hotfixes

### Substitiution matching bug.

From MatchScenarios we now have the following test outcome, and "expected" is wrong (missing `e -> Om`)

```
      [Om/O] :: [e$/x$] - succeeds: [Failed]

expected:   { e -> Om, x -> O,  (x,e) -> (O,Om) }
[BD (fromList []
    ,fromList []
    ,fromList [ ( (Id "e",VE,[],[])
                , BS (fromList [GL (LV (VR (Id "O",VO,WD "m"),[],[]))])
                )
              , ( (Id "x",VO,[],[])
                , BS (fromList [GL (LV (VR (Id "O",VO,WB),[],[]))])
                )
              ]
    ,fromList [ ( (LV (VR (Id "x",VO,WS),[],[]),LV (VR (Id "e",VE,WS),[],[]))
                , (fromList []
                  ,fromList [(LV (VR (Id "O",VO,WB),[],[]),LV (VR (Id "O",VO,WD "m"),[],[]))])
                )
              ]
    )
]

 but got:  { x -> O,  (x,e) -> (O,Om)}

[BD (fromList []
    ,fromList []
    ,fromList [ ( (Id "x",VO,[],[])
                , BS (fromList [GL (LV (VR (Id "O",VO,WB),[],[]))])
                )
              ]
    ,fromList [ ( (LV (VR (Id "x",VO,WS),[],[]),LV (VR (Id "e",VE,WS),[],[]))
                , (fromList []
                  ,fromList [(LV (VR (Id "O",VO,WB),[],[]),LV (VR (Id "O",VO,WD "m"),[],[]))]
                  )
                )
              ]
    )
]

```

#### Key Question

Should we actually produce `{ x -> O,  e -> 0m, (x,e) -> (O,Om) }` ?

*YES!* This is similar to what we do with `x -> u` inducing `x' -> u'`,
or `x_m -> u_n` inducing `m -> n`. It is **necessary** to ensure mapping consistency.

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
