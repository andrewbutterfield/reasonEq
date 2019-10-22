# To Do

## Hotfixes

### `PredUniv` Proofs

Need to reach stage where proofs work.

Proof of `[]_idem` stalls on `(∀ x̅ • (∀ x̅ • P))`.

Proof of `land_[]_distr` stalls on `(∀ x̅ • P)∧(∀ x̅ • Q)    x̅ ⊇ P;x̅ ⊇ Q`.

And etc....

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

 
* LiveProof returns `(bind,local_scC)` - need to get `local_scC` into proof step.


* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

## Quantifier Laws in proofs

## Theory Management

* law renaming

* Generating proof graph as dot/graphviz file.
