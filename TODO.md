# To Do


## Quantification

 
Need three builtin facilities:

1. *alpha*-renaming
2. Substitution into quantifiers
3. Simplifying nested quantifiers

Problem cases

* `(exists x,x' @ x := e)[y,y'/x,x']`  -- how does a builtin *alpha*-renaming know to stop?  
We should get `exists y,y' @ (x:=e)[y,y'/x,x']` and leave it until the assignment is replaced by its definition.

We cannot reply on explicit substitution laws alone. We need to flag `Cons` as substitutable/non-substitutable.
This needs to be done by maintaining a table that matches identifiers
to substitutability.
It cannot be embedded in the term, because how do we handle term parsing? We don't want explicit substitutability annotations. 

### `a n` command in proof REPL

When instantiating unbound variables we have two cases:

1. We have a `StdVar`, which binds to a term. 
   We allow a default option of binding to `true`.
2. We have a `LstVar`, which binds to a variable-set.
   We allow a default option of binding to `{}`.
   
Defaults are specifed by hitting enter with no selection data.

### Instantiating Side-Conditions

`instantiateASC` is just wrong - it's acting more like discharge should.
Also, `Disjoint` and `IsPre` distribute conjunctively through set union (of sets formed when `vs` and `gv` get instantiated)
However, assume we have `Covers x$ P` where `x$` is mapped to `{a,b,c$}` and `P` to `Q /\ x=1 \/ R` (say).
This cannot be broken down into a conjuction of conditions relating
each of `a`, `b`, and `c$` individually to each of `Q`, `{x}`,
and `R`, also taken individually.
Instead we have to assert that `{a,b} U c$` covers `Q U {x} U R`.

### Backing out of a proof step

If we use "b" after a proof step that is not reversible (just Clone?), we leave the goal unchanged,
but shorten the list of steps anyway. See `LiveProofs.undoCalcStep` (line 810 approx)

### Unique quantified variables

We need to either have unique q.v.s, or be very careful. Consider matching `[∀ x$ @ P]`  against `[P]` (part 1 of `[]_def`). How do we distinguish this `x$` from the one in the law?

Need care here - in the conjecture
 `(∃ x̅,y̅ • ∧(x̅=e̅)∧P)≡(∃ y̅ • P[e̅/x̅])  x̅ ∉ e̅` 
we need `x̅` and `y̅` to be the same.

What we want to avoid is "shadowing", 
so that `(∀ x̅ • P ∨ (∀ x̅ • Q)`
becomes `(∀ x̅ • P ∨ (∀ y̅ • Q[y̅/x̅])`.

## Next Task(s)


 
* LiveProof returns `(bind,local_scC)` - need to get `local_scC` into proof step.


* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

## Quantifier Laws in proofs

## Theory Management

* law renaming

* Generating proof graph as dot/graphviz file.
