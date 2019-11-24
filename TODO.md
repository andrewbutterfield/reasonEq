# To Do

## HOTFIX

addToEquiv class: extract *hasX*, *hasY*, *noXY*;
construct *eqvXY = {x,y} union hasX and hasY*;
return *noXY union {eqvXY}*.

### Match Crash

Matching *forall xs . true* crashes in proof of *"exists_false"*.

Issue is in `autoInstantiate`.

Problem identified:

Replacmement  *(forall xs,ys @ P) /\ (forall ys @ P[es/xs])*

Two matches bind *xs,ys* to *xs,{}* - this works fine.

One match binds *xs,ys* to *{},xs* - this fails becuase *es* is bound to *?es* so the substitution becomes [?es/{}].

**We need to guide list-var autoinstantiation by substitutions.**

## Top-Level Plan

We need to refactor all theories:

* XX_def move from PropAxioms or PredAxioms into XX theory with axioms and conjectures.
* XX_subst move in as axioms/conjectures into XX theory
* Theory starts with defining axioms with the last axioms being those that define substitutions, if allowed
* Theory conjectures start with substitution conjectures, if any, and then the rest.

**NEED SIDECONDITIONS OF THE FORM `x$ disj z$` !!!**

*Can be done as  `[x$] notin z$`  or `[z$] notin x$`.*


## Current Task

none


## Hotfixes


### `[]_idem` Proof

Need `PredSubst` axioms !!!

STOP PRESS ! Reading [Gries 97] gives a new perspective for `PredUniv` axioms.

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
