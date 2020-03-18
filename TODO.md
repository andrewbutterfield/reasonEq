# To Do

### Laws

We hard-coded substitution, and now we have to hard-code quantifier scope support

Examples: 

 * `(∀ x̅ • (∀ x̅ • P)),  x̅ ⊇ P` to `(∀ x̅ • P),  x̅ ⊇ P`
 * `(∀ y̅ • (∀ x̅ • P)),  x̅ ⊇ P;y̅ ⊇ P` to `(∀ x̅ • P),  x̅ ⊇ P`
 * `(∀ x̅ • (∀ y̅ • P)),  y̅ ⊇ x̅` to `(∀ y̅ • P)` 
 * `(∀ x̅ • P),  x̅ ∉ P` to `P`


## Robustness

### Robust Load
Need to make file loading robust - no runtime failure.

* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

### Testing

`Substitution.lhs` looks like a good candidate for QuickCheck !

Example:  *(P\s1)s2 = P(s1;s2)* (a.k.a. `substitute` and `substComp`).

### Theory Checks

Need a way to check a theory (in context, with all its dependencies)

* all Cons have a substitutability indication in scope.

## Ongoing Issues

### Backing out of a proof step

If we use "b" after a proof step that is not reversible (just Clone?), we leave the goal unchanged,
but shorten the list of steps anyway. See `LiveProofs.undoCalcStep` (line 810 approx)

### Unique quantified variables

**(Unsure about this)**

We need to either have unique q.v.s, or be very careful. Consider matching `[∀ x$ @ P]`  against `[P]` (part 1 of `[]_def`). How do we distinguish this `x$` from the one in the law?

Need care here - in the conjecture
 `(∃ x̅,y̅ • ∧(x̅=e̅)∧P)≡(∃ y̅ • P[e̅/x̅])  x̅ ∉ e̅` 
we need `x̅` and `y̅` to be the same.

What we want to avoid is "shadowing", 
so that `(∀ x̅ • P ∨ (∀ x̅ • Q)`
becomes `(∀ x̅ • P ∨ (∀ y̅ • Q[y̅/x̅])`. **Why?**

## Next Task(s)


 
* LiveProof returns `(bind,local_scC)` - need to get `local_scC` into proof step.




## Quantifier Laws in proofs

## Theory Management

* law renaming

* Generating proof graph as dot/graphviz file.
 