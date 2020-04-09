# To Do


## Features

### Quantifier Bound Variables (in Laws)

Key decisions regarding the uniqueness or otherwise of quantifier bound variables: 

1. do not routinely use `normaliseQuantifier` - it can be invoked as a proof step.
2. Given something like `b ∧ (∀ b @ b ∧ (∀ b @ b))` we do require a single match binding all those `b`s to the same variable/term. If we want otherwise, we should alpha-rename some quantifiers first (`normaliseQuantifier` does them all systematically).
3. Consider matching `[∀ x$ @ P]`  against `[P]` (part 1 of `[]_def`). How do we distinguish this `x$` from the one in the law?
  * `[]_def` says `[P] = ∀ x$ @ P` where `x$` covers `fv.P`, so `[∀ x$ @ P] = ∀ y$ @ ∀ x$ @ P` where `y$` covers `fv(∀ x$ @ P)`, which is `fv.P \ x$`.
  * Another way to interpret this law is as `[P] = ∀ fv.P @ P`, so `[∀ x$ @ P]` becomes `∀ fv(∀ x$ @ P) @ (∀ x$ @ P)`, which reduces to `∀ (fv.P\x$) @ (∀ x$ @ P)`.
  * We need either a special side-condition that introduces a fresh list-variable ("new `x$` s.t. `x$` covers `fv.P`"),or a way to recognise when to interpret a standard side-condition ("`x$` covers `fv.P`") in this way.

  
### Test Re-jigging

Trying to have common data and function definitions for testing. Non-trivial.

Want to support local (internal) tests within any module that does not export
all data-structure details, with some hidden by invariant-checking constructor functions.
Want lots of shorthand (partial) builders for test data for these data-structures.

To avoid cyclic module imports, we need to export shorthands from non-test modules.
Testing modules need to import the modules they test.

## Robustness

### Demote

 Demote can demote an axiom - it should really warn about that, or require a special argument to force it.

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


We need to either have unique q.v.s, or be very careful. 



## Next Task(s)


 
* LiveProof returns `(bind,local_scC)` - need to get `local_scC` into proof step.




## Quantifier Laws in proofs

## Theory Management

* law renaming

* Generating proof graph as dot/graphviz file.
 