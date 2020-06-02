# To Do


## Features

### Quantifier Bound Variables (in Laws)


The following match should not be displayed,
as the side-condition cannot be discharged.

`1 : “∃_remove”  gives  P[e̅/x̅]  x̅ ∉ e̅ ⟹ Ø ⊇ P ≡[1]`.

When this match is applied, we get the message

```
Cannot discharge side-condition
checkUnboundInvolved: fails
```

We need to attempt to discharge these at the match stage
to prevent these spurious un-dischargeable matches being presented
to the user.
We can only do this where all parts (`x̅`,`P`) are in the binding.


Law `[P] => P` may need to generalise to `[P] => P[e̅/x̅]`,
or we add a facility to add an identity substitution, 
so `P` becomes `P[x̅/x̅]`.
  
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
 