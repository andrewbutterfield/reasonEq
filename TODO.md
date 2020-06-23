# To Do

## Robustness

Working on startup robustness

### Theory Management

Need commands to load a theory file.

Need commands to create and populate a workspace.

Need commands to load a theory "update".
This involves adding in new axioms and conjectures,
but not overwriting the status of existing laws and conjectures,
unless they have been changed.
In the event that a pre-existing item has changed,
confirmation for the update should be requested from the user
(a force option can also be provided).


### Files.lhs

Current focus: `Files.lhs` - needs a re-think.

`getWorkspaces` should check that it has a non-empty list of workspaces,
and return them parsed into current-flag, name and path triples.

`currentWorkspace` needs to become two different things.

One loads up the current workspace, if it exists.

Another creates and initialises a workspace.

## Features

### Substitution Handling


Added Conjecture `[P] => P[e̅/x̅]` to `UClose` and proven.


### Quantifier Bound Variables (in Laws)

The following match should not be displayed,
as the side-condition cannot be discharged.

`1 : “∃_remove”  gives  Q  _ ⟹ Ø ⊇ Q ≡[1]`.


We need to attempt to discharge these at the match stage
to prevent these spurious un-dischargeable matches being presented
to the user.
We have to admit coverage for empty set in undischarged atomic s.c.s. (`autoOrNullInAll`)
However we need another criterie to check that all (unbound) variables in discharged s.c. involve general variables found in goal s.c.s
So above should outlaws because `Q` does not occur in `_`.
(even this isn't enough - we may want a more powerful check
for *unsatisfiability* in s.c.s)

  
### Test Re-jigging

Trying to have common data and function definitions for testing. Non-trivial.

Want to support local (internal) tests within any module that does not export
all data-structure details, with some hidden by invariant-checking constructor functions.
Want lots of shorthand (partial) builders for test data for these data-structures.

To avoid cyclic module imports, we need to export shorthands from non-test modules.
Testing modules need to import the modules they test.


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
 