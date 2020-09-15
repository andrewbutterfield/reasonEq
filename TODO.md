# To Do

## Most Urgent

### Quantifier Bound Variables (in Matches)

The following match should not be displayed,
as the side-condition cannot be discharged.

```
1 : “∃_remove”  gives  b∧P∨¬ b∧R★  b∧Q∨¬ b∧S  _ 
     ⟹ Ø ⊇ P;Ø ⊇ Q;Ø ⊇ R;Ø ⊇ S;Ø ⊇ b ≡[1]
```
This is because all variables, including `b`, denote arbitrary *terms*, which are not guaranteed to be closed.

If all of these variables were "questionable":

```
1 : “∃_remove”  gives  ?b∧?P∨¬ ?b∧?R★  ?b∧?Q∨¬ ?b∧?S  _ 
     ⟹ Ø ⊇ ?P;Ø ⊇ ?Q;Ø ⊇ ?R;Ø ⊇ ?S;Ø ⊇ ?b ≡[1]
```
then we should display the match because we could instantiate them
with closed terms. 

We need to reject residual side-conditions that contain any regular term-variables.

## Upgrade No. 2

For `;` we may want to specify fresh subscripts.
**Yes - we need to allow fresh subscript instantiation
and we need a freshness side-condition for the definition of seq-comp `;`**

## Upgrade No. 3

For simultaneous assignment we need to be able to represent
things like

`x,y$ :=  x+1,y$`

This may require `Var` to contain `GenVar` rather than `Variable`.

## Upgrade No. 4

Need to re-design `TestRendering` so we can have meaningful 
official names (`or`,`refines`) 
that map to nice symbols (`∨`,`⊒`),
rather than be called by their LaTeX names (`lor`,`sqsupseteq`).

### Phase 1.
  Hardcoded Mapping tables
  
### Phase 2.
  Mapping tables part of `REqState`,
  and hence loadable, saveable, and editable.

## Upgrade No. 5

We have an ongoing proof of Ex2.1.2 above, but it requires
a case-analysis.

The rule is, provided that `b:B`,

```
(∀ b • P)  ≡  P[true/b] ∧ P[false/b]
```

What is the best formulation of this rule?

```
 b:B ⟹ ( (∀ b • P)  ≡  P[true/b] ∧ P[false/b] )
```

or

```
(∀ b • P)  ≡  P[true/b] ∧ P[false/b],   b:B
```

or

```
(∀ b:B • P)  ≡  P[true/b] ∧ P[false/b]
```

This needs types!

## Robustness

Working on startup robustness

### Theory Management

In priority order:

1. Load a theory "update".
   This involves adding in new axioms and conjectures,
   but not overwriting the status of existing laws and conjectures,
   unless they have been changed.

2. Load a theory file from outside the workspace

3. Create and Populate a workspace.


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
  