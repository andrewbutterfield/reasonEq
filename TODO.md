# To Do


## Most Urgent


### Side Conditions


**Note: both `Instantiate` and `Assertions` make use of functions that
extract variable sets from side-conditions but ignore uniformity information!**


Moving onto substitution:

```
(∃ O$_1 • (x'=e∧(O$'\x=O$\x))[O$_1/O$']∧((x := f))[O$_1/O$]), O$⊇e, O$⊇f, O$⊇x
   = 'substitute @[1,1]'
(∃ O$_1 • (x'=e[O$_1/O$']∧(O$'\x=O$\x))∧((x := f))[O$_1/O$])    O$⊇e, O$⊇f, O$⊇x
```


The issue is that `(x'=e∧(O$'\x=O$\x))[O$_1/O$']` should become `x_1=e∧(O$_1\x=O$\x)`, and not `(x'=e[O$_1/O$']∧(O$'\x=O$\x))`!

It looks like that we may need to pass in `VarTable`s

We also need to involve side-conditions!
We have `O$⊇e,f,x`, which also implies that `O$'⊇e',f',x'`.
The substitution proceeds as follows:

```
    ( x' = e ∧ O$'\x = O$\x )[O$_1/O$']
= distr subst. in
    x'[O$_1/O$'] = e[O$_1/O$'] ∧ O$'\x[O$_1/O$'] = O$\x[O$_1/O$'] 
=      O$'⊇x'        ¬(O$'⊇e)       O$'⊇O$'\x        ¬(O$'⊇O$\x)
        x_1      =     e       ∧     O$_1\x      =     O$\x
```


Side conditions plus known list variables raise a complication (ill-formed substitutions)
We prevent a target variable from being used more than once when we build substitutions,
but this doesnt cater for a condition like `O$⊇e`. 
In this context, the substitution `[3,O$_1/e,O$]` is illegal, because it asks `e` to be replaced by both `3` (directly) and `e_1` (implicitly, via membership of `O$`).
In effect, we need to use side-conditions like `O$⊇e` to assess the validity
of target-lists like `<e,O$>` (or `<e',O$'>` or `<e_1,O$_1>`!).

### Match Contexts

We need to review use of match-contexts at various levels
in the proof system.
In particular, extracting `VarTable`s from the top-level `mtchCntxt` component of a `LiveProof` by mapping `thd3` and then concatenating them is very inefficient: we should just take the head of the list instead.

### Complete UTPBase proofs

Doing this has shown that proof ranking and short-listing needs improvement.

* Allow `REqSet` settings to be changed  from *within* a proof
* We really need to have symmetric forms of key results, e.g., we have `P∨true≡true`, but should also have `true∨P≡true`.

We really need to able to tune things - using negation-involution to add a double-negation can be really useful.

We also need laws that express equivalence in terms of implication,
and hence in terms of and/or/invert.

The definition of ';' only works if predicates have alphabet O+O'

```
“;_def”     (P;Q)≡(∃ O$_0 • P[O$_0/O$']∧Q[O$_0/O$])  O$,O$' ⊇ P;O$,O$' ⊇ Q;fresh:O$_0
```

We need many posited laws to have the same side-conditions for many of its predicate variables: e.g. `P;(Q;R)≡(P;Q);R`.
This can clutter a lot of laws/conjectures.
Is there a way to have a 'locale' that asserts this about P, Q, R, ....?

**Extend side-conditions to refer to a set of common side-conditions by name?**
We would have a side-condition called `UTPBase [P,Q,R,...]` 
that is shorthand for `O$,O$' ⊇ P; O$,O$' ⊇ Q; O$,O$' ⊇ R;...`
But how would `Design [P..]` capture the idea that `O` contains `ok`?


## Upgrade No. 4

Need to re-design `TestRendering` so we can have meaningful 
official names (`or`,`refines`) 
that map to nice symbols (`∨`,`⊒`),
rather than be called by their LaTeX names (`lor`,`sqsupseteq`).

Need proof transcripts to show assumptions, when `assume` strategy is used.

### Phase 0.

Read [https://harry.garrood.me/blog/down-with-show-part-1/](https://harry.garrood.me/blog/down-with-show-part-1/) carefully!

Look at [https://github.com/ExtremaIS/ttc-haskell](https://github.com/ExtremaIS/ttc-haskell) also.

Introduce `NameRendering` module.

### Phase 1.

  Hardcoded Mapping tables
  
### Phase 2.
  Mapping tables part of `REqState`,
  and hence loadable, saveable, and editable.
  
### Phase 3.

 Add calibration facility.
 
 This would display unicode rendering with different amounts of before/after padding
 and allow the use to select their preferences, 
 which would be stored in the above-mentioned mapping tables
 
### Phase 4.

  Replace TestRendering by a principled system that uses mappings and which can be
  called from anywhere (i.e. distribute rendering to modules with the datatypes,
  or modules that just import that datatype).

## Upgrade No. 5

We have an ongoing proof of Ex2.1.2but it requires
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

## Upgrade No. 6

Need to find a way to change dependencies in a DAG.


## Robustness

### Issue 1
 
  There should be no runtime errors when starting up, regardless of the presence/absense or state of relevant files.

### Issue 2

If in one theory, if we restart a proof based in another theory, using `r`, we get the conjecture in the context of the first theory, and not that of the second. This should be fixed.



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
  