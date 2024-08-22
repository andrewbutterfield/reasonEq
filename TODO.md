# To Do

## URGENT


We know we need to capture that E,R,N do not overlap with O$,O$'

`[gO,gO'] `notin` gE` says `O$,O$' ∉ E`, but we really want `E ∉ O$,O$'`,
but is meant to really mean `E ∉ fv(O$,O$')`.

Perhaps we interpret the "free-variables" of {O$,O$'} as fv(O$) ∪ fv(O$'),
which then becomes {s,ls,s',ls'} in the UTCP case?

We find that `mrgscs [eNotObs,nNotObs]` reduces to `O$,O$' ∉ N`.

Not sure about `SideCond.disjointCheck`.  Is `E`,`N` being `Static` an issue?

If we try to build `E ∉ O$` we get it. 
If we try to do `E ∉ O$ ; N ∉ O$` we get `scTrue` !

We want to 





```
E1[O$_1/O$'] ⊆ ls ∧ a[O$_1/O$']
O$,O$'⊇ₐa
```

Here, `E1` is a static expression variable denoting some set,
while `a` is a static predicate variable whose alphabet is `O$ ∪ O$'`.

**In fact, `E1` is a set whose elements are generated labels**,
which means that we have `in,g,out ⊇ E1`, 
and we know that `{in,out,g}` is disjoint from `O$ ∪ O$'`.


Here we should be able to say that `O$'` does NOT cover `E1`,
so we can obtain just `(E1 ⊆ ls)`, while the substitution on `a` needs to remain.

We have the following error:
```
∃ O$_1  • ((E1 ⊆ ls ∧ a) ∧ ls' = ls \ R1 ∪ N1)[O$_1/O$'] ∧ ...
   = 'substitute @[1,1]'
(∃ O$_1  • ((E1[O$_1/O$'] ⊆ ls ∧ a[O$_1/O$']) 
         ∧ ls' = ls \ R1[O$_1/O$'] ∪ N1[O$_1/O$']) ∧ ...
```

What didn't happen was that we should have had `ls'[O$_1/O$']` 
which would turn into `ls_1`.

The Substitution code is very old and treats `P` and `e` differently,
and seems not to consider static variables at all! BIG RETHINK

a REGRESSION in UTCP caused by fact that re-entering a proof can 
get locked into the wrong base theory

### Next in Line

The following laws in UTP base seem to match anything:
```
   6. ⊤  “II_def”           II ≡ (O$'=O$)  ⊤
   8. ⊤  “bot_def”          ⊥ ≡ true  ⊤
   9. ⊤  “top_def”          ⊤ ≡ false  ⊤
```
e.g.,
```
Matches:
5 : “eqv_refl” true  ⊤ ⟹ ⊤ *
4 : “II_def” (O$'=O$)  ⊤ ⟹ ⊤ trivial!1
3 : “top_def” false  ⊤ ⟹ ⊤ trivial!1
2 : “bot_def” true  ⊤ ⟹ ⊤ trivial!1
1 : “exists_def” ¬¬((E ⊆ ls ∧ a) ∧ ls' = ls \ E ∪ N ≡ (E ⊆ ls ∧ a) ∧ ls' = ls \ E ∪ N)  ⊤ ⟹ ⊤ ≡lhs
⊢
(E ⊆ ls ∧ a) ∧ ls' = ls \ E ∪ N ≡ (E ⊆ ls ∧ a) ∧ ls' = ls \ E ∪ N    ⊤
Focus = []
```

Example:
```
Proof for A_alt
	A(E,a,N) ≡ (E ⊆ ls ∧ a) ∧ ls' = ls \ E ∪ N  ⊤
by red-All
A(E,a,N) ≡ (E ⊆ ls ∧ a) ∧ ls' = ls \ E ∪ N
   = 'match-eqv-pvar(1) II_def@[]'
 ...
⊢
(O$'=O$)    ⊤
```

## Parked for Now

### Works for handling actual theory observables

One possibility:  
a static-var healthiness condition 
`SV_x(P) ^= P /\ x = x'`.

So we add `(SV_in o SV_g o SV_out)(P)`.



Start Developing theories for:

* Hoare Triples
* Weakest Precondition
* UTCP  (in progress)
  depends on:
  * Arithmetic (done)
  * Sets (done)
  * Lists (done)
* Designs
* Reactive Systems


Want to have general settings away from files that contain syntax,
so that syntax changes only affect those files, and not the settings.

So proof settings should not be in `project.req`, for instance.
Lets use `settings.req` instead.

Proof settings command syntax is dreadful!
Should be the same in main and proof REPLs
(e.g.`set [no-]setting [args]`).
A similar syntax to show settings as well (e.g. `sh [setting]`).


### Idea


We should treat `=` like `≡` in pattern matching.

## Issues

Time to add type-inference!
Done but not yet ready to be hooked in.

Adding in Arithmetic and Set theories to test out the need for typechecking.

* We really need to have symmetric forms of key results, e.g., we have `P∨true≡true`, but should also have `true∨P≡true`.

For now, we simply hide all trivial and floating stuff by default.

### Theory and Proof Management.

reading a proof should check that proof and filename match.

Need a way to archive proofs outside theory files. 
Right now we lose a proof when we either demote it to try something different, 
or we have to re-compile and install the theory.

**Rethink** Keep it simple.

Should law names be unique, or tied to a theory?
If tied, are we obliged to use fully qualified names?
KISS: keep them unique for now.

#### Some observations

  * We now have `project.req` that contains settings, theory setup, and live proofs. How much can be determined by looking at the contents of other files also present? For now these are just theory files. Should we just identify a "top" theory?

  * The live proofs depend on an context based on the theories in scope when they were started, which is why they currently reside in `project.req` which captures that context. Could we shift these outside?

  * In any case, what happens to a live-proof if we edit a theory it depends on?  Should have a way of doing impact analysis of any change we make w.r.t *all* current live proofs? Perhaps this should only be done if it becomes an issue. Note: the `Provenance` datatype now has a 
  `Suspect` variant.

  * We have the notion of a "current" theory, w.r.t. which we setup proofs, and should be able to add, edit, and/or delete conjectures (axioms?), variable-table entries, and theory dependencies.

  * A theory called "MyTheory" is always associated with file `MyTheory.thr`.

  * A proof of conjecture "my_conjecture" will be saved in `my_conjecture.prf`.

  * We will add new features to existing `save`, `load` and `new` commands.

  * We will add `delete`, `copy` and `rename` commands.

#### Tasks

Add commands to create, delete, copy/rename theories,
with matching file support. Obviously can't create or delete the current theory, but copying is fine.


### Fixing "Equivales" proof generation

Given a proof attempt that reduces to `false`, we invoked the `=` command to create a proof of `(P∧¬ P∨Q∧¬ Q)∨R∧¬ R≡false`. However, it is shown as a `reduce` proof, which is how the original proof attempt was setup. The proof that results displays as:

```
this_is_false : (P∧¬ P∨Q∧¬ Q)∨R∧¬ R≡false
by 'reduce'
---
(P∧¬ P∨Q∧¬ Q)∨R∧¬ R
Attempting to prove the goal term to be satisfiable
CNF: R  ∧  ¬ R
Unit Propagation: false
Path: [2]
(P∧¬ P∨Q∧¬ Q)∨false
 = 'match-lhs lor_symm @[]'
    { P ⟼ P∧¬ P∨Q∧¬ Q, Q ⟼ false }
false∨(P∧¬ P∨Q∧¬ Q)
Attempting to prove the goal term to be satisfiable
CNF: P  ∧  ¬ P
Unit Propagation: false
Path: [2,1]
false∨(false∨Q∧¬ Q)
Attempting to prove the goal term to be satisfiable
CNF: Q  ∧  ¬ Q
Unit Propagation: false
Path: [2]
false∨false
 = 'match-lhs lor_idem @[]'
    { P ⟼ false }
false
```
This is not right, as it has become a reduce left-to-right proof (`redinit`), and the focii are all wrong, as all action now occurs on the LHS. We need to have a process that transforms the proof steps, and we need to provide an option to close the (failed) proof that lead to this point.

It should look something like this:

```
this_is_false : (P∧¬ P∨Q∧¬ Q)∨R∧¬ R≡false
by 'redinit'
---
(P∧¬ P∨Q∧¬ Q)∨R∧¬ R
Attempting to prove the goal term to be satisfiable
CNF: R  ∧  ¬ R
Unit Propagation: false
Path: [1,2]
(P∧¬ P∨Q∧¬ Q)∨false
 = 'match-lhs lor_symm @[]'
    { P ⟼ P∧¬ P∨Q∧¬ Q, Q ⟼ false }
false∨(P∧¬ P∨Q∧¬ Q)
Attempting to prove the goal term to be satisfiable
CNF: P  ∧  ¬ P
Unit Propagation: false
Path: [1,2,1]
false∨(false∨Q∧¬ Q)
Attempting to prove the goal term to be satisfiable
CNF: Q  ∧  ¬ Q
Unit Propagation: false
Path: [1,2]
false∨false
 = 'match-lhs lor_idem @[]'
    { P ⟼ false }
false
```

### Move some help stuff to AbstractUI !!!

Currently help info is in `Main.lhs`,
but a lot of command argument interpretation is done in the Abs GUI.
We should record some help stuff in there.


### Match Contexts

We need to review use of match-contexts at various levels
in the proof system.
In particular, extracting `VarTable`s from the top-level `mtchCntxt` component of a `LiveProof` by mapping `thd3` and then concatenating them is very inefficient: we should just take the head of the list instead.

### Complete UTPBase proofs

Doing this has shown that proof ranking and short-listing needs improvement.

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
 and allow the user to select their preferences, 
 which would be stored in the above-mentioned mapping tables.

 (This may get subsumed by using decent Terminal apps that 'get' unicode char widths)
 
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
  