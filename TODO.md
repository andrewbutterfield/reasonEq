# To Do

## Urgent/Now


BIGGER ISSUE

```
(E1 ⊆ ls ∧ a) ∧ ls' = ls \ R1 ∪ N1 ; (E2 ⊆ ls ∧ b) ∧ ls' = ls \ R1 ∪ N1    ⊤
Focus = []

Target (RHS): 
E2 ∪ R1 \ N1 = Ø ∧ X(E1 ∪ E2 \ N1,a ; b,R1 ∪ R2,N1 \ R2 ∪ N2)


Instantiated Law S.C. 
  = O$,O$'⊇E1, O$,O$'⊇E2, O$,O$'⊇N1, O$,O$'⊇N2, O$,O$'⊇R1, O$,O$'⊇R2, 
    O$,O$'⊇ls, O$,O$'⊇ls', fresh:O$_0
```

**We need to create a new `CoversDynamic` atomic side-condition.**


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

Seq. Comp: `";_def"`
```
(P ; Q) ≡ (∃ O$_0  • P[O$_0/O$'] ∧ Q[O$_0/O$])  O$,O$'⊇P, O$,O$'⊇Q, fresh:O$_0
```

Command `tm 1 ;_def` reports:
```
Match against `;_def'[1] OK
Binding: { ;  ⟼ ;, P  ⟼ X(E1,a,R1,N1), Q  ⟼ X(E2,b,R1,N1), 0  ⟼ 0, O$  ⟼ ⟨O$⟩ }
Instantiated Law = (∃ O$_0  • (X(E1,a,R1,N1))[O$_0/O$'] ∧ (X(E2,b,R1,N1))[O$_0/O$])

Law S.C. = O$,O$'⊇P, O$,O$'⊇Q, fresh:O$_0



Instantiated Law S.C. = O$,O$'⊇E1, O$,O$'⊇E2, O$,O$'⊇N1, O$,O$'⊇R1, O$,O$'⊇a, O$,O$'⊇b, fresh:O$_0
Goal S.C. = ⊤
Discharged Law S.C. = O$,O$'⊇E1, O$,O$'⊇E2, O$,O$'⊇N1, O$,O$'⊇R1, O$,O$'⊇a, O$,O$'⊇b, fresh:O$_0
```
The issue is that these side-conditions *should* only apply to dynamic variables,
and `a` and `b` should be predicate variables.

It happens also if we expand the X definitions:
```
⊢
(E1 ⊆ ls ∧ a) ∧ ls' = ls \ R1 ∪ N1 ; (E2 ⊆ ls ∧ b) ∧ ls' = ls \ R1 ∪ N1    ⊤


proof: tm 1 ;_def
Match against `;_def'[1] OK
Binding: 
  { ;  ⟼ ;
  , P  ⟼ (E1 ⊆ ls ∧ a) ∧ ls' = ls \ R1 ∪ N1
  , Q  ⟼ (E2 ⊆ ls ∧ b) ∧ ls' = ls \ R1 ∪ N1
  , 0  ⟼ 0
  , O$  ⟼ ⟨O$⟩ 
  }
Instantiated Law 
  = ∃ O$_0  • 
       ((E1 ⊆ ls ∧ a) ∧ ls' = ls \ R1 ∪ N1)[O$_0/O$'] 
       ∧ 
       ((E2 ⊆ ls ∧ b) ∧ ls' = ls \ R1 ∪ N1)[O$_0/O$]

Instantiated Law S.C.
 = O$,O$' ⊇ (E1 ⊆ ls ∧ a) ∧ ls' = ls \ R1 ∪ N1
 , O$,O$' ⊇ (E2 ⊆ ls ∧ b) ∧ ls' = ls \ R1 ∪ N1

 


= O$,O$'⊇E1, O$,O$'⊇E2, O$,O$'⊇N1, O$,O$'⊇R1, O$,O$'⊇a, O$,O$'⊇b, O$,O$'⊇ls, O$,O$'⊇ls', fresh:O$_0
Goal S.C. = ⊤
Discharged Law S.C. = O$,O$'⊇E1, O$,O$'⊇E2, O$,O$'⊇N1, O$,O$'⊇R1, O$,O$'⊇a, O$,O$'⊇b, O$,O$'⊇ls, O$,O$'⊇ls', fresh:O$_0
```




## Next in Line

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

### Parked for Now

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
  