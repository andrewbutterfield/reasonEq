# To Do

## URGENT or NEXT

Add in Hoare-Triple and WP theories together as `PrePost`, based on `Designs`.

**PLAN**

```
[(∀ x$  • P)]
 ⊤
Focus = [] :: 𝔹 
proof: tm 1 []_def
Match against '[]_def'[1] failed!
try s.c. instantiation failed
{ B  ⟼ 𝔹 , P  ⟼ (∀ x$  • P), x$  ⟼ ⟨?x$⟩ }  &&   x$⊇P
lnm[parts]=[]_def[1]
tC=[(∀ x$  • P)]
scC=⊤
tP'=(∀ ?x$  • (∀ x$  • P))
partsP=[P]
replP=(∀ x$  • P)
scP=x$⊇P
vsp2vsc: (P⊇(?x$∖x$))
not single gvar disjoint or superset
```



We cannot prove `X_X_comp` without the relevant invariants.

Time to get `Designs` going and then to the proper UTCP semantics

We need a a way to add witness `ok_1 == false`.

Type `VarBind` has a `BindId` variant, 
but it is only used for variables of dynamicity `During`.  
We should really use this to bind constructor identifiers.


`LiveProofs.undoCalcStep` needs fixing!


**still an issue?**

However `s` converts `Q[O$_1/O$]` to `Q` even with s.c. `O$,O$'⊇ₐQ`
and `ok[O$_1/O$]` to `ok` even with `O$⊇ₐok`.
(it should remain unchanged).

The issue is that, while we have s.c. `O$,O$'⊇ₐQ` in scope,
and we know `Q` is mentioned,
the substitution uses `getLVarExpansions` and `processExpand`
to do further analysis solely based on vartable data.
The only mention of `O$` is `O`, an abstract set in theory `U_CWhl`.

This part of substitute seems to be **massively over-engineered**.


We should search for a target that is clearly involved with the given term variable.
There should only be one, but we could filter to see if there are multiple.

* Continue developing the  `Designs` theory. 
* Add a  `While.Design` theory.
* Most of the laws/conjectures for naive and design while-languages are the same. However `While.Common` is not the place for those. The conjectures need to be in or "above" a theory that gives the specific semantics.
In effect there should be a copy of all these conjectures in both the theories that have the semantic axioms. Ideally their names will be distinct.
* For sequential composition in Designs, the right-unit law requires **H3**, while the right-zero law requires **H4**.
* Need a pre/post-condition theory that covers sec 2.8 of the book (Hoare Triples, Floyd assertions, Weakest precondition).

### Simple Input Format

We want a text format for theory artifacts that is easy to parse,
rather than being readable.

We will use the need to expand the `Sets` theory to drive a mechanism to read conjectures from a text file.

* Now have conjecture naming convention: `conj_name-conj.txt`.
* need to define syntax for and handle substitutions
* need to be able to declare variables
* need to have proper line/position numbers for better error messages
* should save live-proofs outside `project.req`.


### Known Constants and Substitution

If `k` is known to be shorthand for `t`,
then the only valid uses of `k` as a substitution target are `[k/k]` or `[t/k]`.

Note that there currently is **no** use made of Known Constants.

### Matching Issues


### RANKING BUSTED

It needs a complete redesign
It should define and export DS + functions to define its settings.

In general proofs involving prop logic, esp. and/or/not  rhs matches are as good as lhs ones!

`eqv_refl [*]` should beat `eqv_def [≡[1,2]]` !!! 
 `true` vs `P ∧ P ∨ ¬P ∧ ¬P` !!!`


**Need useability improvements**

* better theory load/save support
  * if theory is updated, allow proofs to be loaded in rather than redone
* better proof display settings:
  * better setting command syntax
  * finer control of level of detail (e.g. don't show scTrue as T, leave blank)
  * proof help should appear before proof prompt (after matches), and NOT wait for use to hit the return key. **Builtin to REPL!!!**
  * proof show output likewise.
  * ability to save liveproof settings as toplevel settings

## Next in Line

Need to expand the `Sets` theory to capture interactions between set operators,
and the `Equality` theory to support reasoning like:

```
x=e /\ E(x)        ===  x=e /\ E[e/x]   ===?  E[e/x]
expr=u /\ E(expr)  ===  expr=u /\ E(u)  ===?  E(u)
```

TODO?

Future improvement:  given `E` is an `ExprVar` and `O$` maps to `ObsV`,
it should be obvious that `O$,O$' ∉ E`. No need for an explicit side-condition.
 
 Allow user to toggle between which s.c. version is displayed
    (currently both are)?


```
1 : “exists_def” [≡lhs] ¬(¬(X(E1,a,R1,N1)))
ls,ls',s,s'∉N2, s,s'⊇ₐa, s,s'⊇ₐb ⟹ ⊤
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
  * Sets (in progress)
  * Lists (done)
* Designs
* Reactive Systems


Want to have general settings away from files that contain syntax,
so that syntax changes only affect those files, and not the settings.

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

Type-check need confirmed with X_X_comp, as per following excerpt:

```
4 : “*_cancel” [≡rhs]
    ?e * (E2 ∩ (R1 \ N1)) = ?e * Ø
 3 : “+_cancel” [≡rhs]
    ?e + E2 ∩ (R1 \ N1) = ?e + Ø
 ⊢
E2 ∩ (R1 \ N1) = Ø ∧ ...
```

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
  