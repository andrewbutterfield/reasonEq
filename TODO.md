# To Do

### Test Re-jigging

Trying to have common data and function definitions for testing. Non-trivial.

Want to support local (internal) tests within any module that does not export
all data-structure details, with some hidden by invariant-checking constructor functions.
Want lots of shorthand (partial) builders for test data for these data-structures.

To avoid cyclic module imports, we need to export shorthands from non-test modules.
Testing modules need to import the modules they test.



### Laws

We have hard-coded nesting simplification (`FreeVars.lhs`).

However, we still need a hard-coded rule of the form `(∀ x̅ • (∃ y̅ • P)) = (∃ y̅ • P)` whenever `y̅ covers P`.

When we expand `[P]` twice using `[]_def`, 
we need to end up at `(∀ x̅ • (∀ y̅ • P)`, 
where both `x̅` and `y̅`
are *fresh*.
**Having both the same is unsound**.

#### IDEA:


We extend variable names `v` to `v.u` where `u` is a natural number. 
A variable written as `v` is normally represented as `v.0`.

Entering `(∀ x • (∃ y • x + y = z))` will initally result in `(∀ x.0 • (∃ y.0 • x.0 + y.0 = z.0))`
which will then be "normalised" to ``(∀ x.1 • (∃ y.1 • x.1 + y.1 = z.0))`

As far as proofs and matching are concerned, `v.n` and `v.m` are different if `n` and `m` are.
However, when dispaying terms to the user, the `.u` part will usually be suppressed.
One exception might be when displaying match bindings.


##### Why?

We could have a scheme that makes different "instances" of `v` by appending a number to make it unique,
but then we get a lot of cluttered terms, particulary if we are using variables that already end in numbers
(e.g. a law like `i1 + (i2 + i3) = (i1 +i2) + i3`.

The approach described here has two advantages:

1. we can switch easily between showing the `.u` component or not
2. The algorthim to "normalise" terms becomes much simpler. 

#### How?

We first add the `u` component to the `Identifier` datatype, and set it to zero.
Then, rebuild and check tests and proof engine is unchanged.

Done as `FreeVars.normaliseQuantifiers` which now takes an `Assertion` (which itself is now defined in module `SideCond`).

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
 