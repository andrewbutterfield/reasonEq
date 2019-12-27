# To Do

## Reverse Substitution

While proving `exists_inst` (should that be `exists_gen`?) we encounter

 *(∀ x̅,y̅ • ¬ P)⟹  (∀ y̅ • ¬(P[e̅/x̅]))*
 
Here we need to "reverse" the substitution to transform *¬(P[e̅/x̅])* into *(¬P)[e̅/x̅]*.

When is this sound?  Consider *P = C(P1 sigma, P2 sigma, ...)*
where *Pi* are predicate/expression **variables**, and *...* can contain other predicates over observation variables.

Let *R = (C(P1,P2,...)) sigma*.
When will *R = P*, once *sigma* is applied?

The answer seems to be:

* the "same" explicit substutition throughout on all occurences of free predicate/expression variables;
* no free observational variables in *C(P1,P2,...)* are targetted by *sigma*;
* all occurences of predicate (*P*) or expression (*e*) variables have *sigma*
  applied.

By "same" we mean "same - modulo quantifiers", i.e., that *sigma*
outside a quantifer *Q x$ @ P*, is the same as *sigma\x$* within *P*.


## Quantification

Need to substitute for variables, noting that x, e, and P will behave
differently depending on the target class of the substitution.

## Robustness

### Robust Load
Need to make file loading robust - no runtime failure.

* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

### Testing

`Substitution.lhs` looks like a good candidate for QuickCheck !

Example:  *(P\s1)s2 = P(s1;s2)* (a.k.a. `substitute` and `substComp`).
### Theory Checks

Need a way to check a theory (in context, with all its dependencies)

* all Cons have a substitutability indication.

## Ongoing Issues

### `a n` command in proof REPL

When instantiating unbound variables we have two cases:

1. We have a `StdVar`, which binds to a term. 
   We allow a default option of binding to `true`.
2. We have a `LstVar`, which binds to a variable-set.
   We allow a default option of binding to `{}`.
   
Defaults are specifed by hitting enter with no selection data.

### Instantiating Side-Conditions

`instantiateASC` is just wrong - it's acting more like discharge should.
Also, `Disjoint` and `IsPre` distribute conjunctively through set union (of sets formed when `vs` and `gv` get instantiated)
However, assume we have `Covers x$ P` where `x$` is mapped to `{a,b,c$}` and `P` to `Q /\ x=1 \/ R` (say).
This cannot be broken down into a conjuction of conditions relating
each of `a`, `b`, and `c$` individually to each of `Q`, `{x}`,
and `R`, also taken individually.
Instead we have to assert that `{a,b} U c$` covers `Q U {x} U R`.

### Backing out of a proof step

If we use "b" after a proof step that is not reversible (just Clone?), we leave the goal unchanged,
but shorten the list of steps anyway. See `LiveProofs.undoCalcStep` (line 810 approx)

### Unique quantified variables

We need to either have unique q.v.s, or be very careful. Consider matching `[∀ x$ @ P]`  against `[P]` (part 1 of `[]_def`). How do we distinguish this `x$` from the one in the law?

Need care here - in the conjecture
 `(∃ x̅,y̅ • ∧(x̅=e̅)∧P)≡(∃ y̅ • P[e̅/x̅])  x̅ ∉ e̅` 
we need `x̅` and `y̅` to be the same.

What we want to avoid is "shadowing", 
so that `(∀ x̅ • P ∨ (∀ x̅ • Q)`
becomes `(∀ x̅ • P ∨ (∀ y̅ • Q[y̅/x̅])`.

## Next Task(s)


 
* LiveProof returns `(bind,local_scC)` - need to get `local_scC` into proof step.




## Quantifier Laws in proofs

## Theory Management

* law renaming

* Generating proof graph as dot/graphviz file.