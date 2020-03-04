# To Do

The `tm` command now works properly, as does side-conditions instantiation
and discharge.
Next step is to ensure that the `m` and `a` commands do the right thing.


### SC Handling during Matching

We invoke `matchFocus` which itself calls `matchInContexts`
which invokes `domatch` on every law in scope.
This calls `basicMatch`  and `doPartialMatch`.

The key seems to be `basicMatch` which does (among other things:)

```
bind <- match vts tC partsP
(bind',scC',scP') <- completeBind vts tC scC tP scP bind
scP'' <- instantiateSC bind' scP'
if scDischarged scC' scP'' then ... -- we return a match!       
```

### SC Handling during match Application

Old `applyMatchToFocus` (deprecated) did:

```
let unbound = findUnboundVars bind repl
let goalAsn = conjecture liveProof
let brepl = autoInstantiate bind (mRepl mtch)
```

New `applyMatchToFocus1` does:

```
let unbound = findUnboundVars (mBind mtch) (mRepl mtch)
```

while `applyMatchToFocus2` follows up with:

```
brepl <- instantiate bind (mRepl mtch)
```

### "Instantiations" and friends

1. `Instantiate.instantiate :: Monad m => Binding -> Term -> m Term`
2. `Instantiate.instantiateSC :: Monad m => Binding -> SideCond -> m SideCond`
3. `Instantiate.autoInstantiate :: Binding -> Term -> Term`
4. `Instantiate.findUnboundVars :: Binding -> Term -> VarSet`
5. `Instantiate.termLVarPairings :: Term -> [(ListVar,ListVar)]`
6. `Instantiate.mkEquivClasses :: Eq a => [(a,a)] -> [[a]]`
7. `Instantiate.questionableBinding :: Binding -> [[ListVar]] -> VarSet -> Binding`

## Robustness

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
* 