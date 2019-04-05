# To Do

## Hotfixes

## Next Task(s)

* create Closure AST item for [P] and friends
  * the empty `vs` hack is bad. 
* add in side-condition inference
  * we need to consider when a partial equivalence match does not bind all pattern variables, and in particular those in side-conditions
  * e.g. matching against *[P]* in law *[P] = ∀ x̅ • P*,  where the side-conditions is that *x̅* cover *P*.
  * Here we will have no binding for *x̅*, and will want to instantiate it as (at least) the free variables of the matching candidate term.
* complete side-cond instantiation.
* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

## Quantifier Laws in proofs

## Theory Management

* law renaming
* Generating proof graph as dot/graphviz file.
