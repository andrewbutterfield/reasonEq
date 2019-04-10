# To Do

## Hotfixes

## Next Task(s)

* arrange for `LiveProofs.tryLawByName` to do partial matches
	* we add a list of numbers to the command, and it matches against those terms in an equivalence
	* e.g. given law 'mylaw' *P≡Q≡R≡S≡T*, then `tm mylaw 1 3 5` will match against *P≡R≡T*, with *Q≡S* as replacement.
* add in side-condition inference
  * we need to consider when a partial equivalence match does not bind all pattern variables, and in particular those in side-conditions
  * e.g. matching against *[P]* in law *[P] ≡ ∀ x̅ • P*,  where the side-conditions is that *x̅* cover *P*.
  * Here we will have no binding for *x̅*, and will want to instantiate it as (at least) the free variables of the matching candidate term.
  * We need to introduce existential side-conditions, and within a proof, have a mechanism to instantiated the existentiallty quantified variable.
  * e.g., we now have law *[P] ≡ ∀ x̅ • P, ∃x̅⊇P*
  * In proof of *[[P]] = [P]*, which itself has no side-condition, we effectively introduce set-variables, asserting them equal to free variables of relevant predicates as existential witnesses. These allow us to transfrom [[P]] into [P], neither of which mentions these temporary set-variables. WE are matching the LHS of the law and replacing with the RHS.
  * In the event that we match the RHS to replace with the LHS, then the existential *∃x̅⊇P* is treated as the simpler *x̅⊇P*, as indeed we already have a "witness".
* complete side-cond instantiation.
* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).

## Quantifier Laws in proofs

## Theory Management

* law renaming
* Generating proof graph as dot/graphviz file.
