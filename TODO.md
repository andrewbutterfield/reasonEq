# To Do

## Hotfixes

Need to use `bindLVarToTlist` in `lvlvMatchCheck` instead of both `bindLVarToVList` and `bindLVarToVSet`. Both target and replacement list-variables should be bound to lists of the same length, to maintain target/replacement correspondance.

How do we convert a list-var to a term?

## Next Task(s)

* instantiate side-conditions in matches
* handle side-conditions (just `Disjoint` for now)

## Quantifier Laws in proofs

## Theory Management

* law renaming
* Generating proof graph as dot/graphviz file.
