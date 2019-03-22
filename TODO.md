# To Do

## Hotfixes

## Next Task(s)

* figure out where side-condition checking should be done
  * what is the last point at which we have both the goal and law side-conditions to hand?
     * the `Match` type has field `mAsn` - the law assertion, incl. its s.c. 
     * the goal s.c. is dropped when calling into `LiveProofs` from `AbstractUI` - a term is passed over rather than an assertion.
* implement side-cond instantiation.
* make proof loading more tolerant of read/show mismatches - allow a step to be marked as TBR (to-be-redone).
* instantiate side-conditions in matches
* handle side-conditions (just `Disjoint` for now)

## Quantifier Laws in proofs

## Theory Management

* law renaming
* Generating proof graph as dot/graphviz file.
