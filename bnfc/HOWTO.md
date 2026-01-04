# HowTo

We use `bnfc -d -m UTP.lbnf` 
which puts the generated stuff into directory `reasonEq/bnfc/UTP`.

General approach:

```
bnfc -d -m UTP.lbnf
make
UTP/Test
  <enter stuff>
^D
```

## Issues

Lexing for variables like `'varA` (Before `varA`),
 `varB'` (After `varB`),
 and `varC_m` (During `var_C`) is too difficult.
 The plan is to encode those as follows:
 `b_varA`, `varB_a`, and `varC_m`, where `m` will be numeric. 


The comparisons (== and friends) are now part of  `Pred`, 
which also has its own identifiers.





