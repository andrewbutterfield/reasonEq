# HowTo

We use `bnfc -d -m UTP.lbnf` 
which puts the generated stuff 
into directory `reasonEq/src/BNFC/UTP`.

General approach:

```
cd .../reasonEq/src/BNFC
bnfc -d -m UTP.lbnf
make -f rmake
./Runner
  <enter stuff>
^D
```

Now we need to move to having a test program. 
We will add a new top-level application, to be built using stack.
Currently standalone.

## Issues

Lexing for variables like `'varA` (Before `varA`),
 `varB'` (After `varB`),
 and `varC_m` (During `var_C`) is too difficult.
 The plan is to encode those as follows:
 `_varA`, `varB_`, and `varC_m`, where `m` will be numeric. 

Replaced `Pred` and `Exp` by `Term`.



