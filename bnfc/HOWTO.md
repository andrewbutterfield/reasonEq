# HowTo

We use `bnfc -d -m REQ.lbnf` 
which puts the generated stuff 
into directory `reasonEq/bnfc/REQ`.

General approach:

For development/debugging:

```
cd .../reasonEq/bnfc
bnfc -d -m REQ.lbnf
make -f rmake
./Runner -- help
./Runner
  <enter stuff>
^D
```

For deployment:

```
cd .../reasonEq/bnfc
bnfc -d -m REQ.lbnf
make
source deploy.sh
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



