# reasonEq Tutorial

## Prerequisites

`reasonEq` has been installed and started for at least the first time according to instructions
in the top-level  `README.md`.

You should have seen a transcript similar to this, observed on OS X:

```
:- req
starting REPL...
Running user mode, default initial state.
Creating app. dir.: /Users/butrfeld/.reasonEq
Creating workspace : /Users/butrfeld/TEST/MyReasonEq
appFP = /Users/butrfeld/.reasonEq
projects:
*MyReasonEq|/Users/butrfeld/TEST/MyReasonEq

Creating /Users/butrfeld/TEST/MyReasonEq
Creating /Users/butrfeld/TEST/MyReasonEq/project.req
Project Name: MyReasonEq
Project Path: /Users/butrfeld/TEST/MyReasonEq
Loading...
Welcome to the reasonEq 0.6.9.0 REPL
Type '?' for help.

REq ≡ 
```

## Getting Help

Requesting help by typing `help` or `?` results in:

```
quit -- exit
?,help -- this help text
?,help <cmd> -- help for <cmd>
sh -- show parts of the prover state
set -- set parts of the prover state
new -- generate new theory items
N -- new proof
r -- return to live proof
save -- save prover state to file
load -- load prover state from file
b -- builtin theory handling
```

More help on a specific command is given by supplying it to help,
so typing `? sh` results in:

```
sh f -- show current project
sh s -- show logic signature
sh t -- show theories
sh L -- show laws
sh T -- show 'current' theory
sh c -- show current conjectures
sh p -- show current (live) proof
sh P -- show completed proofs
```