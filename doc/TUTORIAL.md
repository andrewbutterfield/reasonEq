# reasonEq Tutorial

## Prerequisites

`reasonEq` has been installed and started for at least the first time according to instructions
in the top-level  `README.md`.

You should have seen a transcript similar to this:

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

You are now using the "Top-Level" command line interface.

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
so, for example, typing `? sh` results in:

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

## Builtin Theories

Currently it is not possible for the user to create new theories,
or add new axioms to existing theories.
Instead, some builtin theories have been defined, but they are not "installed" by default.

The `b` command allows the installation and checking of builtin theories

```
b e -- list all existing builtin theories
b i -- list all installed theories
b I <name> -- install builtin theory <name>
```

For this tutorial we need theories `PropAxioms` and `PropEquiv` to be installed:

```
REq ≡ b I PropAxioms
*REq ≡ b I PropEquiv
*REq ≡ b i
PropEquiv ; PropAxioms
*REq ≡ 
```

The asterisk on the prompt indicates that the prover state has been modified, but not yet saved.
Save it, just to be safe:

```
*REq ≡ save
REQ-STATE written to '/Users/butrfeld/TEST/MyReasonEq'.
REq ≡ 
```

Now, ask to see all the known laws, using `sh L` :

```
---
Theory 'PropEquiv'
Known Variables: None
Laws: None.
Conjectures:
   1. ❓  “≡_id”  (true≡Q)≡Q  
---
Theory 'PropAxioms'
Known Variables:
false ≜ ¬(true)
true : 𝔹
Laws:
   1. ⊤  “true”         true  
   2. ⊤  “≡_refl”       P≡P  
   3. ⊤  “≡_assoc”      ((P≡Q)≡R)≡(P≡(Q≡R))  
   4. ⊤  “≡_symm”       P≡Q≡Q≡P  
   5. ⊤  “false-def”    false≡¬(true)  
   6. ⊤  “¬_≡_distr”    ¬(P≡Q)≡(¬(P)≡Q)  
   7. ⊤  “∨_symm”       P∨Q≡Q∨P  
   8. ⊤  “∨_assoc”      P∨Q∨R≡P∨Q∨R  
   9. ⊤  “∨_idem”       P∨P≡P  
  10. ⊤  “∨_≡_distr”    P∨(Q≡R)≡P∨Q≡P∨R  
  11. ⊤  “excl-middle”  P∨¬(P)  
  12. ⊤  “golden-rule”  P∧Q≡((P≡Q)≡P∨Q)  
  13. ⊤  “⟹ _def”       P⟹ Q≡P∨Q≡Q  
Conjectures: None.
```

We see that we have two theories installed. At the bottom is the `PropAxioms` theory, which contains thirteen laws, all marked with '⊤' to indicate that they are axioms.
There are also two known predicate variables defined, `true` and `false`.
Above this is the `PropEquiv` theory, which has no laws, but does contain one *conjecture*, a predicate that we hope is true, and which we shall now raise to theoremhood by proving it so. Conjectures are marked with '❓'.

## Finding Conjectures

In order to prove a conjecture we need to ensure 
that its containing theory is "current":

```
REq ≡ sh T
No current theory.
```

If it isn't, as in the above example, then we can make it so:

```
REq ≡ set T PropEquiv
Current Theory now 'PropEquiv'
*REq ≡ 
```

At this point we can ask to see the conjectures available in the
current theory, using `sh c` :

```
   1. “≡_id”  (true≡Q)≡Q  
```

There is only one in this case. 

## Proving “≡_id”

Start a new proof by entering `N 1` (new proof for conjecture 1).
You are shown a list of four options:

```
REq ≡ N 1
   1. 'reduce':   ⊢ (true≡Q)≡Q = true
   2. 'redboth':   ⊢ true≡Q = Q
   3. 'redtail':   ⊢ Q = true≡Q
   4. 'redinit':   ⊢ true≡Q = Q
Select sequent by number: 
```
Each option corresponds to a different strategy that is applicable
to the conjecture.
Proof strategies will be described in detail elsewhere,
and for now we will simply select the `reduce` strategy by typing `1`. 
This strategy is simply to try to reduce the whole conjecture down to `true`.
In effect we are going to prove this by reducing the lefthand-side
`(true≡Q)≡Q` to the righthand-side `true`.

Entering `1` causes the screen to clear (on OS X/Unix at least)
and displays something like this:

<img src="images/starting-equiv-id-proof.png" alt="Proof Start" width=33%>

We see that we are proving conjecture `≡_id` using the `reduce` strategy. 
We are told that our target (righthand-side) is `true`.
We see our lefthand-side displayed, in color,
and finally we see that we have a new command line prompt `proof:`.

You are now in the Prover command line interface.
This has a different set of commands to the top-level one,
but still has the same help mechanism:

```
proof: ?

q -- exit
? -- this help text
? <cmd> -- help for <cmd>
ll -- list laws
d -- down
u -- up
m -- match laws
a -- apply match
fe -- flatten equivalences
ge -- group equivalences
b -- go back (undo)
i -- instantiate
s -- switch
h -- to hypothesis
l -- leave hypothesis
c -- clone hyp
```

### Proof Step 1

We start by invoking the `Matcher` that tries to match the current
goal, here `(true≡Q)≡Q`, against known laws.
This is done by typing `m` to produce:

```
Matches:
1 : “≡_assoc” gives     true≡(Q≡Q)  
2 : “≡_symm” gives     Q≡(true≡Q)  
3 : “≡_symm” gives     Q≡(true≡Q)  
4 : “≡_symm” gives     ((true≡Q)≡Q)≡Q≡Q  
5 : “≡_symm” gives     P≡((true≡Q)≡Q)≡P  
6 : “≡_symm” gives     P≡((true≡Q)≡Q)≡P  
7 : “≡_symm” gives     Q≡Q≡((true≡Q)≡Q)  
8 : “∨_idem” gives     ((true≡Q)≡Q)∨((true≡Q)≡Q)  
9 : “⟹ _def” gives     P⟹ ((true≡Q)≡Q)≡P∨((true≡Q)≡Q)
```
The matcher tries to match the goal against entire laws, in which case it would report a match that "gives true". It also takes laws
of the form `P≡Q` and try to match the goal against just `P` and just `Q`. If it succeeds in matching against `P`, then it "gives Q" back (and vice-versa.)

In our case, we see that it matched, amongst other things,
 against the lefthand-side
of the `≡_assoc` law and is giving back the righthand-side. 
This is what we want so we request that match 1 be applied,
using command `a 1` (or `a1`).

This results in:

<img src="images/2-equiv-id-one-a1.png" alt="Proof Start" width=40%>

We see that the goal has changed,and also that we have the start of a proof transcript showing the the original goal was transformed by a match with the `≡_assoc` law at the top-level.

### Proof Step 2

We now want to focus attention on the `Q≡Q` sub-part of the goal. It is the second argument to thew top-level `≡` operator, so we want to move the focus down to that 2nd argument.
We do this using the command `d 2`:

<img src="images/3-equiv-id-down-2.png" alt="Proof Start" width=38%>

No we see the sginificance of the purple colour - it signifies that we are focussed in on a part of the overall goal.
We not want to see what this matches against,
so we issue the match command `m` once more:

```
Matches:
1 : “≡_refl” gives     true  
2 : “≡_symm” gives     Q≡Q  
3 : “≡_symm” gives     Q≡Q  
4 : “≡_symm” gives     (Q≡Q)≡Q≡Q  
5 : “≡_symm” gives     P≡(Q≡Q)≡P  
6 : “≡_symm” gives     P≡(Q≡Q)≡P  
7 : “≡_symm” gives     Q≡Q≡(Q≡Q)  
8 : “∨_idem” gives     (Q≡Q)∨(Q≡Q)  
9 : “⟹ _def” gives     P⟹ (Q≡Q)≡P∨(Q≡Q) 
```

Here the first match is against all of the law `≡_refl`,
so we use `a 1` to apply it:

<img src="images/5-equiv-id-two-a1.png" alt="Proof Start" width=38%>

Note that we are still focussed at the same place. Here we matched the law `≡_refl` at the second component of the top-level goal (`@[2]`).

### Proof Step 3

To complete, we want to return to the top-level,
so we issue the up-command `u` :

<img src="images/6-equiv-id-up.png" alt="Proof Start" width=38%>

Now we match (`m`) and see the same matches as the previous step,
so we apply the first (`a1`).

```
proof: a1
Proof Complete
*REq ≡ 

```

The proof is complete, so this reported, and we exit the proof command-line and return top the top-level command line.
If we now ask to see the laws usinf `sh L`, then almost everything
is unchanged, except at the top where we see:

```
*REq ≡ sh L

---
Theory 'PropEquiv'
Known Variables: None
Laws:
   1. ∎  “≡_id”  (true≡Q)≡Q  
Conjectures: None.
---

```

We see the the `PropEquiv` theory has no conectures anymore,
but a new law (“≡_id”) instead. This law differs from the axioms in `PropAxioms` in that it is marked with `∎` instead of `⊤` to show that it is a theorem with a proof, rather than an axiom.

## Next Steps.

Try installing theory `PropNot` and proving its four conjectures.
