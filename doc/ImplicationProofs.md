# Implication Proofs

Obtained by cut-n-past from `reasonEq` theorem prover,
using the `sh P <theoren-name>` command.

## Alternative definition of implication

(Edited by hand to improve spacing)

```
implies_def2 : P⟹  Q≡¬ P∨Q
by 'reduce'
---
P⟹  Q≡¬ P∨Q
 = 'match-equiv[1] implies_def @[1]'
{ P ⟼ P, Q ⟼ Q, ⟹   ⟼ ⟹   }
(P∨Q≡Q)≡¬ P∨Q
 = 'match-equiv[1,2] equiv_symm @[1]'
{ P ⟼ P∨Q, Q ⟼ Q, ≡ ⟼ ≡ }
(Q≡P∨Q)≡¬ P∨Q
 = 'match-equiv[1] equiv_assoc @[]'
{ P ⟼ Q, Q ⟼ P∨Q, R ⟼ ¬ P∨Q, ≡ ⟼ ≡ }
Q≡(P∨Q≡¬ P∨Q)
 = 'match-equiv[2] lor_symm @[2,1]'
{ P ⟼ Q, Q ⟼ P, ∨ ⟼ ∨ }
Q≡(Q∨P≡¬ P∨Q)
 = 'match-equiv[2] lor_symm @[2,2]'
{ P ⟼ Q, Q ⟼ ¬ P, ∨ ⟼ ∨ }
Q≡(Q∨P≡Q∨¬ P)
 = 'match-equiv[1,2] lor_equiv_split @[2]'
{ P ⟼ Q, Q ⟼ P, ≡ ⟼ ≡, ¬ ⟼ ¬, ∨ ⟼ ∨ }
Q≡Q
 = 'match-all equiv_refl @[]'
{ P ⟼ Q, ≡ ⟼ ≡ }
true
```

## Some early theorems

(Undedited, so reveals `reasonEq` spacing)

```
contrapositive : P ⟹ Q  ≡  ¬Q ⟹ ¬P
by 'redtail'
---
¬ Q ⟹ ¬ P
 = 'match-equiv[1] implies_def2 @[]'
{ P ⟼ ¬ Q, Q ⟼ ¬ P, ⟹   ⟼ ⟹   }
¬(¬Q) ∨ ¬P
 = 'match-equiv[1] lnot_invol @[1]'
{ P ⟼ Q, ¬ ⟼ ¬ }
Q ∨ ¬P
 = 'match-equiv[2] lor_symm @[]'
{ P ⟼ ¬ P, Q ⟼ Q, ∨ ⟼ ∨ }
¬P ∨ Q
 = 'match-equiv[2] implies_def2 @[]'
{ P ⟼ P, Q ⟼ Q, ¬ ⟼ ¬, ∨ ⟼ ∨ }
P ⟹ Q
```

```
implies_meet : P⟹  Q≡(P∧Q≡P)
by 'reduce'
---
P⟹  Q≡(P∧Q≡P)
 = 'match-equiv[1] implies_def @[1]'
{ P ⟼ P, Q ⟼ Q, ⟹   ⟼ ⟹   }
(P∨Q≡Q)≡(P∧Q≡P)
 = 'match-equiv[1,2] equiv_symm @[]'
{ P ⟼ P∨Q≡Q, Q ⟼ P∧Q≡P, ≡ ⟼ ≡ }
(P∧Q≡P)≡(P∨Q≡Q)
 = 'match-equiv[1] equiv_assoc @[]'
{ P ⟼ P∧Q, Q ⟼ P, R ⟼ P∨Q≡Q, ≡ ⟼ ≡ }
P∧Q≡(P≡(P∨Q≡Q))
 = 'match-equiv[1,2] equiv_symm @[2,2]'
{ P ⟼ P∨Q, Q ⟼ Q, ≡ ⟼ ≡ }
P∧Q≡(P≡(Q≡P∨Q))
 = 'match-equiv[2] equiv_assoc @[2]'
{ P ⟼ P, Q ⟼ Q, R ⟼ P∨Q, ≡ ⟼ ≡ }
P∧Q≡((P≡Q)≡P∨Q)
 = 'match-all golden-rule @[]'
{ P ⟼ P, Q ⟼ Q, ≡ ⟼ ≡, ∧ ⟼ ∧, ∨ ⟼ ∨ }
true
```

```
implies_subst : (P⟹  Q)[e$/x$]≡P[e$/x$]⟹  Q[e$/x$]
by 'reduce'
---
(P⟹  Q)[e$/x$]≡P[e$/x$]⟹  Q[e$/x$]
   = 'substitute @[1]'
P[e$/x$]⟹  Q[e$/x$]≡P[e$/x$]⟹  Q[e$/x$]
 = 'match-all equiv_refl @[]'
{ P ⟼ P[e$/x$]⟹  Q[e$/x$], ≡ ⟼ ≡ }
true
```


