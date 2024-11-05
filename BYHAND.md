# PROOFS BY HAND

A place to look at proofs by hand while figuring stuff out

`O$,O$'∉E1, O$,O$'∉E2, O$,O$'∉N1, O$,O$'∉N2, O$,O$'∉R1, O$,O$'∉R2, O$,O$'⊇ₐa`

We need a tighter side-condition on `a` and `b`:  `{s,s'}⊇ₐa.b`.

Prove:
```
∃ O$_1  • 
    ls_1 = (ls \ R1) ∪ N1 ∧ 
    E1 ⊆ ls ∧ 
    a[O$_1/O$'] ∧ 
    E2 ⊆ ls_1 ∧ 
    b[O$_1/O$] ∧ 
    ls' = (ls_1 \ R2) ∪ N2  
 = "1pt"
∃ O$_1\ls  • 
    E1 ⊆ ls ∧ 
    a[O$_1/O$'][ls \ R1 ∪ N1/ls_1] ∧ 
    E2 ⊆ ls \ R1 ∪ N1 ∧ 
    b[O$_1/O$][ls \ R1 ∪ N1/ls_1] ∧ 
    ls' = ((ls \ R1) ∪ N1) \ R2 ∪ N2  
 = "{s,s'}⊇ₐa.b,  O$={s,ls}"
∃ s_1  • 
    E1 ⊆ ls ∧ 
    a[O$_1/O$'] ∧ 
    E2 ⊆ ls \ R1 ∪ N1 ∧ 
    b[O$_1/O$] ∧ 
    ls' = (ls \ R1 ∪ N1) \ R2 ∪ N2 
 = "scoping" 
E1 ⊆ ls ∧ 
E2 ⊆ (ls \ R1) ∪ N1 ∧ 
ls' = (((ls \ R1) ∪ N1) \ R2) ∪ N2  ∧
∃ s_1  • a[s_1/s'] ∧ b[s_1/s] 
 = ";_def"
E1 ⊆ ls ∧ E2 ⊆ (ls \ R1) ∪ N1 ∧
(a;b) ∧
ls' = (((ls \ R1) ∪ N1) \ R2) ∪ N2
```

Lemmas
```
E2 ⊆ (ls \ R1) ∪ N1
 = E2 ⊆ (ls \ R1) \/ E2 ⊆ N1
 = E2 ⊆ ls /\ E2 not⊆  R1  \/ E2 ⊆ N1
```

```
X(E,a,R,N) ≡ E ⊆ ls ∧ a ∧ ls' = ls \ R ∪ N  
O$,O$'∉E, O$,O$'∉N, O$,O$'∉R
```