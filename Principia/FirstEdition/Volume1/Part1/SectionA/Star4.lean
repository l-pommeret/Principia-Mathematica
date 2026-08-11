/-!
# PM I, first edition, ✱4 — equivalence and formal rules

This source-critical file deliberately records only the diplomatic source for
the prepared ✱4 items.  Their Lean declarations are not introduced until their
earlier PM dependencies have been reconstructed and kernel-checked.

Canonical scan leaves: 142–145 (printed pp. 120–123).
-/

/- PM-VERBATIM-BEGIN PM1:✱4·01
✱4·01.  p ≡ q .=. p ⊃ q . q ⊃ p   Df

When each of two propositions implies the other, we say that the two are
equivalent, which we write "p ≡ q."
PM-VERBATIM-END PM1:✱4·01 -/

/- PM-VERBATIM-BEGIN PM1:✱4·02
✱4·02.  p ≡ q ≡ r .=. p ≡ q . q ≡ r   Df

This definition serves merely to provide a convenient abbreviation.
PM-VERBATIM-END PM1:✱4·02 -/

/- PM-VERBATIM-BEGIN PM1:✱4·1
✱4·1.  ⊢ : p ⊃ q . ≡ . ∼q ⊃ ∼p   [✱2·16·17]
PM-VERBATIM-END PM1:✱4·1 -/

/- PM-VERBATIM-BEGIN PM1:✱4·11
✱4·11.  ⊢ : p ≡ q . ≡ . ∼p ≡ ∼q   [✱2·16·17 . ✱3·47·22]

These are both forms of the "principle of transposition."
PM-VERBATIM-END PM1:✱4·11 -/

/- PM-VERBATIM-BEGIN PM1:✱4·12
✱4·12.  ⊢ : p ≡ ∼q . ≡ . q ≡ ∼p   [✱2·03·15]
PM-VERBATIM-END PM1:✱4·12 -/

/- PM-VERBATIM-BEGIN PM1:✱4·13
✱4·13.  ⊢ . p ≡ ∼(∼p)   [✱2·12·14]

This is the principle of double negation, i.e. a proposition is equivalent to
the falsehood of its negation.
PM-VERBATIM-END PM1:✱4·13 -/

/- PM-VERBATIM-BEGIN PM1:✱4·14
✱4·14.  ⊢ : p . q . ⊃ . r : ≡ : p . ∼r . ⊃ . ∼q   [✱3·37 . ✱4·13]
PM-VERBATIM-END PM1:✱4·14 -/

/- PM-VERBATIM-BEGIN PM1:✱4·15
✱4·15.  ⊢ : p . q . ⊃ . ∼r : ≡ : q . r . ⊃ . ∼p   [✱3·22 . ✱4·13·14]
PM-VERBATIM-END PM1:✱4·15 -/

/- PM-VERBATIM-BEGIN PM1:✱4·2
✱4·2.  ⊢ . p ≡ p   [Id . ✱3·2]
PM-VERBATIM-END PM1:✱4·2 -/

/- PM-VERBATIM-BEGIN PM1:✱4·21
✱4·21.  ⊢ : p ≡ q . ≡ . q ≡ p   [✱3·22]
PM-VERBATIM-END PM1:✱4·21 -/

/- PM-VERBATIM-BEGIN PM1:✱4·22
✱4·22.  ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ r

Dem.

⊢ . ✱3·26 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ q :
[✱3·26] ⊃ . p ⊃ q   (1)
⊢ . ✱3·27 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . q ≡ r :
[✱3·26] ⊃ . q ⊃ r   (2)
⊢ . (1) . (2) . ✱2·83 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . p ⊃ r   (3)
⊢ . ✱3·27 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . q ≡ r :
[✱3·27] ⊃ . r ⊃ q   (4)
⊢ . ✱3·26 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ q :
[✱3·27] ⊃ . q ⊃ p   (5)
⊢ . (4) . (5) . ✱2·83 . ⊃ ⊢ : p ≡ q . q ≡ r . ⊃ . r ⊃ p   (6)
⊢ . (3) . (6) . Comp . ⊃ ⊢ . Prop

These propositions assert that equivalence is reflexive, symmetrical and
transitive.
PM-VERBATIM-END PM1:✱4·22 -/

/- PM-VERBATIM-BEGIN PM1:✱4·24
✱4·24.  ⊢ : p . ≡ . p . p

Dem.

⊢ . ✱3·26 . ⊃ ⊢ : p . p . ⊃ . p   (1)
⊢ . ✱3·2 . ⊃ ⊢ : p . ⊃ : p . ⊃ . p . p :
[✱2·43] ⊃ ⊢ : p . ⊃ . p . p   (2)
⊢ . (1) . (2) . ✱3·2 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·24 -/

/- PM-VERBATIM-BEGIN PM1:✱4·25
✱4·25.  ⊢ : p . ≡ . p ∨ p   [Taut . Add p/q]

Note. ✱4·24·25 are two forms of the law of tautology, which is what chiefly
distinguishes the algebra of symbolic logic from ordinary algebra.
PM-VERBATIM-END PM1:✱4·25 -/

/- PM-VERBATIM-BEGIN PM1:✱4·3
✱4·3.  ⊢ : p . q . ≡ . q . p   [✱3·22]

Note. Whenever we have, whatever values p and q may have,
φ(p,q) . ⊃ . φ(q,p), we have also φ(p,q) . ≡ . φ(q,p).
PM-VERBATIM-END PM1:✱4·3 -/

/- PM-VERBATIM-BEGIN PM1:✱4·31
✱4·31.  ⊢ : p ∨ q . ≡ . q ∨ p   [Perm]
PM-VERBATIM-END PM1:✱4·31 -/

/- PM-VERBATIM-BEGIN PM1:✱4·32
✱4·32.  ⊢ : (p . q) . r . ≡ . p . (q . r)

Dem.

⊢ . ✱4·15 . ⊃ ⊢ : p . q . ⊃ . ∼r : ≡ : q . r . ⊃ . ∼p :
[✱4·12] ⊃ : p . ⊃ . ∼(q . r)   (1)
⊢ . (1) . ✱4·11 . ⊃ ⊢ : ∼(p . q . ⊃ . ∼r) . ≡ . ∼{p . ⊃ . ∼(q . r)} :
[(✱1·01 . ✱3·01)] ⊃ ⊢ . Prop

Note. Here "(1)" stands for
⊢ : p . q . ⊃ . ∼r : ≡ : p . ⊃ . ∼(q . r), which is obtained from the
above steps by ✱4·22. The use of ✱4·22 will often be tacit, as above.
PM-VERBATIM-END PM1:✱4·32 -/

/- PM-VERBATIM-BEGIN PM1:✱4·33
✱4·33.  ⊢ : (p ∨ q) ∨ r . ≡ . p ∨ (q ∨ r)   [✱2·31·32]

The above are the associative laws for multiplication and addition.
PM-VERBATIM-END PM1:✱4·33 -/
