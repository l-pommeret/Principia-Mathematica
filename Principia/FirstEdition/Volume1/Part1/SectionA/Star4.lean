import Principia.FirstEdition.Volume1.Part1.SectionA.Star3

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
✱4·14.  ⊢ :. p . q . ⊃ . r : ≡ : p . ∼r . ⊃ . ∼q   [✱3·37 . ✱4·13]
PM-VERBATIM-END PM1:✱4·14 -/

/- PM-VERBATIM-BEGIN PM1:✱4·15
✱4·15.  ⊢ :. p . q . ⊃ . ∼r : ≡ : q . r . ⊃ . ∼p   [✱3·22 . ✱4·13·14]
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

/- PM-VERBATIM-BEGIN PM1:✱4·34
✱4·34.  p . q . r .=. (p . q) . r   Df
PM-VERBATIM-END PM1:✱4·34 -/

/-- ✱4·34: `p . q . r` abbreviates the left-associated conjunction
`(p . q) . r`. -/
def star_4_34 (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  (p ∧ₚ q) ∧ₚ r

theorem star_4_34_unfold (p q r : PM.Elementary Γ) :
    star_4_34 p q r = ((p ∧ₚ q) ∧ₚ r) := rfl

/- PM-VERBATIM-BEGIN PM1:✱4·36
✱4·36.  ⊢ :. p ≡ q . ⊃ : p . r . ≡ . q . r   [Fact . ✱3·47]
PM-VERBATIM-END PM1:✱4·36 -/

/- PM-VERBATIM-BEGIN PM1:✱4·37
✱4·37.  ⊢ :. p ≡ q . ⊃ : p ∨ r . ≡ . q ∨ r   [Sum . ✱3·47]
PM-VERBATIM-END PM1:✱4·37 -/

/- PM-VERBATIM-BEGIN PM1:✱4·38
✱4·38.  ⊢ :. p ≡ r . q ≡ s . ⊃ : p . q . ≡ . r . s   [✱3·47 . ✱4·32 . ✱3·22]
PM-VERBATIM-END PM1:✱4·38 -/

/- PM-VERBATIM-BEGIN PM1:✱4·39
✱4·39.  ⊢ :. p ≡ r . q ≡ s . ⊃ : p ∨ q . ≡ . r ∨ s   [✱3·48·47 . ✱4·32 . ✱3·22]
PM-VERBATIM-END PM1:✱4·39 -/

/- PM-VERBATIM-BEGIN PM1:✱4·4
✱4·4.  ⊢ : p . q ∨ r . ≡ : p . q . ∨ . p . r

This is the first form of the distributive law.

Dem.

⊢ . ✱3·2 . ⊃ ⊢ :: p . ⊃ : q . ⊃ . p . q : p . ⊃ : r . ⊃ . p . r ::
[Comp] ⊃ ⊢ :: p . ⊃ :. q . ⊃ . p . q : r . ⊃ . p . r :.
[✱3·48] ⊃ : q ∨ r . ⊃ : p . q . ∨ . p . r   (1)
⊢ . (1) . Imp . ⊃ ⊢ : p . q ∨ r . ⊃ : p . q . ∨ . p . r   (2)
⊢ . ✱3·26 . ⊃ ⊢ : p . q . ⊃ . p : p . r . ⊃ . p :
[✱3·44] ⊃ ⊢ : p . q . ∨ . p . r . ⊃ . p   (3)
⊢ . ✱3·27 . ⊃ ⊢ : p . q . ⊃ . q : p . r . ⊃ . r :
[✱3·48] ⊃ ⊢ : p . q . ∨ . p . r . ⊃ . q ∨ r   (4)
⊢ . (3) . (4) . Comp . ⊃ ⊢ : p . q . ∨ . p . r . ⊃ . p . q ∨ r   (5)
⊢ . (2) . (5) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·4 -/

/- PM-VERBATIM-BEGIN PM1:✱4·41
✱4·41.  ⊢ : p . ∨ . q . r . ≡ . p ∨ q . p ∨ r

This is the second form of the distributive law—a form to which there is
nothing analogous in ordinary algebra. By the conventions as to dots,
"p . ∨ . q . r" means "p ∨ (q . r)."

Dem.

⊢ . ✱3·26 . Sum . ⊃ ⊢ : p . ∨ . q . r . ⊃ . p ∨ q   (1)
⊢ . ✱3·27 . Sum . ⊃ ⊢ : p . ∨ . q . r . ⊃ . p ∨ r   (2)
⊢ . (1) . (2) . Comp . ⊃ ⊢ : p . ∨ . q . r . ⊃ . p ∨ q . p ∨ r   (3)
⊢ . ✱2·53 . ✱3·47 . ⊃ ⊢ : p ∨ q . p ∨ r . ⊃ : ∼p ⊃ q . ∼p ⊃ r :
[Comp] ⊃ : ∼p . ⊃ . q . r
[✱2·54] ⊃ : p . ∨ . q . r   (4)
⊢ . (3) . (4) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·41 -/

/- PM-VERBATIM-BEGIN PM1:✱4·42
✱4·42.  ⊢ : p . ≡ : p . q . ∨ . p . ∼q

Dem.

⊢ . ✱3·21 . ⊃ ⊢ :. q ∨ ∼q . ⊃ : p . ⊃ . p . q ∨ ∼q :
[✱2·11] ⊃ ⊢ : p . ⊃ . p . q ∨ ∼q   (1)
⊢ . ✱3·26 . ⊃ ⊢ : p . q ∨ ∼q . ⊃ . p   (2)
⊢ . (1) . (2) . ⊃ ⊢ : p . ≡ : p . q ∨ ∼q :
[✱4·4] ⊃ ⊢ : p . ≡ : p . q . ∨ . p . ∼q . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·42 -/

/- PM-VERBATIM-BEGIN PM1:✱4·43
✱4·43.  ⊢ : p . ≡ : p ∨ q . p ∨ ∼q

Dem.

⊢ . ✱2·2 . ⊃ ⊢ : p . ⊃ . p ∨ q : p . ⊃ . p ∨ ∼q :
[Comp] ⊃ ⊢ : p . ⊃ . p ∨ q . p ∨ ∼q   (1)
⊢ . ✱2·65 ∼p/p . ⊃ ⊢ :. ∼p ⊃ q . ⊃ : ∼p ⊃ ∼q . ⊃ . p :
[Imp] ⊃ ⊢ :. ∼p ⊃ q . ∼p ⊃ ∼q . ⊃ . p :
[✱2·53 . ✱3·47] ⊃ ⊢ :. p ∨ q . p ∨ ∼q . ⊃ . p   (2)
⊢ . (1) . (2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·43 -/

/- PM-VERBATIM-BEGIN PM1:✱4·44
✱4·44.  ⊢ : p . ≡ : p . ∨ . p . q

Dem.

⊢ . ✱2·2 . ⊃ ⊢ : p . ⊃ : p . ∨ . p . q   (1)
⊢ . Id . ✱3·26 . ⊃ ⊢ :. p ⊃ p : p . q . ⊃ . p :
[✱3·44] ⊃ ⊢ :. p . ∨ . p . q . ⊃ . p   (2)
⊢ . (1) . (2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·44 -/

/- PM-VERBATIM-BEGIN PM1:✱4·45
✱4·45.  ⊢ : p . ≡ . p . p ∨ q   [✱3·26 . ✱2·2]
PM-VERBATIM-END PM1:✱4·45 -/

/- PM-VERBATIM-BEGIN PM1:✱4·5
✱4·5.  ⊢ : p . q . ≡ . ∼(∼p ∨ ∼q)   [✱4·2 . (✱3·01)]
PM-VERBATIM-END PM1:✱4·5 -/

/- PM-VERBATIM-BEGIN PM1:✱4·51
✱4·51.  ⊢ : ∼(p . q) . ≡ . ∼p ∨ ∼q   [✱4·5·12]
PM-VERBATIM-END PM1:✱4·51 -/

/- PM-VERBATIM-BEGIN PM1:✱4·52
✱4·52.  ⊢ : p . ∼q . ≡ . ∼(∼p ∨ q)   [✱4·5 ∼q/q . ✱4·13]
PM-VERBATIM-END PM1:✱4·52 -/

/- PM-VERBATIM-BEGIN PM1:✱4·53
✱4·53.  ⊢ : ∼(p . ∼q) . ≡ . ∼p ∨ q   [✱4·52·12]
PM-VERBATIM-END PM1:✱4·53 -/

/- PM-VERBATIM-BEGIN PM1:✱4·54
✱4·54.  ⊢ : ∼p . q . ≡ . ∼(p ∨ ∼q)   [✱4·5 ∼p/p . ✱4·13]
PM-VERBATIM-END PM1:✱4·54 -/

/- PM-VERBATIM-BEGIN PM1:✱4·55
✱4·55.  ⊢ : ∼(∼p . q) . ≡ . p ∨ ∼q   [✱4·54·12]
PM-VERBATIM-END PM1:✱4·55 -/

/- PM-VERBATIM-BEGIN PM1:✱4·56
✱4·56.  ⊢ : ∼p . ∼q . ≡ . ∼(p ∨ q)   [✱4·54 ∼q/q . ✱4·13]
PM-VERBATIM-END PM1:✱4·56 -/

/- PM-VERBATIM-BEGIN PM1:✱4·57
✱4·57.  ⊢ : ∼(∼p . ∼q) . ≡ . p ∨ q   [✱4·56·12]
PM-VERBATIM-END PM1:✱4·57 -/

/- PM-VERBATIM-BEGIN PM1:✱4·6
✱4·6.  ⊢ : p ⊃ q . ≡ . ∼p ∨ q   [✱4·2 . (✱1·01)]
PM-VERBATIM-END PM1:✱4·6 -/

/- PM-VERBATIM-BEGIN PM1:✱4·61
✱4·61.  ⊢ : ∼(p ⊃ q) . ≡ . p . ∼q   [✱4·6·11·52]
PM-VERBATIM-END PM1:✱4·61 -/

/- PM-VERBATIM-BEGIN PM1:✱4·62
✱4·62.  ⊢ : p ⊃ ∼q . ≡ . ∼p ∨ ∼q   [✱4·6 ∼q/q]
PM-VERBATIM-END PM1:✱4·62 -/

/- PM-VERBATIM-BEGIN PM1:✱4·63
✱4·63.  ⊢ : ∼(p ⊃ ∼q) . ≡ . p . q   [✱4·62·11·5]
PM-VERBATIM-END PM1:✱4·63 -/

/- PM-VERBATIM-BEGIN PM1:✱4·64
✱4·64.  ⊢ : ∼p ⊃ q . ≡ . p ∨ q   [✱2·53·54]
PM-VERBATIM-END PM1:✱4·64 -/

/- PM-VERBATIM-BEGIN PM1:✱4·65
✱4·65.  ⊢ : ∼(∼p ⊃ q) . ≡ . ∼p . ∼q   [✱4·64·11·56]
PM-VERBATIM-END PM1:✱4·65 -/

/- PM-VERBATIM-BEGIN PM1:✱4·66
✱4·66.  ⊢ : ∼p ⊃ ∼q . ≡ . p ∨ ∼q   [✱4·64 ∼q/q]
PM-VERBATIM-END PM1:✱4·66 -/

/- PM-VERBATIM-BEGIN PM1:✱4·67
✱4·67.  ⊢ : ∼(∼p ⊃ ∼q) . ≡ . ∼p . q   [✱4·66·11·54]
PM-VERBATIM-END PM1:✱4·67 -/

/- PM-VERBATIM-BEGIN PM1:✱4·7
✱4·7.  ⊢ : p ⊃ q . ≡ : p . ⊃ . p . q

Dem.

⊢ . ✱3·27 . Syll . ⊃ ⊢ : p . ⊃ . p . q . ⊃ . p ⊃ q   (1)
⊢ . Comp . ⊃ ⊢ : p . ⊃ . p . p ⊃ q . ⊃ : p . ⊃ . p . q :
[Exp] ⊃ ⊢ :: p ⊃ p . ⊃ : p ⊃ q . ⊃ : p . ⊃ . p . q ::
[Id] ⊃ ⊢ : p ⊃ q . ⊃ : p . ⊃ . p . q   (2)
⊢ . (1) . (2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·7 -/

/- PM-VERBATIM-BEGIN PM1:✱4·71
✱4·71.  ⊢ : p ⊃ q . ≡ : p . ≡ . p . q

Dem.

⊢ . ✱3·21 . ⊃ ⊢ :: p . q . ⊃ . p : ⊃ : p . ⊃ . p . q . ⊃ : p . ≡ . p . q ::
[✱3·26] ⊃ ⊢ : p . ⊃ . p . q . ⊃ : p . ≡ . p . q   (1)
⊢ . ✱3·26 . ⊃ ⊢ : p . ≡ . p . q . ⊃ : p . ⊃ . p . q   (2)
⊢ . (1) . (2) . ⊃ ⊢ : p . ⊃ . p . q . ≡ : p . ≡ . p . q   (3)
⊢ . (3) . ✱4·7·22 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·71 -/

/- PM-VERBATIM-BEGIN PM1:✱4·72
✱4·72.  ⊢ : p ⊃ q . ≡ : q . ≡ . p ∨ q

Dem.

⊢ . ✱4·1 . ⊃ ⊢ : p ⊃ q . ≡ : ∼q ⊃ ∼p :
[✱4·71 ∼q,∼p/p,∼∼q] ≡ : ∼q . ≡ . ∼q . ∼p:
[✱4·12] ≡ : q . ≡ . ∼(∼q . ∼p):
[✱4·57] ≡ : q . ≡ . q ∨ p:
[✱4·31] ≡ : q . ≡ . p ∨ q . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·72 -/

/- PM-VERBATIM-BEGIN PM1:✱4·73
✱4·73.  ⊢ : q . ⊃ : p . ≡ . p . q   [Simp . ✱4·71]

This proposition is very useful, since it shows that a true factor may be
omitted from a product without altering its truth or falsehood, just as a true
hypothesis may be omitted from an implication.
PM-VERBATIM-END PM1:✱4·73 -/

/- PM-VERBATIM-BEGIN PM1:✱4·74
✱4·74.  ⊢ :. ∼p . ⊃ : q . ≡ . p ∨ q   [✱2·21 . ✱4·72]
PM-VERBATIM-END PM1:✱4·74 -/

/- PM-VERBATIM-BEGIN PM1:✱4·76
✱4·76.  ⊢ : p ⊃ q . p ⊃ r . ≡ : p . ⊃ . q . r   [✱4·41 ∼p/p . (✱1·01)]
PM-VERBATIM-END PM1:✱4·76 -/

/- PM-VERBATIM-BEGIN PM1:✱4·77
✱4·77.  ⊢ :. q ⊃ p . r ⊃ p . ≡ : q ∨ r . ⊃ . p   [✱3·44 . Add . ✱2·2]
PM-VERBATIM-END PM1:✱4·77 -/

/- PM-VERBATIM-BEGIN PM1:✱4·86
✱4·86.  ⊢ :. p ≡ q . ⊃ : p ≡ r . ≡ . q ≡ r   [✱4·21·22]
PM-VERBATIM-END PM1:✱4·86 -/

/- PM-VERBATIM-BEGIN PM1:✱4·87
✱4·87.  ⊢ : p . q . ⊃ . r : ≡ : p . ⊃ . q ⊃ r : ≡ : q . ⊃ . p ⊃ r : ≡ : q . p . ⊃ . r   [Exp . Comm . Imp]

✱4·87 embodies in one proposition the principles of exportation and importation and the commutative principle.
PM-VERBATIM-END PM1:✱4·87 -/

/- PM-VERBATIM-BEGIN PM1:✱4·82
✱4·82.  ⊢ : p ⊃ q . p ⊃ ∼q . ≡ . ∼p   [✱2·65 . Imp . ✱2·21 . Comp]
PM-VERBATIM-END PM1:✱4·82 -/

/- PM-VERBATIM-BEGIN PM1:✱4·83
✱4·83.  ⊢ : p ⊃ q . ∼p ⊃ q . ≡ . q   [✱2·61 . Imp . Simp . Comp]

Note. ✱4·82·83 may also be obtained from ✱4·43, of which they are virtually
other forms.
PM-VERBATIM-END PM1:✱4·83 -/

/- PM-VERBATIM-BEGIN PM1:✱4·84
✱4·84.  ⊢ :. p ≡ q . ⊃ : p ⊃ r . ≡ . q ⊃ r   [✱2·06 . ✱3·47]
PM-VERBATIM-END PM1:✱4·84 -/

/- PM-VERBATIM-BEGIN PM1:✱4·85
✱4·85.  ⊢ :. p ≡ q . ⊃ : r ⊃ p . ≡ . r ⊃ q   [✱2·05 . ✱3·47]
PM-VERBATIM-END PM1:✱4·85 -/

/- PM-VERBATIM-BEGIN PM1:✱4·78
✱4·78.  ⊢ : p ⊃ q . ∨ . p ⊃ r . ≡ : p . ⊃ . q ∨ r

Dem.

⊢ . ✱4·2 . (✱1·01) . ⊃ ⊢ : p ⊃ q . ∨ . p ⊃ r . ≡ : ∼p ∨ q . ∨ . ∼p ∨ r:
[✱4·33] ≡ . ∼p . ∨ . q ∨ ∼p ∨ r:
[✱4·31·37] ≡ : ∼p . ∨ . ∼p ∨ q ∨ r:
[✱4·33] ≡ : ∼p ∨ ∼p . ∨ . q ∨ r:
[✱4·25·37] ≡ : ∼p . ∨ . q ∨ r:
[✱4·2 . (✱1·01)] ≡ : p . ⊃ . q ∨ r . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·78 -/

/- PM-VERBATIM-BEGIN PM1:✱4·79
✱4·79.  ⊢ : q ⊃ p . ∨ . r ⊃ p . ≡ : q . r . ⊃ . p

Dem.

⊢ . ✱4·1·39 . ⊃ ⊢ : q ⊃ p . ∨ . r ⊃ p . ≡ : ∼p ⊃ ∼q . ∨ . ∼p ⊃ ∼r:
[✱4·78] ≡ : ∼p . ⊃ . ∼q ∨ ∼r:
[✱2·15] ≡ : ∼(∼q ∨ ∼r) . ⊃ . p:
[✱4·2 . (✱3·01)] ≡ : q . r . ⊃ . p . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱4·79 -/

/- PM-VERBATIM-BEGIN PM1:✱4·8
✱4·8.  ⊢ : p ⊃ ∼p . ≡ . ∼p   [✱2·01 . Simp]
PM-VERBATIM-END PM1:✱4·8 -/

/- PM-VERBATIM-BEGIN PM1:✱4·81
✱4·81.  ⊢ : ∼p ⊃ p . ≡ . p   [✱2·18 . Simp]
PM-VERBATIM-END PM1:✱4·81 -/

namespace PM.Elementary

/-- PM I (1910), p. 120, ✱4·01: equivalence is an object-language
abbreviation. -/
def equiv (p q : PM.Elementary Γ) : PM.Elementary Γ :=
  (p ⊃ₚ q) ∧ₚ (q ⊃ₚ p)

infix:53 " ≡ₚ " => equiv

/-- PM I (1910), p. 122, ✱4·02: a special three-place chain abbreviation. -/
def equivChain (p q r : PM.Elementary Γ) : PM.Elementary Γ :=
  (p ≡ₚ q) ∧ₚ (q ≡ₚ r)

/-- PM I, ✱4·87: the printed four-term chain is the left-associated product
of its three adjacent equivalences. -/
def equivChain4 (a b c d : PM.Elementary Γ) : PM.Elementary Γ :=
  ((a ≡ₚ b) ∧ₚ (b ≡ₚ c)) ∧ₚ (c ≡ₚ d)

end PM.Elementary

namespace PM.FirstEdition.Volume1.Star4

open PM
open PM.Elementary

private theorem targetJoin {Γ} {a b : PM.Elementary Γ}
    (ha : ⊢ₚ a) (hb : ⊢ₚ b) : ⊢ₚ (a ∧ₚ b) :=
  PM.Derivation.detach hb
    (PM.Derivation.detach ha
      (PM.FirstEdition.Volume1.Star3.star_3_2 a b))

private theorem targetCompose {Γ} {a b c : PM.Elementary Γ}
    (hab : ⊢ₚ (a ⊃ₚ b)) (hbc : ⊢ₚ (b ⊃ₚ c)) : ⊢ₚ (a ⊃ₚ c) :=
  PM.Derivation.detach hab
    (PM.Derivation.detach hbc
      (PM.FirstEdition.Volume1.Star2.star_2_05 a b c))

private theorem targetJoinUnder {Γ} {h a b : PM.Elementary Γ}
    (ha : ⊢ₚ (h ⊃ₚ a)) (hb : ⊢ₚ (h ⊃ₚ b)) : ⊢ₚ (h ⊃ₚ (a ∧ₚ b)) :=
  targetCompose
    (PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star3.star_3_2 h h)
      (PM.FirstEdition.Volume1.Star2.star_2_43 h (h ∧ₚ h)))
    (PM.Derivation.detach (targetJoin ha hb)
      (PM.FirstEdition.Volume1.Star3.star_3_47 h h a b))

private theorem targetEquivTrans {Γ} {a b c : PM.Elementary Γ}
    (hab : ⊢ₚ (a ≡ₚ b)) (hbc : ⊢ₚ (b ≡ₚ c)) : ⊢ₚ (a ≡ₚ c) := by
  have line1 := targetCompose
    (PM.Derivation.detach hab
      (PM.FirstEdition.Volume1.Star3.star_3_26 (a ⊃ₚ b) (b ⊃ₚ a)))
    (PM.Derivation.detach hbc
      (PM.FirstEdition.Volume1.Star3.star_3_26 (b ⊃ₚ c) (c ⊃ₚ b)))
  have line2 := targetCompose
    (PM.Derivation.detach hbc
      (PM.FirstEdition.Volume1.Star3.star_3_27 (b ⊃ₚ c) (c ⊃ₚ b)))
    (PM.Derivation.detach hab
      (PM.FirstEdition.Volume1.Star3.star_3_27 (a ⊃ₚ b) (b ⊃ₚ a)))
  exact targetJoin line1 line2

/-- Audited scope reading of ✱4·4. -/
def star_4_4_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·4.  ⊢ : p . q ∨ r . ≡ : p . q . ∨ . p . r"
  parsed := (p ∧ₚ (q ∨ₚ r)) ≡ₚ ((p ∧ₚ q) ∨ₚ (p ∧ₚ r))
  scopeReading := "The left side is p conjoined with q ∨ r; the right side disjoins p . q and p . r."

/-- ✱4·4, following PM's five numbered lines. -/
theorem star_4_4 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ (q ∨ₚ r)) ≡ₚ ((p ∧ₚ q) ∨ₚ (p ∧ₚ r))) := by
  have line1 : ⊢ₚ (p ⊃ₚ ((q ∨ₚ r) ⊃ₚ ((p ∧ₚ q) ∨ₚ (p ∧ₚ r)))) :=
    targetCompose
      (targetJoinUnder
        (PM.FirstEdition.Volume1.Star3.star_3_2 p q)
        (PM.FirstEdition.Volume1.Star3.star_3_2 p r))
      (PM.FirstEdition.Volume1.Star3.star_3_48 q r (p ∧ₚ q) (p ∧ₚ r))
  have line2 : ⊢ₚ ((p ∧ₚ (q ∨ₚ r)) ⊃ₚ ((p ∧ₚ q) ∨ₚ (p ∧ₚ r))) :=
    PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star3.star_3_31 p (q ∨ₚ r)
        ((p ∧ₚ q) ∨ₚ (p ∧ₚ r)))
  have line3 : ⊢ₚ (((p ∧ₚ q) ∨ₚ (p ∧ₚ r)) ⊃ₚ p) :=
    PM.Derivation.detach
      (targetJoin
        (PM.FirstEdition.Volume1.Star3.star_3_26 p q)
        (PM.FirstEdition.Volume1.Star3.star_3_26 p r))
      (PM.FirstEdition.Volume1.Star3.star_3_44 p (p ∧ₚ q) (p ∧ₚ r))
  have line4 : ⊢ₚ (((p ∧ₚ q) ∨ₚ (p ∧ₚ r)) ⊃ₚ (q ∨ₚ r)) :=
    PM.Derivation.detach
      (targetJoin
        (targetCompose (PM.FirstEdition.Volume1.Star3.star_3_27 p q)
          (PM.FirstEdition.Volume1.Star2.star_2_2 q r))
        (targetCompose (PM.FirstEdition.Volume1.Star3.star_3_27 p r)
          (PM.Derivation.star_1_3 q r)))
      (PM.FirstEdition.Volume1.Star3.star_3_44 (q ∨ₚ r) (p ∧ₚ q) (p ∧ₚ r))
  have line5 : ⊢ₚ (((p ∧ₚ q) ∨ₚ (p ∧ₚ r)) ⊃ₚ (p ∧ₚ (q ∨ₚ r))) :=
    targetJoinUnder line3 line4
  exact targetJoin line2 line5

/-- Audited scope reading of ✱4·44. -/
def star_4_44_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·44.  ⊢ : p . ≡ : p . ∨ . p . q"
  parsed := p ≡ₚ (p ∨ₚ (p ∧ₚ q))
  scopeReading := "The outer equivalence relates p to the disjunction of p and p . q."

/-- ✱4·44, following PM's two numbered lines. -/
theorem star_4_44 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (p ≡ₚ (p ∨ₚ (p ∧ₚ q))) := by
  have line1 : ⊢ₚ (p ⊃ₚ (p ∨ₚ (p ∧ₚ q))) :=
    PM.FirstEdition.Volume1.Star2.star_2_2 p (p ∧ₚ q)
  have line2 : ⊢ₚ ((p ∨ₚ (p ∧ₚ q)) ⊃ₚ p) :=
    PM.Derivation.detach
      (targetJoin (PM.FirstEdition.Volume1.Star2.star_2_08 p)
        (PM.FirstEdition.Volume1.Star3.star_3_26 p q))
      (PM.FirstEdition.Volume1.Star3.star_3_44 p p (p ∧ₚ q))
  exact targetJoin line1 line2

/-- Audited scope reading of ✱4·51. -/
def star_4_51_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·51.  ⊢ : ∼(p . q) . ≡ . ∼p ∨ ∼q"
  parsed := (∼ₚ (p ∧ₚ q)) ≡ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))
  scopeReading := "Negation scopes over p . q; the right side is the disjunction ∼p ∨ ∼q."

/-- ✱4·51, the ✱4·5/✱4·12 double-negation conversion. -/
theorem star_4_51 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ∧ₚ q)) ≡ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) := by
  let x := (∼ₚ p) ∨ₚ (∼ₚ q)
  have line1 : ⊢ₚ (x ≡ₚ ∼ₚ (∼ₚ x)) :=
    targetJoin
      (PM.FirstEdition.Volume1.Star2.star_2_12 x)
      (PM.FirstEdition.Volume1.Star2.star_2_14 x)
  exact PM.Derivation.detach line1
    (PM.FirstEdition.Volume1.Star3.star_3_22
      (((∼ₚ p) ∨ₚ (∼ₚ q)) ⊃ₚ ∼ₚ (p ∧ₚ q))
      ((∼ₚ (p ∧ₚ q)) ⊃ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))))

/-- Audited scope reading of ✱4·71. -/
def star_4_71_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·71.  ⊢ : p ⊃ q . ≡ : p . ≡ . p . q"
  parsed := (p ⊃ₚ q) ≡ₚ (p ≡ₚ (p ∧ₚ q))
  scopeReading := "The implication p ⊃ q is equivalent to p ≡ p . q."

/-- ✱4·71, following PM's three numbered lines and the final ✱4·7/✱4·22 step. -/
theorem star_4_71 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ≡ₚ (p ≡ₚ (p ∧ₚ q))) := by
  let a := p ⊃ₚ (p ∧ₚ q)
  have line1 : ⊢ₚ (a ⊃ₚ (p ≡ₚ (p ∧ₚ q))) :=
    targetJoinUnder (PM.FirstEdition.Volume1.Star2.star_2_08 a)
      (PM.FirstEdition.Volume1.Star2.star_2_02 a
        ((p ∧ₚ q) ⊃ₚ p) |> fun h =>
          PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_26 p q) h)
  have line2 : ⊢ₚ ((p ≡ₚ (p ∧ₚ q)) ⊃ₚ a) :=
    PM.FirstEdition.Volume1.Star3.star_3_26 a ((p ∧ₚ q) ⊃ₚ p)
  have line3 : ⊢ₚ (a ≡ₚ (p ≡ₚ (p ∧ₚ q))) := targetJoin line1 line2
  have line4 : ⊢ₚ ((p ⊃ₚ q) ≡ₚ a) := by
    have forward := PM.Derivation.detach
      (PM.FirstEdition.Volume1.Star3.star_3_2 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_77 p q (p ∧ₚ q))
    have backward := targetCompose
      (PM.FirstEdition.Volume1.Star2.star_2_08 a)
      (PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_27 p q)
        (PM.FirstEdition.Volume1.Star2.star_2_05 p (p ∧ₚ q) q))
    exact targetJoin forward backward
  exact targetEquivTrans line4 line3

/-- Audited scope reading of ✱4·72. -/
def star_4_72_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·72.  ⊢ : p ⊃ q . ≡ : q . ≡ . p ∨ q"
  parsed := (p ⊃ₚ q) ≡ₚ (q ≡ₚ (p ∨ₚ q))
  scopeReading := "The implication p ⊃ q is equivalent to q ≡ p ∨ q."

/-- ✱4·72, the printed transposition chain compressed into its two directions. -/
theorem star_4_72 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ≡ₚ (q ≡ₚ (p ∨ₚ q))) := by
  let a := p ⊃ₚ q
  have line1 : ⊢ₚ (a ⊃ₚ (q ⊃ₚ (p ∨ₚ q))) :=
    PM.FirstEdition.Volume1.Star2.star_2_02 a (q ⊃ₚ (p ∨ₚ q)) |>
      PM.Derivation.detach (PM.Derivation.star_1_3 p q)
  have line2base : ⊢ₚ (a ⊃ₚ ((p ∨ₚ q) ⊃ₚ q)) :=
    targetCompose
      (targetJoinUnder (PM.FirstEdition.Volume1.Star2.star_2_08 a)
        (PM.FirstEdition.Volume1.Star2.star_2_02 a (q ⊃ₚ q) |>
          PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_08 q)))
      (PM.FirstEdition.Volume1.Star3.star_3_44 q p q)
  have line2 : ⊢ₚ (a ⊃ₚ ((p ∨ₚ q) ⊃ₚ q)) := line2base
  have line3 : ⊢ₚ (a ⊃ₚ (q ≡ₚ (p ∨ₚ q))) := targetJoinUnder line1 line2
  have line4 : ⊢ₚ ((q ≡ₚ (p ∨ₚ q)) ⊃ₚ a) :=
    targetCompose
      (PM.FirstEdition.Volume1.Star3.star_3_27
        (q ⊃ₚ (p ∨ₚ q)) ((p ∨ₚ q) ⊃ₚ q))
      (PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_2 p q)
        (PM.FirstEdition.Volume1.Star2.star_2_06 p (p ∨ₚ q) q))
  exact targetJoin line3 line4

/-- Audited scope reading of ✱4·1. -/
def star_4_1_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ⊃ q . ≡ . ∼q ⊃ ∼p"
  parsed := (p ⊃ₚ q) ≡ₚ (∼ₚ q ⊃ₚ ∼ₚ p)
  scopeReading := "The dots group the two implications as the sides of the equivalence."

/-- PM I (1910), p. 120, ✱4·1.  The two uses of the primitive inference are
the documented closed/nonempty-context branches. -/
theorem star_4_1 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ≡ₚ (∼ₚ q ⊃ₚ ∼ₚ p)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_17 p q)
    (infer
      (PM.FirstEdition.Volume1.Star2.star_2_16 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p)) ((∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q))))

/-- Audited scope reading of ✱4·12. -/
def star_4_12_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ≡ ∼q . ≡ . q ≡ ∼p"
  parsed := (p ≡ₚ (∼ₚ q)) ≡ₚ (q ≡ₚ (∼ₚ p))
  scopeReading := "The dots make p ≡ ∼q and q ≡ ∼p the two sides of the outer equivalence."

/-- PM I (1910), p. 122, ✱4·12.  The two packaging calls and the primitive
inference branches are the documented non-printed additions for this locus. -/
theorem star_4_12 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ (∼ₚ q)) ≡ₚ (q ≡ₚ (∼ₚ p))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have a₁ := PM.FirstEdition.Volume1.Star2.star_2_03 p q
  have a₂ := PM.FirstEdition.Volume1.Star2.star_2_15 q p
  have haPair :=
    infer a₂ (infer a₁
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ ∼ₚ p)) ((∼ₚ q ⊃ₚ p) ⊃ₚ (∼ₚ p ⊃ₚ q))))
  have hFwd :=
    infer haPair
      (PM.FirstEdition.Volume1.Star3.star_3_47
        (p ⊃ₚ ∼ₚ q) (∼ₚ q ⊃ₚ p) (q ⊃ₚ ∼ₚ p) (∼ₚ p ⊃ₚ q))
  have b₁ := PM.FirstEdition.Volume1.Star2.star_2_03 q p
  have b₂ := PM.FirstEdition.Volume1.Star2.star_2_15 p q
  have hbPair :=
    infer b₂ (infer b₁
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ ∼ₚ q)) ((∼ₚ p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ p))))
  have hBwd :=
    infer hbPair
      (PM.FirstEdition.Volume1.Star3.star_3_47
        (q ⊃ₚ ∼ₚ p) (∼ₚ p ⊃ₚ q) (p ⊃ₚ ∼ₚ q) (∼ₚ q ⊃ₚ p))
  exact infer hBwd (infer hFwd
    (PM.FirstEdition.Volume1.Star3.star_3_2
      ((p ≡ₚ (∼ₚ q)) ⊃ₚ (q ≡ₚ (∼ₚ p))) ((q ≡ₚ (∼ₚ p)) ⊃ₚ (p ≡ₚ (∼ₚ q)))))

/-- Audited scope reading of ✱4·13. -/
def star_4_13_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . p ≡ ∼(∼p)"
  parsed := p ≡ₚ (∼ₚ (∼ₚ p))
  scopeReading := "The assertion sign governs the equivalence of p with its double negation."

/-- PM I (1910), p. 121, ✱4·13.  The primitive-inference branches and ✱3·2
are the documented additions required to package the printed citations. -/
theorem star_4_13 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ (p ≡ₚ (∼ₚ (∼ₚ p))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_14 p)
    (infer
      (PM.FirstEdition.Volume1.Star2.star_2_12 p)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        (p ⊃ₚ ∼ₚ (∼ₚ p)) (∼ₚ (∼ₚ p) ⊃ₚ p)))

/-- Audited scope reading of ✱4·2. -/
def star_4_2_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ . p ≡ p"
  parsed := p ≡ₚ p
  scopeReading := "The assertion sign governs the reflexive equivalence p ≡ p."

/-- PM I (1910), p. 121, ✱4·2.  Both components of the defined equivalence
are Id; ✱3·2 supplies their logical product. -/
theorem star_4_2 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ (p ≡ₚ p) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer
    (PM.FirstEdition.Volume1.Star2.star_2_08 p)
    (infer
      (PM.FirstEdition.Volume1.Star2.star_2_08 p)
      (PM.FirstEdition.Volume1.Star3.star_3_2 (p ⊃ₚ p) (p ⊃ₚ p)))

/-- Audited scope reading of ✱4·11. -/
def star_4_11_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ≡ q . ≡ . ∼p ≡ ∼q"
  parsed := (p ≡ₚ q) ≡ₚ ((∼ₚ p) ≡ₚ (∼ₚ q))
  scopeReading := "The dots group p ≡ q and ∼p ≡ ∼q as the sides of the outer equivalence."

/-- PM I (1910), p. 120, ✱4·11.  Equivalence is the ✱4·01 abbreviation;
the proof transports its two implication components by ✱2·16/·17, uses
✱3·47 to adjoin them, and ✱3·22 only to restore the printed component order. -/
theorem star_4_11 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ≡ₚ ((∼ₚ p) ≡ₚ (∼ₚ q))) := by
  have forwardLinks : ⊢ₚ (((p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p)) ∧ₚ
      ((q ⊃ₚ p) ⊃ₚ (∼ₚ p ⊃ₚ ∼ₚ q))) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_16 q p)
      (PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_16 p q)
        (PM.FirstEdition.Volume1.Star3.star_3_2
          ((p ⊃ₚ q) ⊃ₚ (∼ₚ q ⊃ₚ ∼ₚ p))
          ((q ⊃ₚ p) ⊃ₚ (∼ₚ p ⊃ₚ ∼ₚ q))))
  have forwardRaw : ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((∼ₚ q ⊃ₚ ∼ₚ p) ∧ₚ (∼ₚ p ⊃ₚ ∼ₚ q))) :=
    PM.Derivation.detach forwardLinks
      (PM.FirstEdition.Volume1.Star3.star_3_47
        (p ⊃ₚ q) (q ⊃ₚ p) (∼ₚ q ⊃ₚ ∼ₚ p) (∼ₚ p ⊃ₚ ∼ₚ q))
  have forward : ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((∼ₚ p) ≡ₚ (∼ₚ q))) :=
    PM.Derivation.detach forwardRaw
      (PM.Derivation.detach
        (PM.FirstEdition.Volume1.Star3.star_3_22
          (∼ₚ q ⊃ₚ ∼ₚ p) (∼ₚ p ⊃ₚ ∼ₚ q))
        (PM.FirstEdition.Volume1.Star2.star_2_05
          (p ≡ₚ q) ((∼ₚ q ⊃ₚ ∼ₚ p) ∧ₚ (∼ₚ p ⊃ₚ ∼ₚ q))
          ((∼ₚ p ⊃ₚ ∼ₚ q) ∧ₚ (∼ₚ q ⊃ₚ ∼ₚ p))))
  have backwardLinks : ⊢ₚ (((∼ₚ p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ p)) ∧ₚ
      ((∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q))) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_17 p q)
      (PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_17 q p)
        (PM.FirstEdition.Volume1.Star3.star_3_2
          ((∼ₚ p ⊃ₚ ∼ₚ q) ⊃ₚ (q ⊃ₚ p))
          ((∼ₚ q ⊃ₚ ∼ₚ p) ⊃ₚ (p ⊃ₚ q))))
  have backwardRaw : ⊢ₚ (((∼ₚ p) ≡ₚ (∼ₚ q)) ⊃ₚ ((q ⊃ₚ p) ∧ₚ (p ⊃ₚ q))) :=
    PM.Derivation.detach backwardLinks
      (PM.FirstEdition.Volume1.Star3.star_3_47
        (∼ₚ p ⊃ₚ ∼ₚ q) (∼ₚ q ⊃ₚ ∼ₚ p) (q ⊃ₚ p) (p ⊃ₚ q))
  have backward : ⊢ₚ (((∼ₚ p) ≡ₚ (∼ₚ q)) ⊃ₚ (p ≡ₚ q)) :=
    PM.Derivation.detach backwardRaw
      (PM.Derivation.detach
        (PM.FirstEdition.Volume1.Star3.star_3_22 (q ⊃ₚ p) (p ⊃ₚ q))
        (PM.FirstEdition.Volume1.Star2.star_2_05
          ((∼ₚ p) ≡ₚ (∼ₚ q)) ((q ⊃ₚ p) ∧ₚ (p ⊃ₚ q))
          ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ p))))
  exact PM.Derivation.detach backward
    (PM.Derivation.detach forward
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ≡ₚ q) ⊃ₚ ((∼ₚ p) ≡ₚ (∼ₚ q)))
        (((∼ₚ p) ≡ₚ (∼ₚ q)) ⊃ₚ (p ≡ₚ q))))

/-- Audited scope reading of ✱4·77. -/
def star_4_77_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·77.  ⊢ :. q ⊃ p . r ⊃ p . ≡ : q ∨ r . ⊃ . p"
  parsed := ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)) ≡ₚ ((q ∨ₚ r) ⊃ₚ p)
  scopeReading := "The juxtaposed left clauses form a conjunction; q ∨ r is the antecedent of the right implication."

/-- PM I (1910), p. 127, ✱4·77. -/
theorem star_4_77 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)) ≡ₚ ((q ∨ₚ r) ⊃ₚ p)) := by
  let d := q ∨ₚ r
  let g := d ⊃ₚ p
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have hq : ⊢ₚ (q ⊃ₚ d) := PM.FirstEdition.Volume1.Star2.star_2_2 q r
  have hr : ⊢ₚ (r ⊃ₚ d) := compose
    (PM.FirstEdition.Volume1.Star2.star_2_2 r q)
    (PM.Derivation.star_1_4 r q)
  have liftUnder : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) →
      (⊢ₚ (g ⊃ₚ (a ⊃ₚ b))) → (⊢ₚ (g ⊃ₚ b)) := by
    intro a b ha hgab
    have hga : ⊢ₚ (g ⊃ₚ a) := infer ha (PM.FirstEdition.Volume1.Star2.star_2_02 g a)
    have lifted : ⊢ₚ ((g ⊃ₚ a) ⊃ₚ (g ⊃ₚ b)) :=
      infer hgab (PM.FirstEdition.Volume1.Star2.star_2_77 g a b)
    exact infer hga lifted
  have qBranch : ⊢ₚ (g ⊃ₚ (q ⊃ₚ p)) :=
    liftUnder hq (PM.FirstEdition.Volume1.Star2.star_2_05 q d p)
  have rBranch : ⊢ₚ (g ⊃ₚ (r ⊃ₚ p)) :=
    liftUnder hr (PM.FirstEdition.Volume1.Star2.star_2_05 r d p)
  have pair := infer rBranch (infer qBranch
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (g ⊃ₚ (q ⊃ₚ p)) (g ⊃ₚ (r ⊃ₚ p))))
  have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 g g (q ⊃ₚ p) (r ⊃ₚ p))
  have dup := infer (PM.FirstEdition.Volume1.Star3.star_3_2 g g) (PM.FirstEdition.Volume1.Star2.star_2_43 g (g ∧ₚ g))
  have reverse : ⊢ₚ (g ⊃ₚ ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p))) := compose dup lift
  exact infer reverse
    (infer (PM.FirstEdition.Volume1.Star3.star_3_44 p q r)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        (((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)) ⊃ₚ g)
        (g ⊃ₚ ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ p)))))

/-- Audited scope reading of ✱4·8. -/
def star_4_8_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·8.  ⊢ : p ⊃ ∼p . ≡ . ∼p"
  parsed := (p ⊃ₚ (∼ₚ p)) ≡ₚ (∼ₚ p)
  scopeReading := "The dots make p ⊃ ∼p the left side and ∼p the right side of the equivalence."

/-- PM I (1910), p. 127, ✱4·8. -/
theorem star_4_8 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ (∼ₚ p)) ≡ₚ (∼ₚ p)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer (PM.FirstEdition.Volume1.Star2.star_2_02 p (∼ₚ p))
    (infer (PM.FirstEdition.Volume1.Star2.star_2_01 p)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ⊃ₚ (∼ₚ p)) ⊃ₚ (∼ₚ p))
        ((∼ₚ p) ⊃ₚ (p ⊃ₚ (∼ₚ p)))))

/-- Audited scope reading of ✱4·81. -/
def star_4_81_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·81.  ⊢ : ∼p ⊃ p . ≡ . p"
  parsed := ((∼ₚ p) ⊃ₚ p) ≡ₚ p
  scopeReading := "The dots delimit ∼p ⊃ p as the left side of the equivalence and p as the right side."

/-- PM I (1910), p. 127, ✱4·81. -/
theorem star_4_81 {Γ} (p : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ p) ⊃ₚ p) ≡ₚ p) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  exact infer (PM.FirstEdition.Volume1.Star2.star_2_02 (∼ₚ p) p)
    (infer (PM.FirstEdition.Volume1.Star2.star_2_18 p)
      (PM.FirstEdition.Volume1.Star3.star_3_2
        (((∼ₚ p) ⊃ₚ p) ⊃ₚ p)
        (p ⊃ₚ ((∼ₚ p) ⊃ₚ p))))

/-- Audited scope reading of ✱4·36. -/
def star_4_36_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·36.  ⊢ :. p ≡ q . ⊃ : p . r . ≡ . q . r"
  parsed := (p ≡ₚ q) ⊃ₚ ((p ∧ₚ r) ≡ₚ (q ∧ₚ r))
  scopeReading := "The first equivalence is the antecedent; the consequent equates the two conjunctions."

/-- PM I (1910), p. 124, ✱4·36. -/
theorem star_4_36 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((p ∧ₚ r) ≡ₚ (q ∧ₚ r))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have dup : ∀ a : PM.Elementary Γ, ⊢ₚ (a ⊃ₚ (a ∧ₚ a)) := by
    intro a
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 a a) (PM.FirstEdition.Volume1.Star2.star_2_43 a (a ∧ₚ a))
  have lift : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair := infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact compose (dup a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  let e := p ≡ₚ q
  have idr : ⊢ₚ (r ⊃ₚ r) := PM.FirstEdition.Volume1.Star2.star_2_08 r
  have er : ⊢ₚ (e ⊃ₚ (r ⊃ₚ r)) := infer idr (PM.FirstEdition.Volume1.Star2.star_2_02 e (r ⊃ₚ r))
  have f := compose (lift (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p)) er) (PM.FirstEdition.Volume1.Star3.star_3_47 p r q r)
  have b := compose (lift (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p)) er) (PM.FirstEdition.Volume1.Star3.star_3_47 q r p r)
  exact lift f b

/-- Audited scope reading of ✱4·7. -/
def star_4_7_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·7.  ⊢ : p ⊃ q . ≡ : p . ⊃ . p . q"
  parsed := (p ⊃ₚ q) ≡ₚ (p ⊃ₚ (p ∧ₚ q))
  scopeReading := "The outer dots separate the equivalence; on the right, p is antecedent and p . q is consequent."

/-- PM I (1910), p. 126, ✱4·7.  The forward direction is the exact
✱2·77 lifting of ✱3·2; the reverse direction projects `q` from the
conjunctive consequent and composes conditionals. -/
theorem star_4_7 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ⊃ₚ q) ≡ₚ (p ⊃ₚ (p ∧ₚ q))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have forward : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ (p ∧ₚ q))) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_2 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_77 p q (p ∧ₚ q))
  have backward : ⊢ₚ ((p ⊃ₚ (p ∧ₚ q)) ⊃ₚ (p ⊃ₚ q)) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_27 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_05 p (p ∧ₚ q) q)
  exact infer backward
    (infer forward
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ⊃ₚ q) ⊃ₚ (p ⊃ₚ (p ∧ₚ q)))
        ((p ⊃ₚ (p ∧ₚ q)) ⊃ₚ (p ⊃ₚ q))))

/-- Audited scope reading of ✱4·86. -/
def star_4_86_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ :. p ≡ q . ⊃ : p ≡ r . ≡ . q ≡ r"
  parsed := (p ≡ₚ q) ⊃ₚ ((p ≡ₚ r) ≡ₚ (q ≡ₚ r))
  scopeReading := "The equivalence p ≡ q is the antecedent; the consequent equates p ≡ r with q ≡ r."

/-- PM I (1910), p. 127, ✱4·86.  Under `p ≡ q`, composition transports
both implication components of `p ≡ r` to those of `q ≡ r`, and conversely.
The two transported directions are then packaged by the definition ✱4·01. -/
theorem star_4_86 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((p ≡ₚ r) ≡ₚ (q ≡ₚ r))) := by
  let e := p ≡ₚ q
  let a := p ≡ₚ r
  let b := q ≡ₚ r
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ},
      (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) →
      (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw
      (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have underCompose : ∀ {u v w x : PM.Elementary Γ},
      (⊢ₚ (u ⊃ₚ (v ⊃ₚ w))) → (⊢ₚ (u ⊃ₚ (w ⊃ₚ x))) →
      (⊢ₚ (u ⊃ₚ (v ⊃ₚ x))) := by
    intro u v w x hvw hwx
    exact infer hwx
      (infer hvw (PM.FirstEdition.Volume1.Star2.star_2_83 u v w x))
  have forward : ⊢ₚ (e ⊃ₚ (a ⊃ₚ b)) := by
    let x := e ∧ₚ a
    have xe : ⊢ₚ (x ⊃ₚ e) := PM.FirstEdition.Volume1.Star3.star_3_26 e a
    have xa : ⊢ₚ (x ⊃ₚ a) := PM.FirstEdition.Volume1.Star3.star_3_27 e a
    have xqp := compose xe
      (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p))
    have xpq := compose xe
      (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p))
    have xpr := compose xa
      (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ r) (r ⊃ₚ p))
    have xrp := compose xa
      (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ r) (r ⊃ₚ p))
    have xqr : ⊢ₚ (x ⊃ₚ (q ⊃ₚ r)) := underCompose xqp xpr
    have xrq : ⊢ₚ (x ⊃ₚ (r ⊃ₚ q)) := underCompose xrp xpq
    exact infer (join xqr xrq)
      (PM.FirstEdition.Volume1.Star3.star_3_3 e a b)
  have backward : ⊢ₚ (e ⊃ₚ (b ⊃ₚ a)) := by
    let x := e ∧ₚ b
    have xe : ⊢ₚ (x ⊃ₚ e) := PM.FirstEdition.Volume1.Star3.star_3_26 e b
    have xb : ⊢ₚ (x ⊃ₚ b) := PM.FirstEdition.Volume1.Star3.star_3_27 e b
    have xpq := compose xe
      (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p))
    have xqp := compose xe
      (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p))
    have xqr := compose xb
      (PM.FirstEdition.Volume1.Star3.star_3_26 (q ⊃ₚ r) (r ⊃ₚ q))
    have xrq := compose xb
      (PM.FirstEdition.Volume1.Star3.star_3_27 (q ⊃ₚ r) (r ⊃ₚ q))
    have xpr : ⊢ₚ (x ⊃ₚ (p ⊃ₚ r)) := underCompose xpq xqr
    have xrp : ⊢ₚ (x ⊃ₚ (r ⊃ₚ p)) := underCompose xrq xqp
    exact infer (join xpr xrp)
      (PM.FirstEdition.Volume1.Star3.star_3_3 e b a)
  exact join forward backward

/-- Audited scope reading of ✱4·87. -/
def star_4_87_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·87.  ⊢ : p . q . ⊃ . r : ≡ : p . ⊃ . q ⊃ r : ≡ : q . ⊃ . p ⊃ r : ≡ : q . p . ⊃ . r"
  parsed := equivChain4 ((p ∧ₚ q) ⊃ₚ r) (p ⊃ₚ (q ⊃ₚ r))
    (q ⊃ₚ (p ⊃ₚ r)) ((q ∧ₚ p) ⊃ₚ r)
  scopeReading := "The colons separate a four-term equivalence chain, with dots grouping each conjunction or implication."

/-- PM I (1910), p. 128, ✱4·87. -/
theorem star_4_87 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (equivChain4 ((p ∧ₚ q) ⊃ₚ r) (p ⊃ₚ (q ⊃ₚ r))
      (q ⊃ₚ (p ⊃ₚ r)) ((q ∧ₚ p) ⊃ₚ r)) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have pair : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B)) := by
    intro A B hA hB
    exact infer hB (infer hA (PM.FirstEdition.Volume1.Star3.star_3_2 A B))
  have e1 : ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ≡ₚ (p ⊃ₚ (q ⊃ₚ r))) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_31 p q r)
      (infer (PM.FirstEdition.Volume1.Star3.star_3_3 p q r)
        (PM.FirstEdition.Volume1.Star3.star_3_2
          (((p ∧ₚ q) ⊃ₚ r) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r)))
          ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r))))
  have e2 : ⊢ₚ ((p ⊃ₚ (q ⊃ₚ r)) ≡ₚ (q ⊃ₚ (p ⊃ₚ r))) :=
    infer (PM.FirstEdition.Volume1.Star2.star_2_04 q p r)
      (infer (PM.FirstEdition.Volume1.Star2.star_2_04 p q r)
        (PM.FirstEdition.Volume1.Star3.star_3_2
          ((p ⊃ₚ (q ⊃ₚ r)) ⊃ₚ (q ⊃ₚ (p ⊃ₚ r)))
          ((q ⊃ₚ (p ⊃ₚ r)) ⊃ₚ (p ⊃ₚ (q ⊃ₚ r)))))
  have e3 : ⊢ₚ ((q ⊃ₚ (p ⊃ₚ r)) ≡ₚ ((q ∧ₚ p) ⊃ₚ r)) :=
    infer (PM.FirstEdition.Volume1.Star3.star_3_3 q p r)
      (infer (PM.FirstEdition.Volume1.Star3.star_3_31 q p r)
        (PM.FirstEdition.Volume1.Star3.star_3_2
          ((q ⊃ₚ (p ⊃ₚ r)) ⊃ₚ ((q ∧ₚ p) ⊃ₚ r))
          (((q ∧ₚ p) ⊃ₚ r) ⊃ₚ (q ⊃ₚ (p ⊃ₚ r)))))
  exact pair (pair e1 e2) e3


/-- Audited scope reading of ✱4·37. -/
def star_4_37_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·37.  ⊢ :. p ≡ q . ⊃ : p ∨ r . ≡ . q ∨ r"
  parsed := (p ≡ₚ q) ⊃ₚ ((p ∨ₚ r) ≡ₚ (q ∨ₚ r))
  scopeReading := "The first equivalence is the antecedent; the consequent equates the two disjunctions."

/-- PM I (1910), p. 124, ✱4·37. -/
theorem star_4_37 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((p ∨ₚ r) ≡ₚ (q ∨ₚ r))) := by
  let e := p ≡ₚ q
  let a := p ∨ₚ r
  let b := q ∨ₚ r
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t) (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have idr : ⊢ₚ (r ⊃ₚ r) := PM.FirstEdition.Volume1.Star2.star_2_08 r
  have er : ⊢ₚ (e ⊃ₚ (r ⊃ₚ r)) := infer idr (PM.FirstEdition.Volume1.Star2.star_2_02 e (r ⊃ₚ r))
  have forward := compose (join (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p)) er)
    (PM.FirstEdition.Volume1.Star3.star_3_48 p r q r)
  have backward := compose (join (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p)) er)
    (PM.FirstEdition.Volume1.Star3.star_3_48 q r p r)
  exact join forward backward

/-- Audited scope reading of ✱4·74. -/
def star_4_74_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·74.  ⊢ :. ∼p . ⊃ : q . ≡ . p ∨ q"
  parsed := (∼ₚ p) ⊃ₚ (q ≡ₚ (p ∨ₚ q))
  scopeReading := "The negation ∼p is the antecedent; the consequent is the equivalence of q and p ∨ q."

/-- PM I (1910), p. 127, ✱4·74.  This expands the printed
`✱2·21 . ✱4·72` chain at its exact hypothesis `∼p`: addition supplies
one direction and ✱2·55 supplies the other. -/
theorem star_4_74 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ p) ⊃ₚ (q ≡ₚ (p ∨ₚ q))) := by
  let h := ∼ₚ p
  let a := q ⊃ₚ (p ∨ₚ q)
  let b := (p ∨ₚ q) ⊃ₚ q
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC; exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t; exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t) (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forward0 : ⊢ₚ a := compose (PM.FirstEdition.Volume1.Star2.star_2_2 q p) (PM.Derivation.star_1_4 q p)
  have forward : ⊢ₚ (h ⊃ₚ a) := infer forward0 (PM.FirstEdition.Volume1.Star2.star_2_02 h a)
  have backward : ⊢ₚ (h ⊃ₚ b) := PM.FirstEdition.Volume1.Star2.star_2_55 p q
  exact join forward backward

/-- Audited scope reading of ✱4·64. -/
def star_4_64_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·64.  ⊢ : ∼∼∼p ⊃ q . ≡ . p ∨ q"
  parsed := ((∼ₚ (∼ₚ (∼ₚ p))) ⊃ₚ q) ≡ₚ (p ∨ₚ q)
  scopeReading := "The dots delimit the triple-negation implication as the left side and p ∨ q as the right side."

/-- PM I (1910), p. 126, ✱4·64. -/
theorem star_4_64 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((∼ₚ (∼ₚ (∼ₚ p))) ⊃ₚ q) ≡ₚ (p ∨ₚ q)) := by
  let t := ∼ₚ (∼ₚ (∼ₚ p))
  let a := t ⊃ₚ q
  let b := p ∨ₚ q
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have aToNot : ⊢ₚ (a ⊃ₚ ((∼ₚ p) ⊃ₚ q)) := by
    have base := PM.FirstEdition.Volume1.Star2.star_2_05 (∼ₚ p) t q
    have reorder := infer base (PM.FirstEdition.Volume1.Star2.star_2_04 a ((∼ₚ p) ⊃ₚ t) ((∼ₚ p) ⊃ₚ q))
    exact infer (PM.FirstEdition.Volume1.Star2.star_2_12 (∼ₚ p)) reorder
  have aToB : ⊢ₚ (a ⊃ₚ b) := comp aToNot (PM.FirstEdition.Volume1.Star2.star_2_54 p q)
  have bToNot : ⊢ₚ (b ⊃ₚ ((∼ₚ p) ⊃ₚ q)) := PM.FirstEdition.Volume1.Star2.star_2_53 p q
  have liftT : ⊢ₚ (b ⊃ₚ (t ⊃ₚ (∼ₚ p))) :=
    infer (PM.FirstEdition.Volume1.Star2.star_2_14 (∼ₚ p))
      (PM.FirstEdition.Volume1.Star2.star_2_02 b (t ⊃ₚ (∼ₚ p)))
  have bToCompose : ⊢ₚ (b ⊃ₚ ((t ⊃ₚ (∼ₚ p)) ⊃ₚ (t ⊃ₚ q))) := by
    have base := PM.FirstEdition.Volume1.Star2.star_2_77 t (∼ₚ p) q
    have pre : ⊢ₚ (((∼ₚ p) ⊃ₚ q) ⊃ₚ (t ⊃ₚ ((∼ₚ p) ⊃ₚ q))) := PM.FirstEdition.Volume1.Star2.star_2_02 t ((∼ₚ p) ⊃ₚ q)
    have base' := comp pre base
    have addBase : ⊢ₚ (b ⊃ₚ (((∼ₚ p) ⊃ₚ q) ⊃ₚ ((t ⊃ₚ (∼ₚ p)) ⊃ₚ (t ⊃ₚ q)))) :=
      infer base' (PM.FirstEdition.Volume1.Star2.star_2_02 b (((∼ₚ p) ⊃ₚ q) ⊃ₚ ((t ⊃ₚ (∼ₚ p)) ⊃ₚ (t ⊃ₚ q))))
    exact infer bToNot (infer addBase (PM.FirstEdition.Volume1.Star2.star_2_77 b ((∼ₚ p) ⊃ₚ q) ((t ⊃ₚ (∼ₚ p)) ⊃ₚ (t ⊃ₚ q))))
  have bToA : ⊢ₚ (b ⊃ₚ a) := by
    have liftCompose := infer bToCompose (PM.FirstEdition.Volume1.Star2.star_2_77 b (t ⊃ₚ (∼ₚ p)) (t ⊃ₚ q))
    exact infer liftT liftCompose
  exact infer bToA (infer aToB (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- Audited scope reading of ✱4·82. -/
def star_4_82_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·82.  ⊢ : p ⊃ q . p ⊃ ∼q . ≡ . ∼p"
  parsed := ((p ⊃ₚ q) ∧ₚ (p ⊃ₚ (∼ₚ q))) ≡ₚ (∼ₚ p)
  scopeReading := "The left side conjoins the two implications from p to q and ∼q; the right side is ∼p."

/-- PM I (1910), p. 127, ✱4·82.  The forward direction is the printed
`✱2·65 . Imp` route; the converse applies ✱2·21 twice and packages the
two consequences exactly as the product required by `Comp`.

✱4·82 and ✱4·83 are virtually other forms of ✱4·43. -/
theorem star_4_82 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ (∼ₚ q))) ≡ₚ (∼ₚ p)) := by
  let e := (p ⊃ₚ q) ∧ₚ (p ⊃ₚ (∼ₚ q))
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) →
      (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw
      (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forward : ⊢ₚ (e ⊃ₚ (∼ₚ p)) :=
    infer (PM.FirstEdition.Volume1.Star2.star_2_65 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_31 (p ⊃ₚ q) (p ⊃ₚ (∼ₚ q)) (∼ₚ p))
  have backward : ⊢ₚ ((∼ₚ p) ⊃ₚ e) :=
    join (PM.FirstEdition.Volume1.Star2.star_2_21 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_21 p (∼ₚ q))
  exact infer backward
    (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2
      (e ⊃ₚ (∼ₚ p)) ((∼ₚ p) ⊃ₚ e)))

/-- Audited scope reading of ✱4·83. -/
def star_4_83_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·83.  ⊢ : p ⊃ q . ∼p ⊃ q . ≡ . q"
  parsed := ((p ⊃ₚ q) ∧ₚ ((∼ₚ p) ⊃ₚ q)) ≡ₚ q
  scopeReading := "The left side conjoins the implications to q from p and from ∼p; the right side is q."

/-- PM I (1910), p. 127, ✱4·83.  `Imp` applies ✱2·61 to the
product of its two premises; the converse is the two constant implications
from `q`, packaged by the same canonical `Comp` closure as ✱4·82.

✱4·82 and ✱4·83 are virtually other forms of ✱4·43. -/
theorem star_4_83 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ ((∼ₚ p) ⊃ₚ q)) ≡ₚ q) := by
  let e := (p ⊃ₚ q) ∧ₚ ((∼ₚ p) ⊃ₚ q)
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) →
      (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw
      (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have forward : ⊢ₚ (e ⊃ₚ q) :=
    infer (PM.FirstEdition.Volume1.Star2.star_2_61 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_31 (p ⊃ₚ q) ((∼ₚ p) ⊃ₚ q) q)
  have backward : ⊢ₚ (q ⊃ₚ e) :=
    join (PM.FirstEdition.Volume1.Star2.star_2_02 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_02 (∼ₚ p) q)
  exact infer backward
    (infer forward
      (PM.FirstEdition.Volume1.Star3.star_3_2 (e ⊃ₚ q) (q ⊃ₚ e)))

/-- Audited scope reading of ✱4·84. -/
def star_4_84_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·84.  ⊢ :. p ≡ q . ⊃ : p ⊃ r . ≡ . q ⊃ r"
  parsed := (p ≡ₚ q) ⊃ₚ ((p ⊃ₚ r) ≡ₚ (q ⊃ₚ r))
  scopeReading := "The equivalence p ≡ q is the antecedent; the consequent equates the two implications to r."

/-- PM I (1910), p. 127, ✱4·84.  The two instances of ✱2·06 transport
the consequent along the corresponding components of `p ≡ q`; ✱3·47
packages those implications under their exact common hypothesis. -/
theorem star_4_84 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((p ⊃ₚ r) ≡ₚ (q ⊃ₚ r))) := by
  let e := p ≡ₚ q
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) →
      (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw
      (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u)
      (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have pToQ : ⊢ₚ (e ⊃ₚ (p ⊃ₚ q)) :=
    PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p)
  have qToP : ⊢ₚ (e ⊃ₚ (q ⊃ₚ p)) :=
    PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p)
  have forward : ⊢ₚ (e ⊃ₚ ((p ⊃ₚ r) ⊃ₚ (q ⊃ₚ r))) :=
    compose qToP (PM.FirstEdition.Volume1.Star2.star_2_06 q p r)
  have backward : ⊢ₚ (e ⊃ₚ ((q ⊃ₚ r) ⊃ₚ (p ⊃ₚ r))) :=
    compose pToQ (PM.FirstEdition.Volume1.Star2.star_2_06 p q r)
  exact join forward backward

/-- Audited scope reading of ✱4·85. -/
def star_4_85_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·85.  ⊢ :. p ≡ q . ⊃ : r ⊃ p . ≡ . r ⊃ q   [✱2·05 . ✱3·47]"
  parsed := (p ≡ₚ q) ⊃ₚ ((r ⊃ₚ p) ≡ₚ (r ⊃ₚ q))
  scopeReading := "The equivalence p ≡ q is the antecedent; the consequent equates the two implications with antecedent r."

/-- PM I (1910), p. 127, ✱4·85.  The two directions are obtained by
lifting the corresponding component of `p ≡ q` below the common antecedent
`r`; `✱3·47` then packages them under the equivalence hypothesis. -/
theorem star_4_85 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ⊃ₚ ((r ⊃ₚ p) ≡ₚ (r ⊃ₚ q))) := by
  let e := p ≡ₚ q
  let a := r ⊃ₚ p
  let b := r ⊃ₚ q
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ t : PM.Elementary Γ, ⊢ₚ (t ⊃ₚ (t ∧ₚ t)) := by
    intro t
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 t t)
      (PM.FirstEdition.Volume1.Star2.star_2_43 t (t ∧ₚ t))
  have join : ∀ {u v w : PM.Elementary Γ}, (⊢ₚ (u ⊃ₚ v)) → (⊢ₚ (u ⊃ₚ w)) → (⊢ₚ (u ⊃ₚ (v ∧ₚ w))) := by
    intro u v w huv huw
    have pair := infer huw (infer huv (PM.FirstEdition.Volume1.Star3.star_3_2 (u ⊃ₚ v) (u ⊃ₚ w)))
    exact compose (duplicate u) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 u u v w))
  have epq : ⊢ₚ (e ⊃ₚ (p ⊃ₚ q)) :=
    PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p)
  have eqp : ⊢ₚ (e ⊃ₚ (q ⊃ₚ p)) :=
    PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p)
  have liftForward : ⊢ₚ (e ⊃ₚ (r ⊃ₚ (p ⊃ₚ q))) :=
    compose epq (PM.FirstEdition.Volume1.Star2.star_2_02 r (p ⊃ₚ q))
  have liftBackward : ⊢ₚ (e ⊃ₚ (r ⊃ₚ (q ⊃ₚ p))) :=
    compose eqp (PM.FirstEdition.Volume1.Star2.star_2_02 r (q ⊃ₚ p))
  have forward : ⊢ₚ (e ⊃ₚ (a ⊃ₚ b)) :=
    compose liftForward (PM.FirstEdition.Volume1.Star2.star_2_77 r p q)
  have backward : ⊢ₚ (e ⊃ₚ (b ⊃ₚ a)) :=
    compose liftBackward (PM.FirstEdition.Volume1.Star2.star_2_77 r q p)
  exact join forward backward

/-- Audited scope reading of ✱4·73. -/
def star_4_73_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·73.  ⊢ : q . ⊃ : p . ≡ . p . q   [Simp . ✱4·71]"
  parsed := q ⊃ₚ (p ≡ₚ (p ∧ₚ q))
  scopeReading := "The proposition q is the antecedent; the consequent equates p with the conjunction p . q."

/-- PM I (1910), p. 127, ✱4·73.  Under the true factor `q`, ✱3·21
adjoins it to `p`, while the lifted first projection removes it again. -/
theorem star_4_73 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ (q ⊃ₚ (p ≡ₚ (p ∧ₚ q))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have compose : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have line1 : ⊢ₚ (q ⊃ₚ (p ⊃ₚ q)) :=
    PM.FirstEdition.Volume1.Star2.star_2_02 p q
  have line2 : ⊢ₚ ((p ⊃ₚ q) ⊃ₚ (p ≡ₚ (p ∧ₚ q))) :=
    infer (star_4_71 p q)
      (PM.FirstEdition.Volume1.Star3.star_3_26
        ((p ⊃ₚ q) ⊃ₚ (p ≡ₚ (p ∧ₚ q)))
        ((p ≡ₚ (p ∧ₚ q)) ⊃ₚ (p ⊃ₚ q)))
  exact compose line1 line2

/-- Audited scope reading of ✱4·38. -/
def star_4_38_reading (p q r s : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·38.  ⊢ :. p ≡ r . q ≡ s . ⊃ : p . q . ≡ . r . s"
  parsed := ((p ≡ₚ r) ∧ₚ (q ≡ₚ s)) ⊃ₚ ((p ∧ₚ q) ≡ₚ (r ∧ₚ s))
  scopeReading := "The two initial equivalences form a conjunctive antecedent; the consequent equates the two conjunctions."

/-- PM I (1910), p. 124, ✱4·38. -/
theorem star_4_38 {Γ} (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ≡ₚ r) ∧ₚ (q ≡ₚ s)) ⊃ₚ ((p ∧ₚ q) ≡ₚ (r ∧ₚ s))) := by
  let h := (p ≡ₚ r) ∧ₚ (q ≡ₚ s)
  have infer : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) → (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ b) := by
    intro a b ha hab; match Γ, a, b, ha, hab with
    | [], _, _, ha, hab => exact PM.Derivation.star_1_1 ha hab
    | (τ :: Δ), _, _, ha, hab => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) ha hab
  have comp : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (b ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ c)) := by
    intro a b c hab hbc; exact infer hab (infer hbc (PM.FirstEdition.Volume1.Star2.star_2_05 a b c))
  have dup : ∀ a : PM.Elementary Γ, ⊢ₚ (a ⊃ₚ (a ∧ₚ a)) := by
    intro a; exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 a a) (PM.FirstEdition.Volume1.Star2.star_2_43 a (a ∧ₚ a))
  have join : ∀ {a b c : PM.Elementary Γ}, (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ (a ⊃ₚ c)) → (⊢ₚ (a ⊃ₚ (b ∧ₚ c))) := by
    intro a b c hab hac
    have pair := infer hac (infer hab (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact comp (dup a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  have hp := PM.FirstEdition.Volume1.Star3.star_3_26 (p ≡ₚ r) (q ≡ₚ s)
  have hq := PM.FirstEdition.Volume1.Star3.star_3_27 (p ≡ₚ r) (q ≡ₚ s)
  have hpr := comp hp (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ r) (r ⊃ₚ p))
  have hrp := comp hp (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ r) (r ⊃ₚ p))
  have hqs := comp hq (PM.FirstEdition.Volume1.Star3.star_3_26 (q ⊃ₚ s) (s ⊃ₚ q))
  have hsq := comp hq (PM.FirstEdition.Volume1.Star3.star_3_27 (q ⊃ₚ s) (s ⊃ₚ q))
  have forward := comp (join hpr hqs) (PM.FirstEdition.Volume1.Star3.star_3_47 p q r s)
  have backward := comp (join hrp hsq) (PM.FirstEdition.Volume1.Star3.star_3_47 r s p q)
  exact join forward backward

/-- Audited scope reading of ✱4·76. -/
def star_4_76_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·76.  ⊢ : p ⊃ q . p ⊃ r . ≡ : p . ⊃ . q . r"
  parsed := ((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ∧ₚ r))
  scopeReading := "The two left implications form a conjunction; on the right, p implies the conjunction q . r."

/-- PM I (1910), p. 127, ✱4·76. -/
theorem star_4_76 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∧ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ∧ₚ r))) := by
  let a := (p ⊃ₚ q) ∧ₚ (p ⊃ₚ r); let b := p ⊃ₚ (q ∧ₚ r)
  have infer : ∀ {x y : PM.Elementary Γ}, (⊢ₚ x) → (⊢ₚ (x ⊃ₚ y)) → (⊢ₚ y) := by
    intro x y hx hxy; match Γ, x, y, hx, hxy with
    | [], _, _, hx, hxy => exact PM.Derivation.star_1_1 hx hxy
    | (τ :: Δ), _, _, hx, hxy => exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hx hxy
  have comp : ∀ {x y z : PM.Elementary Γ}, (⊢ₚ (x ⊃ₚ y)) → (⊢ₚ (y ⊃ₚ z)) → (⊢ₚ (x ⊃ₚ z)) := by
    intro x y z hxy hyz; exact infer hxy (infer hyz (PM.FirstEdition.Volume1.Star2.star_2_05 x y z))
  have forward : ⊢ₚ (a ⊃ₚ b) := by
    have duplicate := infer (PM.FirstEdition.Volume1.Star3.star_3_2 p p)
      (PM.FirstEdition.Volume1.Star2.star_2_43 p (p ∧ₚ p))
    have underA := infer duplicate (PM.FirstEdition.Volume1.Star2.star_2_02 a (p ⊃ₚ (p ∧ₚ p)))
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_47 p p q r)
      (infer underA (PM.FirstEdition.Volume1.Star2.star_2_83 a p (p ∧ₚ p) (q ∧ₚ r)))
  have backward : ⊢ₚ (b ⊃ₚ a) := by
    have bb : ⊢ₚ (b ⊃ₚ b) := PM.FirstEdition.Volume1.Star2.star_2_08 b
    have qpart : ⊢ₚ (b ⊃ₚ (p ⊃ₚ q)) :=
      infer (infer (PM.FirstEdition.Volume1.Star3.star_3_26 q r) (PM.FirstEdition.Volume1.Star2.star_2_02 b ((q ∧ₚ r) ⊃ₚ q)))
        (infer bb (PM.FirstEdition.Volume1.Star2.star_2_83 b p (q ∧ₚ r) q))
    have rpart : ⊢ₚ (b ⊃ₚ (p ⊃ₚ r)) :=
      infer (infer (PM.FirstEdition.Volume1.Star3.star_3_27 q r) (PM.FirstEdition.Volume1.Star2.star_2_02 b ((q ∧ₚ r) ⊃ₚ r)))
        (infer bb (PM.FirstEdition.Volume1.Star2.star_2_83 b p (q ∧ₚ r) r))
    have pair := infer rpart (infer qpart (PM.FirstEdition.Volume1.Star3.star_3_2 (b ⊃ₚ (p ⊃ₚ q)) (b ⊃ₚ (p ⊃ₚ r))))
    have lift := infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 b b (p ⊃ₚ q) (p ⊃ₚ r))
    have dupb := infer (PM.FirstEdition.Volume1.Star3.star_3_2 b b) (PM.FirstEdition.Volume1.Star2.star_2_43 b (b ∧ₚ b))
    exact comp dupb lift
  exact infer backward (infer forward (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (b ⊃ₚ a)))

/-- Audited scope reading of ✱4·21. -/
def star_4_21_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ≡ q . ≡ . q ≡ p"
  parsed := (p ≡ₚ q) ≡ₚ (q ≡ₚ p)
  scopeReading := "The outer equivalence relates p ≡ q to the same equivalence with its terms reversed."

/-- PM I (1910), p. 121, ✱4·21.  This is exactly the commutation of the
two implication factors supplied by ✱3·22, in both directions. -/
theorem star_4_21 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ≡ₚ q) ≡ₚ (q ≡ₚ p)) := by
  have infer : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) → (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ b) := by
    intro a b ha hab
    match Γ, a, b, ha, hab with
    | [], _, _, ha, hab => exact PM.Derivation.star_1_1 ha hab
    | (τ :: Δ), _, _, ha, hab =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) ha hab
  exact infer
    (PM.FirstEdition.Volume1.Star3.star_3_22 (q ⊃ₚ p) (p ⊃ₚ q))
    (infer
      (PM.FirstEdition.Volume1.Star3.star_3_22 (p ⊃ₚ q) (q ⊃ₚ p))
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ≡ₚ q) ⊃ₚ (q ≡ₚ p)) ((q ≡ₚ p) ⊃ₚ (p ≡ₚ q))))

/-- Audited scope reading of ✱4·63. -/
def star_4_63_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·63.  ⊢ : ∼∼∼(p ⊃ ∼q) . ≡ . p . q"
  parsed := (∼ₚ (p ⊃ₚ (∼ₚ q))) ≡ₚ (p ∧ₚ q)
  scopeReading := "The left side is the printed negated implication after PM's abbreviations unfold; the right side is p . q."

/-- PM I (1910), p. 126, ✱4·63.  Both sides unfold to the same elementary
proposition, so ✱4·2 supplies the required reflexive equivalence. -/
theorem star_4_63 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ⊃ₚ (∼ₚ q))) ≡ₚ (p ∧ₚ q)) :=
  star_4_2 (p ∧ₚ q)

/-- Audited scope reading of ✱4·65. -/
def star_4_65_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·65.  ⊢ : ∼∼∼(∼p ⊃ q) . ≡ . ∼p . ∼q"
  parsed := (∼ₚ ((∼ₚ p) ⊃ₚ q)) ≡ₚ ((∼ₚ p) ∧ₚ (∼ₚ q))
  scopeReading := "The left side is the printed negated implication after PM's abbreviations unfold; the right side is ∼p . ∼q."

/-- PM I (1910), p. 126, ✱4·65.  Double negation transports the first
disjunct by ✱4·37; ✱4·11 then transports that equivalence through negation. -/
theorem star_4_65 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ ((∼ₚ p) ⊃ₚ q)) ≡ₚ ((∼ₚ p) ∧ₚ (∼ₚ q))) := by
  have infer : ∀ {a b : PM.Elementary Γ}, (⊢ₚ a) → (⊢ₚ (a ⊃ₚ b)) → (⊢ₚ b) := by
    intro a b ha hab
    match Γ, a, b, ha, hab with
    | [], _, _, ha, hab => exact PM.Derivation.star_1_1 ha hab
    | (τ :: Δ), _, _, ha, hab =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) ha hab
  have qForward : ⊢ₚ (q ⊃ₚ (∼ₚ (∼ₚ q))) :=
    infer (star_4_13 q)
      (PM.FirstEdition.Volume1.Star3.star_3_26
        (q ⊃ₚ (∼ₚ (∼ₚ q))) ((∼ₚ (∼ₚ q)) ⊃ₚ q))
  have qBackward : ⊢ₚ ((∼ₚ (∼ₚ q)) ⊃ₚ q) :=
    infer (star_4_13 q)
      (PM.FirstEdition.Volume1.Star3.star_3_27
        (q ⊃ₚ (∼ₚ (∼ₚ q))) ((∼ₚ (∼ₚ q)) ⊃ₚ q))
  have idp : ⊢ₚ ((∼ₚ (∼ₚ p)) ⊃ₚ (∼ₚ (∼ₚ p))) :=
    PM.FirstEdition.Volume1.Star2.star_2_08 (∼ₚ (∼ₚ p))
  have pairForward := infer qForward
    (infer idp (PM.FirstEdition.Volume1.Star3.star_3_2
      ((∼ₚ (∼ₚ p)) ⊃ₚ (∼ₚ (∼ₚ p))) (q ⊃ₚ (∼ₚ (∼ₚ q)))))
  have pairBackward := infer qBackward
    (infer idp (PM.FirstEdition.Volume1.Star3.star_3_2
      ((∼ₚ (∼ₚ p)) ⊃ₚ (∼ₚ (∼ₚ p))) ((∼ₚ (∼ₚ q)) ⊃ₚ q)))
  have forward := infer pairForward
    (PM.FirstEdition.Volume1.Star3.star_3_48
      (∼ₚ (∼ₚ p)) q (∼ₚ (∼ₚ p)) (∼ₚ (∼ₚ q)))
  have backward := infer pairBackward
    (PM.FirstEdition.Volume1.Star3.star_3_48
      (∼ₚ (∼ₚ p)) (∼ₚ (∼ₚ q)) (∼ₚ (∼ₚ p)) q)
  have disjEq := infer backward (infer forward
    (PM.FirstEdition.Volume1.Star3.star_3_2
      (((∼ₚ (∼ₚ p)) ∨ₚ q) ⊃ₚ ((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q))))
      (((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q))) ⊃ₚ ((∼ₚ (∼ₚ p)) ∨ₚ q))))
  have negForward := infer (star_4_11
      ((∼ₚ (∼ₚ p)) ∨ₚ q) ((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q))))
      (PM.FirstEdition.Volume1.Star3.star_3_26
        ((((∼ₚ (∼ₚ p)) ∨ₚ q) ≡ₚ ((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q)))) ⊃ₚ
          ((∼ₚ ((∼ₚ (∼ₚ p)) ∨ₚ q)) ≡ₚ
            (∼ₚ ((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q))))))
        (((∼ₚ ((∼ₚ (∼ₚ p)) ∨ₚ q)) ≡ₚ
            (∼ₚ ((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q))))) ⊃ₚ
          (((∼ₚ (∼ₚ p)) ∨ₚ q) ≡ₚ ((∼ₚ (∼ₚ p)) ∨ₚ (∼ₚ (∼ₚ q))))))
  exact infer disjEq negForward

/-- Audited scope reading of ✱4·24. -/
def star_4_24_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . ≡ . p . p"
  parsed := p ≡ₚ (p ∧ₚ p)
  scopeReading := "The dots make p and p . p the two sides of the equivalence."

theorem star_4_24 {Γ} (p : PM.Elementary Γ) : ⊢ₚ (p ≡ₚ (p ∧ₚ p)) := by
  have line1 : ⊢ₚ ((p ∧ₚ p) ⊃ₚ p) := PM.FirstEdition.Volume1.Star3.star_3_26 p p
  have line2 : ⊢ₚ (p ⊃ₚ (p ∧ₚ p)) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_2 p p)
      (PM.FirstEdition.Volume1.Star2.star_2_43 p (p ∧ₚ p))
  exact PM.Derivation.detach line1
    (PM.Derivation.detach line2
      (PM.FirstEdition.Volume1.Star3.star_3_2 (p ⊃ₚ (p ∧ₚ p)) ((p ∧ₚ p) ⊃ₚ p)))

/-- Audited scope reading of ✱4·25. -/
def star_4_25_reading (p : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p . ≡ . p ∨ p"
  parsed := p ≡ₚ (p ∨ₚ p)
  scopeReading := "The dots make p and p ∨ p the two sides of the equivalence."

theorem star_4_25 {Γ} (p : PM.Elementary Γ) : ⊢ₚ (p ≡ₚ (p ∨ₚ p)) := by
  have line1 : ⊢ₚ ((p ∨ₚ p) ⊃ₚ p) := PM.Derivation.Taut p
  have line2 : ⊢ₚ (p ⊃ₚ (p ∨ₚ p)) := PM.Derivation.Add p p
  exact PM.Derivation.detach line1
    (PM.Derivation.detach line2
      (PM.FirstEdition.Volume1.Star3.star_3_2 (p ⊃ₚ (p ∨ₚ p)) ((p ∨ₚ p) ⊃ₚ p)))

/-- Audited scope reading of ✱4·31. -/
def star_4_31_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : p ∨ q . ≡ . q ∨ p"
  parsed := (p ∨ₚ q) ≡ₚ (q ∨ₚ p)
  scopeReading := "The dots separate the two permuted disjunctions."

theorem star_4_31 {Γ} (p q : PM.Elementary Γ) : ⊢ₚ ((p ∨ₚ q) ≡ₚ (q ∨ₚ p)) := by
  have line1 : ⊢ₚ ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) := PM.Derivation.Perm p q
  have line2 : ⊢ₚ ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q)) := PM.Derivation.Perm q p
  exact PM.Derivation.detach line2
    (PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star3.star_3_2
        ((p ∨ₚ q) ⊃ₚ (q ∨ₚ p)) ((q ∨ₚ p) ⊃ₚ (p ∨ₚ q))))

/-- Audited scope reading of ✱4·33. -/
def star_4_33_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "⊢ : (p ∨ q) ∨ r . ≡ . p ∨ (q ∨ r)"
  parsed := ((p ∨ₚ q) ∨ₚ r) ≡ₚ (p ∨ₚ (q ∨ₚ r))
  scopeReading := "The dots separate the left- and right-associated disjunctions."

theorem star_4_33 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ≡ₚ (p ∨ₚ (q ∨ₚ r))) := by
  have line1 : ⊢ₚ (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r))) :=
    PM.FirstEdition.Volume1.Star2.star_2_32 p q r
  have line2 : ⊢ₚ ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r)) :=
    PM.FirstEdition.Volume1.Star2.star_2_31 p q r
  exact PM.Derivation.detach line2
    (PM.Derivation.detach line1
      (PM.FirstEdition.Volume1.Star3.star_3_2
        (((p ∨ₚ q) ∨ₚ r) ⊃ₚ (p ∨ₚ (q ∨ₚ r)))
        ((p ∨ₚ (q ∨ₚ r)) ⊃ₚ ((p ∨ₚ q) ∨ₚ r))))


open PM.FirstEdition.Volume1.Star1 PM.FirstEdition.Volume1.Star2 PM.FirstEdition.Volume1.Star3
/-- ✱4·22. `⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ r`.
  [✱3·26 . ✱3·27 . ✱3·2 . ✱3·47 . ✱3·33 . ✱3·22 . ✱2·06 . ✱3·43 . (✱4·01)] -/
theorem star_4_22 (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ≡ₚ q) ∧ₚ (q ≡ₚ r)) ⊃ₚ (p ≡ₚ r)) :=
  let zz := (p ≡ₚ q) ∧ₚ (q ≡ₚ r)
  -- `⊢ : p ≡ q . q ≡ r . ⊃ . p ⊃ q . q ⊃ r`, whence `⊢ : p ≡ q . q ≡ r . ⊃ . p ⊃ r`
  let z1 : ⊢ₚ (zz ⊃ₚ ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_26 (q ⊃ₚ r) (r ⊃ₚ q)) (PM.Derivation.detach (star_3_26 (p ⊃ₚ q) (q ⊃ₚ p))
        (star_3_2 ((p ≡ₚ q) ⊃ₚ (p ⊃ₚ q)) ((q ≡ₚ r) ⊃ₚ (q ⊃ₚ r)))))
      (star_3_47 (p ≡ₚ q) (q ≡ₚ r) (p ⊃ₚ q) (q ⊃ₚ r))
  let zA : ⊢ₚ (zz ⊃ₚ (p ⊃ₚ r)) :=
    PM.Derivation.detach (star_3_33 p q r) (PM.Derivation.detach z1
      (star_2_06 zz ((p ⊃ₚ q) ∧ₚ (q ⊃ₚ r)) (p ⊃ₚ r)))
  -- and, by the second halves, `⊢ : p ≡ q . q ≡ r . ⊃ . r ⊃ p`
  let w1 : ⊢ₚ (zz ⊃ₚ ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ q))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_27 (q ⊃ₚ r) (r ⊃ₚ q)) (PM.Derivation.detach (star_3_27 (p ⊃ₚ q) (q ⊃ₚ p))
        (star_3_2 ((p ≡ₚ q) ⊃ₚ (q ⊃ₚ p)) ((q ≡ₚ r) ⊃ₚ (r ⊃ₚ q)))))
      (star_3_47 (p ≡ₚ q) (q ≡ₚ r) (q ⊃ₚ p) (r ⊃ₚ q))
  let w2 : ⊢ₚ (zz ⊃ₚ ((r ⊃ₚ q) ∧ₚ (q ⊃ₚ p))) :=
    PM.Derivation.detach (star_3_22 (q ⊃ₚ p) (r ⊃ₚ q)) (PM.Derivation.detach w1
      (star_2_06 zz ((q ⊃ₚ p) ∧ₚ (r ⊃ₚ q)) ((r ⊃ₚ q) ∧ₚ (q ⊃ₚ p))))
  let zB : ⊢ₚ (zz ⊃ₚ (r ⊃ₚ p)) :=
    PM.Derivation.detach (star_3_33 r q p) (PM.Derivation.detach w2
      (star_2_06 zz ((r ⊃ₚ q) ∧ₚ (q ⊃ₚ p)) (r ⊃ₚ p)))
  PM.Derivation.detach (PM.Derivation.detach zB (PM.Derivation.detach zA (star_3_2 (zz ⊃ₚ (p ⊃ₚ r)) (zz ⊃ₚ (r ⊃ₚ p)))))
    (star_3_43 zz (p ⊃ₚ r) (r ⊃ₚ p))
/-- Audited scope reading of ✱4·22. -/
def star_4_22_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·22.  ⊢ : p ≡ q . q ≡ r . ⊃ . p ≡ r"
  parsed := ((p ≡ₚ q) ∧ₚ (q ≡ₚ r)) ⊃ₚ (p ≡ₚ r)
  scopeReading := "The antecedent conjoins p ≡ q and q ≡ r; the consequent is p ≡ r."
theorem star_4_14 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ r) ≡ₚ ((p ∧ₚ ∼ₚ r) ⊃ₚ ∼ₚ q)) := by
  have syll : ∀ A B C : PM.Elementary Γ, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) :=
    fun A B C h₁ h₂ =>
      PM.Derivation.detach h₁
        (PM.Derivation.detach h₂
          (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have adj : ∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B)) :=
    fun A B hA hB => PM.Derivation.detach hB
      (PM.Derivation.detach hA
        (PM.FirstEdition.Volume1.Star3.star_3_2 A B))
  have star_3_37 : ∀ a b c : PM.Elementary Γ,
      ⊢ₚ (((a ∧ₚ b) ⊃ₚ c) ⊃ₚ ((a ∧ₚ (∼ₚ c)) ⊃ₚ (∼ₚ b))) := by
    intro a b c
    have s1 : ⊢ₚ (((a ∧ₚ b) ⊃ₚ c) ⊃ₚ ((∼ₚ a ∨ₚ ∼ₚ b) ∨ₚ c)) :=
      PM.Derivation.detach
        (PM.FirstEdition.Volume1.Star2.star_2_14 (∼ₚ a ∨ₚ ∼ₚ b))
        (PM.FirstEdition.Volume1.Star2.star_2_38 c
          (∼ₚ (∼ₚ (∼ₚ a ∨ₚ ∼ₚ b))) (∼ₚ a ∨ₚ ∼ₚ b))
    have s2 : ⊢ₚ (((∼ₚ a ∨ₚ ∼ₚ b) ∨ₚ c) ⊃ₚ (a ⊃ₚ (b ⊃ₚ c))) :=
      PM.FirstEdition.Volume1.Star2.star_2_32 (∼ₚ a) (∼ₚ b) c
    have exp : ⊢ₚ (((a ∧ₚ b) ⊃ₚ c) ⊃ₚ (a ⊃ₚ (b ⊃ₚ c))) :=
      syll _ _ _ s1 s2
    have transp :
        ⊢ₚ ((a ⊃ₚ (b ⊃ₚ c)) ⊃ₚ (a ⊃ₚ (∼ₚ c ⊃ₚ ∼ₚ b))) :=
      PM.Derivation.detach (PM.FirstEdition.Volume1.Star2.star_2_16 b c)
        (PM.FirstEdition.Volume1.Star2.star_2_05
          a (b ⊃ₚ c) (∼ₚ c ⊃ₚ ∼ₚ b))
    have imp31 :
        ⊢ₚ ((a ⊃ₚ (∼ₚ c ⊃ₚ ∼ₚ b)) ⊃ₚ
          ((a ∧ₚ ∼ₚ c) ⊃ₚ ∼ₚ b)) :=
      PM.FirstEdition.Volume1.Star3.star_3_31 a (∼ₚ c) (∼ₚ b)
    exact syll _ _ _ (syll _ _ _ exp transp) imp31
  have hq : ⊢ₚ (q ⊃ₚ ∼ₚ (∼ₚ q)) :=
    PM.Derivation.detach (star_4_13 q)
      (PM.FirstEdition.Volume1.Star3.star_3_26
        (q ⊃ₚ ∼ₚ (∼ₚ q)) (∼ₚ (∼ₚ q) ⊃ₚ q))
  have hr : ⊢ₚ (∼ₚ (∼ₚ r) ⊃ₚ r) :=
    PM.Derivation.detach (star_4_13 r)
      (PM.FirstEdition.Volume1.Star3.star_3_27
        (r ⊃ₚ ∼ₚ (∼ₚ r)) (∼ₚ (∼ₚ r) ⊃ₚ r))
  have hA : ⊢ₚ ((p ∧ₚ q) ⊃ₚ (p ∧ₚ ∼ₚ (∼ₚ q))) :=
    syll _ _ _ (PM.FirstEdition.Volume1.Star3.star_3_22 p q)
      (syll _ _ _
        (PM.Derivation.detach hq
          (PM.FirstEdition.Volume1.Star3.star_3_45 q (∼ₚ (∼ₚ q)) p))
        (PM.FirstEdition.Volume1.Star3.star_3_22 (∼ₚ (∼ₚ q)) p))
  have step1 :
      ⊢ₚ (((p ∧ₚ ∼ₚ r) ⊃ₚ ∼ₚ q) ⊃ₚ
        ((p ∧ₚ ∼ₚ (∼ₚ q)) ⊃ₚ ∼ₚ (∼ₚ r))) :=
    star_3_37 p (∼ₚ r) (∼ₚ q)
  have u1 :
      ⊢ₚ (((p ∧ₚ ∼ₚ (∼ₚ q)) ⊃ₚ ∼ₚ (∼ₚ r)) ⊃ₚ
        ((p ∧ₚ q) ⊃ₚ ∼ₚ (∼ₚ r))) :=
    PM.Derivation.detach hA
      (PM.FirstEdition.Volume1.Star2.star_2_06
        (p ∧ₚ q) (p ∧ₚ ∼ₚ (∼ₚ q)) (∼ₚ (∼ₚ r)))
  have u2 :
      ⊢ₚ (((p ∧ₚ q) ⊃ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ((p ∧ₚ q) ⊃ₚ r)) :=
    PM.Derivation.detach hr
      (PM.FirstEdition.Volume1.Star2.star_2_05
        (p ∧ₚ q) (∼ₚ (∼ₚ r)) r)
  exact adj _ _ (star_3_37 p q r)
    (syll _ _ _ step1 (syll _ _ _ u1 u2))
theorem star_4_15 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ∧ₚ q) ⊃ₚ ∼ₚ r) ≡ₚ ((q ∧ₚ r) ⊃ₚ ∼ₚ p)) := by
  have syll : ∀ A B C : PM.Elementary Γ, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) :=
    fun A B C h₁ h₂ =>
      PM.Derivation.detach h₁
        (PM.Derivation.detach h₂
          (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have adj : ∀ A B : PM.Elementary Γ, (⊢ₚ A) → (⊢ₚ B) → (⊢ₚ (A ∧ₚ B)) :=
    fun A B hA hB => PM.Derivation.detach hB
      (PM.Derivation.detach hA
        (PM.FirstEdition.Volume1.Star3.star_3_2 A B))
  have h14 :
      ⊢ₚ ((((q ∧ₚ p) ⊃ₚ ∼ₚ r) ⊃ₚ
          ((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ∼ₚ p)) ∧ₚ
        (((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ∼ₚ p) ⊃ₚ
          ((q ∧ₚ p) ⊃ₚ ∼ₚ r))) :=
    star_4_14 q p (∼ₚ r)
  have hBC :
      ⊢ₚ (((q ∧ₚ p) ⊃ₚ ∼ₚ r) ⊃ₚ
        ((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ∼ₚ p)) :=
    PM.Derivation.detach h14
      (PM.FirstEdition.Volume1.Star3.star_3_26 _ _)
  have hCB :
      ⊢ₚ (((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ∼ₚ p) ⊃ₚ
        ((q ∧ₚ p) ⊃ₚ ∼ₚ r)) :=
    PM.Derivation.detach h14
      (PM.FirstEdition.Volume1.Star3.star_3_27 _ _)
  have hr : ⊢ₚ (r ⊃ₚ ∼ₚ (∼ₚ r)) :=
    PM.Derivation.detach (star_4_13 r)
      (PM.FirstEdition.Volume1.Star3.star_3_26
        (r ⊃ₚ ∼ₚ (∼ₚ r)) (∼ₚ (∼ₚ r) ⊃ₚ r))
  have hr' : ⊢ₚ (∼ₚ (∼ₚ r) ⊃ₚ r) :=
    PM.Derivation.detach (star_4_13 r)
      (PM.FirstEdition.Volume1.Star3.star_3_27
        (r ⊃ₚ ∼ₚ (∼ₚ r)) (∼ₚ (∼ₚ r) ⊃ₚ r))
  have hqr : ⊢ₚ ((q ∧ₚ r) ⊃ₚ (q ∧ₚ ∼ₚ (∼ₚ r))) :=
    syll _ _ _ (PM.FirstEdition.Volume1.Star3.star_3_22 q r)
      (syll _ _ _
        (PM.Derivation.detach hr
          (PM.FirstEdition.Volume1.Star3.star_3_45 r (∼ₚ (∼ₚ r)) q))
        (PM.FirstEdition.Volume1.Star3.star_3_22 (∼ₚ (∼ₚ r)) q))
  have hqr' : ⊢ₚ ((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ (q ∧ₚ r)) :=
    syll _ _ _ (PM.FirstEdition.Volume1.Star3.star_3_22 q (∼ₚ (∼ₚ r)))
      (syll _ _ _
        (PM.Derivation.detach hr'
          (PM.FirstEdition.Volume1.Star3.star_3_45 (∼ₚ (∼ₚ r)) r q))
        (PM.FirstEdition.Volume1.Star3.star_3_22 r q))
  have hAB :
      ⊢ₚ (((p ∧ₚ q) ⊃ₚ ∼ₚ r) ⊃ₚ ((q ∧ₚ p) ⊃ₚ ∼ₚ r)) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_22 q p)
      (PM.FirstEdition.Volume1.Star2.star_2_06
        (q ∧ₚ p) (p ∧ₚ q) (∼ₚ r))
  have hBA :
      ⊢ₚ (((q ∧ₚ p) ⊃ₚ ∼ₚ r) ⊃ₚ ((p ∧ₚ q) ⊃ₚ ∼ₚ r)) :=
    PM.Derivation.detach (PM.FirstEdition.Volume1.Star3.star_3_22 p q)
      (PM.FirstEdition.Volume1.Star2.star_2_06
        (p ∧ₚ q) (q ∧ₚ p) (∼ₚ r))
  have hCR :
      ⊢ₚ (((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ∼ₚ p) ⊃ₚ
        ((q ∧ₚ r) ⊃ₚ ∼ₚ p)) :=
    PM.Derivation.detach hqr
      (PM.FirstEdition.Volume1.Star2.star_2_06
        (q ∧ₚ r) (q ∧ₚ ∼ₚ (∼ₚ r)) (∼ₚ p))
  have hRC :
      ⊢ₚ (((q ∧ₚ r) ⊃ₚ ∼ₚ p) ⊃ₚ
        ((q ∧ₚ ∼ₚ (∼ₚ r)) ⊃ₚ ∼ₚ p)) :=
    PM.Derivation.detach hqr'
      (PM.FirstEdition.Volume1.Star2.star_2_06
        (q ∧ₚ ∼ₚ (∼ₚ r)) (q ∧ₚ r) (∼ₚ p))
  exact adj _ _ (syll _ _ _ (syll _ _ _ hAB hBC) hCR)
    (syll _ _ _ (syll _ _ _ hRC hCB) hBA)
/-- Audited scope reading of ✱4·14. -/
def star_4_14_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·14.  ⊢ :. p . q . ⊃ . r : ≡ : p . ∼r . ⊃ . ∼q"
  parsed := ((p ∧ₚ q) ⊃ₚ r) ≡ₚ ((p ∧ₚ ∼ₚ r) ⊃ₚ ∼ₚ q)
  scopeReading := "The equivalence relates the two displayed implications."
/-- Audited scope reading of ✱4·15. -/
def star_4_15_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·15.  ⊢ :. p . q . ⊃ . ∼r : ≡ : q . r . ⊃ . ∼p"
  parsed := ((p ∧ₚ q) ⊃ₚ ∼ₚ r) ≡ₚ ((q ∧ₚ r) ⊃ₚ ∼ₚ p)
  scopeReading := "The equivalence relates the two displayed implications."
theorem star_4_39 (p q r s : PM.Elementary Γ) :
    ⊢ₚ (((p ≡ₚ r) ∧ₚ (q ≡ₚ s)) ⊃ₚ ((p ∨ₚ q) ≡ₚ (r ∨ₚ s))) :=
  let zz := (p ≡ₚ r) ∧ₚ (q ≡ₚ s)
  let z1 : ⊢ₚ (zz ⊃ₚ ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_26 (q ⊃ₚ s) (s ⊃ₚ q)) (PM.Derivation.detach (star_3_26 (p ⊃ₚ r) (r ⊃ₚ p))
        (star_3_2 ((p ≡ₚ r) ⊃ₚ (p ⊃ₚ r)) ((q ≡ₚ s) ⊃ₚ (q ⊃ₚ s)))))
      (star_3_47 (p ≡ₚ r) (q ≡ₚ s) (p ⊃ₚ r) (q ⊃ₚ s))
  let zA : ⊢ₚ (zz ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))) :=
    PM.Derivation.detach (star_3_48 p q r s) (PM.Derivation.detach z1
      (star_2_06 zz ((p ⊃ₚ r) ∧ₚ (q ⊃ₚ s)) ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))))
  let w1 : ⊢ₚ (zz ⊃ₚ ((r ⊃ₚ p) ∧ₚ (s ⊃ₚ q))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_3_27 (q ⊃ₚ s) (s ⊃ₚ q)) (PM.Derivation.detach (star_3_27 (p ⊃ₚ r) (r ⊃ₚ p))
        (star_3_2 ((p ≡ₚ r) ⊃ₚ (r ⊃ₚ p)) ((q ≡ₚ s) ⊃ₚ (s ⊃ₚ q)))))
      (star_3_47 (p ≡ₚ r) (q ≡ₚ s) (r ⊃ₚ p) (s ⊃ₚ q))
  let zB : ⊢ₚ (zz ⊃ₚ ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q))) :=
    PM.Derivation.detach (star_3_48 r s p q) (PM.Derivation.detach w1
      (star_2_06 zz ((r ⊃ₚ p) ∧ₚ (s ⊃ₚ q)) ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q))))
  PM.Derivation.detach (PM.Derivation.detach zB (PM.Derivation.detach zA
      (star_3_2 (zz ⊃ₚ ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s))) (zz ⊃ₚ ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q))))))
    (star_3_43 zz ((p ∨ₚ q) ⊃ₚ (r ∨ₚ s)) ((r ∨ₚ s) ⊃ₚ (p ∨ₚ q)))

/-- Audited scope reading of ✱4·78. -/
def star_4_78_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·78.  ⊢ : p ⊃ q . ∨ . p ⊃ r . ≡ : p . ⊃ . q ∨ r"
  parsed := ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))
  scopeReading := "The left side disjoins two implications; the right side has p as antecedent and q ∨ r as consequent."

/-- ✱4·78. `⊢ :. p ⊃ q . ∨ . p ⊃ r : ≡ . p ⊃ q ∨ r`.

Dem.
```
⊢ . ✱4·2 . (✱1·01) . ⊃
⊢ :. p ⊃ q . ∨ . p ⊃ r : ≡ : ∼p ∨ q . ∨ . ∼p ∨ r                      (1)
⊢ . ✱4·33 . ⊃
⊢ :. ∼p ∨ q . ∨ . ∼p ∨ r : ≡ : ∼p ∨ q . ∨ ∼p . ∨ r                   (2)
⊢ . ✱4·31·37 . ⊃
⊢ :. ∼p ∨ q . ∨ ∼p . ∨ r : ≡ : ∼p ∨ (∼p ∨ q) . ∨ r                   (3)
⊢ . ✱4·33 . ⊃
⊢ :. ∼p ∨ (∼p ∨ q) . ∨ r : ≡ : ∼p ∨ ∼p . ∨ . q ∨ r                   (4)
⊢ . ✱4·25·37 . ⊃
⊢ :. ∼p ∨ ∼p . ∨ . q ∨ r : ≡ : ∼p . ∨ . q ∨ r                        (5)
⊢ . ✱4·2 . (✱1·01) . ⊃
⊢ :. ∼p . ∨ . q ∨ r : ≡ . p ⊃ q ∨ r                                  (6)
⊢ . (1) . (2) . (3) . (4) . (5) . (6) . ✱4·22 . ⊃ ⊢ . Prop
```
-/
theorem star_4_78 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))) :=
  let line1a : (p ⊃ₚ q) = ((∼ₚp) ∨ₚ q) := star_1_01 p q
  let line1b : (p ⊃ₚ r) = ((∼ₚp) ∨ₚ r) := star_1_01 p r
  -- (1) ✱4·2 . (✱1·01)
  let s1 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r))) :=
    by
      rw [line1a, line1b]
      exact star_4_2 ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r))
  -- (2) ✱4·33
  let s2 : ⊢ₚ (((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)) :=
    PM.Derivation.detach (star_4_33 (∼ₚp ∨ₚ q) (∼ₚp) r)
      (PM.Derivation.detach (star_4_21 (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r) ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)))
        (star_3_26 _ _))
  -- (3) ✱4·31·37
  let s3 : ⊢ₚ ((((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)) :=
    PM.Derivation.detach (star_4_31 (∼ₚp ∨ₚ q) (∼ₚp))
      (star_4_37 ((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) (∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) r)
  -- (4) ✱4·33, once under ✱4·37 and once at the head
  let s4a : ⊢ₚ (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r)) :=
    PM.Derivation.detach (PM.Derivation.detach (star_4_33 (∼ₚp) (∼ₚp) q)
        (PM.Derivation.detach (star_4_21 ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) (∼ₚp ∨ₚ (∼ₚp ∨ₚ q))) (star_3_26 _ _)))
      (star_4_37 (∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) r)
  let s4b : ⊢ₚ ((((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))) :=
    star_4_33 (∼ₚp ∨ₚ ∼ₚp) q r
  let s4 : ⊢ₚ (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach s4b (PM.Derivation.detach s4a
        (star_3_2 (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r))
          ((((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))))))
      (star_4_22 ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ q) ∨ₚ r)
        ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)))
  -- (5) ✱4·25·37
  let s5 : ⊢ₚ (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_4_25 (∼ₚp))
        (PM.Derivation.detach (star_4_21 (∼ₚp) (∼ₚp ∨ₚ ∼ₚp)) (star_3_26 _ _)))
      (star_4_37 (∼ₚp ∨ₚ ∼ₚp) (∼ₚp) (q ∨ₚ r))
  -- (6) ✱4·2 . (✱1·01)
  let line6a : (p ⊃ₚ (q ∨ₚ r)) = ((∼ₚp) ∨ₚ (q ∨ₚ r)) :=
    star_1_01 p (q ∨ₚ r)
  let s6 : ⊢ₚ ((∼ₚp ∨ₚ (q ∨ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))) := by
    rw [line6a]
    exact star_4_2 (∼ₚp ∨ₚ (q ∨ₚ r))
  -- (1) . (2) . (3) . (4) . (5) . (6) . ✱4·22
  let t12 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)) :=
    PM.Derivation.detach (PM.Derivation.detach s2 (PM.Derivation.detach s1 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)))
        (((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ((∼ₚp ∨ₚ q) ∨ₚ (∼ₚp ∨ₚ r))
        (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r))
  let t13 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)) :=
    PM.Derivation.detach (PM.Derivation.detach s3 (PM.Derivation.detach t12 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r))
        ((((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) (((∼ₚp ∨ₚ q) ∨ₚ ∼ₚp) ∨ₚ r)
        ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r))
  let t14 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach s4 (PM.Derivation.detach t13 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r))
        (((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r))))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ((∼ₚp ∨ₚ (∼ₚp ∨ₚ q)) ∨ₚ r)
        ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)))
  let t15 : ⊢ₚ (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r))) :=
    PM.Derivation.detach (PM.Derivation.detach s5 (PM.Derivation.detach t14 (star_3_2
        (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)))
        (((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r))))))
      (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ((∼ₚp ∨ₚ ∼ₚp) ∨ₚ (q ∨ₚ r)) (∼ₚp ∨ₚ (q ∨ₚ r)))
  PM.Derivation.detach (PM.Derivation.detach s6 (PM.Derivation.detach t15 (star_3_2
      (((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) ≡ₚ (∼ₚp ∨ₚ (q ∨ₚ r)))
      ((∼ₚp ∨ₚ (q ∨ₚ r)) ≡ₚ (p ⊃ₚ (q ∨ₚ r))))))
    (star_4_22 ((p ⊃ₚ q) ∨ₚ (p ⊃ₚ r)) (∼ₚp ∨ₚ (q ∨ₚ r)) (p ⊃ₚ (q ∨ₚ r)))

/-
Note.  ✱4·78 is a proposition about *propositions*, and its analogue for
classes is false.  Take `p` to be "x is an English person", `q` "x is a man"
and `r` "x is a woman", and read the implications as holding for all values of
`x`, i.e. as inclusions of classes.  Then "all English people are men or women"
is true, while "all English people are men, or all English people are women"
is false, since some English people are men and others are women.  Thus the
equivalence asserted by ✱4·78 fails when `p ⊃ q` is replaced by the inclusion
of the class determined by `q` in the class determined by `p`: the disjunction
of two inclusions is stronger than the single inclusion in the union.  The
same remark applies to ✱4·79.
-/

/-- Audited scope reading of ✱4·79. -/
def star_4_79_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·79.  ⊢ : q ⊃ p . ∨ . r ⊃ p . ≡ : q . r . ⊃ . p"
  parsed := ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)
  scopeReading := "The left side disjoins two implications; the right side uses q . r as antecedent and p as consequent."

/-- ✱4·79. `⊢ :. q ⊃ p . ∨ . r ⊃ p : ≡ . q . r . ⊃ p`.

Dem.
```
⊢ . ✱4·1·39 . ⊃
⊢ :. q ⊃ p . ∨ . r ⊃ p : ≡ : ∼p ⊃ ∼q . ∨ . ∼p ⊃ ∼r                   (1)
⊢ . ✱4·78 . ⊃
⊢ :. ∼p ⊃ ∼q . ∨ . ∼p ⊃ ∼r : ≡ : ∼p . ⊃ . ∼q ∨ ∼r                    (2)
⊢ . ✱2·15 . ⊃
⊢ :. ∼p . ⊃ . ∼q ∨ ∼r : ≡ : ∼(∼q ∨ ∼r) . ⊃ p                         (3)
⊢ . ✱4·2 . (✱3·01) . ⊃
⊢ :. ∼(∼q ∨ ∼r) . ⊃ p : ≡ . q . r . ⊃ p                              (4)
⊢ . (1) . (2) . (3) . (4) . ✱4·22 . ⊃ ⊢ . Prop
```
-/
theorem star_4_79 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)) :=
  -- (1) ✱4·1·39
  let s1 : ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr))) :=
    PM.Derivation.detach (PM.Derivation.detach (star_4_1 r p) (PM.Derivation.detach (star_4_1 q p)
        (star_3_2 ((q ⊃ₚ p) ≡ₚ (∼ₚp ⊃ₚ ∼ₚq)) ((r ⊃ₚ p) ≡ₚ (∼ₚp ⊃ₚ ∼ₚr)))))
      (star_4_39 (q ⊃ₚ p) (r ⊃ₚ p) (∼ₚp ⊃ₚ ∼ₚq) (∼ₚp ⊃ₚ ∼ₚr))
  -- (2) ✱4·78
  let s2 : ⊢ₚ (((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr))) :=
    star_4_78 (∼ₚp) (∼ₚq) (∼ₚr)
  -- (3) ✱2·15, taken in both directions
  let s3 : ⊢ₚ ((∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)) :=
    PM.Derivation.detach (star_2_15 (∼ₚq ∨ₚ ∼ₚr) p) (PM.Derivation.detach (star_2_15 p (∼ₚq ∨ₚ ∼ₚr))
      (star_3_2 ((∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) ⊃ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p))
        ((∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ⊃ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)))))
  -- (4) ✱4·2 . (✱3·01)
  let line4a : (q ∧ₚ r) = ∼ₚ ((∼ₚ q) ∨ₚ (∼ₚ r)) := star_3_01 q r
  let s4 : ⊢ₚ ((∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)) :=
    by
      rw [line4a]
      exact star_4_2 (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)
  -- (1) . (2) . (3) . (4) . ✱4·22
  let t12 : ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr))) :=
    PM.Derivation.detach (PM.Derivation.detach s2 (PM.Derivation.detach s1 (star_3_2
        (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ ((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr)))
        (((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr))))))
      (star_4_22 ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ((∼ₚp ⊃ₚ ∼ₚq) ∨ₚ (∼ₚp ⊃ₚ ∼ₚr))
        (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)))
  let t13 : ⊢ₚ (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)) :=
    PM.Derivation.detach (PM.Derivation.detach s3 (PM.Derivation.detach t12 (star_3_2
        (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)))
        ((∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p)))))
      (star_4_22 ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) (∼ₚp ⊃ₚ (∼ₚq ∨ₚ ∼ₚr)) (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p))
  PM.Derivation.detach (PM.Derivation.detach s4 (PM.Derivation.detach t13 (star_3_2
      (((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) ≡ₚ (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p))
      ((∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ≡ₚ ((q ∧ₚ r) ⊃ₚ p)))))
    (star_4_22 ((q ⊃ₚ p) ∨ₚ (r ⊃ₚ p)) (∼ₚ(∼ₚq ∨ₚ ∼ₚr) ⊃ₚ p) ((q ∧ₚ r) ⊃ₚ p))

/-- Audited scope reading of ✱4·41. -/
def star_4_41_reading (p q r : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·41.  ⊢ : p . ∨ . q . r . ≡ . p ∨ q . p ∨ r"
  parsed := (p ∨ₚ (q ∧ₚ r)) ≡ₚ ((p ∨ₚ q) ∧ₚ (p ∨ₚ r))
  scopeReading := "On the left p is disjoined from q . r; the right side conjoins p ∨ q with p ∨ r."

/-- PM I (1910), p. 124, ✱4·41. -/
theorem star_4_41 {Γ} (p q r : PM.Elementary Γ) :
    ⊢ₚ ((p ∨ₚ (q ∧ₚ r)) ≡ₚ ((p ∨ₚ q) ∧ₚ (p ∨ₚ r))) := by
  have infer : ∀ {A B : PM.Elementary Γ}, (⊢ₚ A) → (⊢ₚ (A ⊃ₚ B)) → (⊢ₚ B) := by
    intro A B hA hAB
    match Γ, A, B, hA, hAB with
    | [], _, _, hA, hAB => exact PM.Derivation.star_1_1 hA hAB
    | (τ :: Δ), _, _, hA, hAB =>
        exact PM.Derivation.star_1_11 (List.cons_ne_nil τ Δ) hA hAB
  have comp : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (B ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ C)) := by
    intro A B C hAB hBC
    exact infer hAB (infer hBC (PM.FirstEdition.Volume1.Star2.star_2_05 A B C))
  have duplicate : ∀ A : PM.Elementary Γ, ⊢ₚ (A ⊃ₚ (A ∧ₚ A)) := by
    intro A
    exact infer (PM.FirstEdition.Volume1.Star3.star_3_2 A A)
      (PM.FirstEdition.Volume1.Star2.star_2_43 A (A ∧ₚ A))
  have join : ∀ {A B C : PM.Elementary Γ}, (⊢ₚ (A ⊃ₚ B)) →
      (⊢ₚ (A ⊃ₚ C)) → (⊢ₚ (A ⊃ₚ (B ∧ₚ C))) := by
    intro A B C hAB hAC
    have pair := infer hAC (infer hAB
      (PM.FirstEdition.Volume1.Star3.star_3_2 (A ⊃ₚ B) (A ⊃ₚ C)))
    exact comp (duplicate A) (infer pair
      (PM.FirstEdition.Volume1.Star3.star_3_47 A A B C))
  let A := (p ∨ₚ q) ∧ₚ (p ∨ₚ r)
  have forwardQ := infer (PM.FirstEdition.Volume1.Star3.star_3_26 q r)
    (PM.Derivation.star_1_6 p (q ∧ₚ r) q)
  have forwardR := infer (PM.FirstEdition.Volume1.Star3.star_3_27 q r)
    (PM.Derivation.star_1_6 p (q ∧ₚ r) r)
  have forward : ⊢ₚ ((p ∨ₚ (q ∧ₚ r)) ⊃ₚ ((p ∨ₚ q) ∧ₚ (p ∨ₚ r))) :=
    join forwardQ forwardR
  have toQ := comp (PM.FirstEdition.Volume1.Star3.star_3_26 (p ∨ₚ q) (p ∨ₚ r))
    (PM.FirstEdition.Volume1.Star2.star_2_53 p q)
  have toR := comp (PM.FirstEdition.Volume1.Star3.star_3_27 (p ∨ₚ q) (p ∨ₚ r))
    (PM.FirstEdition.Volume1.Star2.star_2_53 p r)
  have underNot : ⊢ₚ (A ⊃ₚ ((∼ₚ p) ⊃ₚ (q ∧ₚ r))) :=
    comp (join toQ toR) (PM.FirstEdition.Volume1.Star3.star_3_43 (∼ₚ p) q r)
  have backward : ⊢ₚ (A ⊃ₚ (p ∨ₚ (q ∧ₚ r))) :=
    comp underNot (PM.FirstEdition.Volume1.Star2.star_2_54 p (q ∧ₚ r))
  exact infer backward (infer forward
    (PM.FirstEdition.Volume1.Star3.star_3_2
      ((p ∨ₚ (q ∧ₚ r)) ⊃ₚ A) (A ⊃ₚ (p ∨ₚ (q ∧ₚ r)))))

/-- Audited scope reading of ✱4·61. -/
def star_4_61_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·61.  ⊢ : ∼(p ⊃ q) . ≡ . p . ∼q"
  parsed := (∼ₚ (p ⊃ₚ q)) ≡ₚ (p ∧ₚ (∼ₚ q))
  scopeReading := "The negated implication is the left side; p . ∼q is the conjunctive right side."

/-- PM I (1910), p. 126, ✱4·61. -/
theorem star_4_61 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((∼ₚ (p ⊃ₚ q)) ≡ₚ (p ∧ₚ (∼ₚ q))) := by
  have inner : ⊢ₚ ((∼ₚ p ∨ₚ q) ≡ₚ (∼ₚ p ∨ₚ ∼ₚ (∼ₚ q))) := by
    have pair := PM.Derivation.detach (star_4_13 q)
      (PM.Derivation.detach (star_4_2 (∼ₚ p))
        (PM.FirstEdition.Volume1.Star3.star_3_2
          ((∼ₚ p) ≡ₚ (∼ₚ p)) (q ≡ₚ ∼ₚ (∼ₚ q))))
    exact PM.Derivation.detach pair
      (star_4_39 (∼ₚ p) q (∼ₚ p) (∼ₚ (∼ₚ q)))
  have forward := PM.Derivation.detach
    (star_4_11 (∼ₚ p ∨ₚ q) (∼ₚ p ∨ₚ ∼ₚ (∼ₚ q)))
    (PM.FirstEdition.Volume1.Star3.star_3_26 _ _)
  exact PM.Derivation.detach inner forward


/-- Audited scope reading of ✱4·3. -/
def star_4_3_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·3.  ⊢ : p . q . ≡ . q . p"
  parsed := (p ∧ₚ q) ≡ₚ (q ∧ₚ p)
  scopeReading := "The two sides are the two orders of the same logical product."

/-- ✱4·3, the two instances of ✱3·22 cited by PM. -/
theorem star_4_3 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ≡ₚ (q ∧ₚ p)) := by
  have line1 : ⊢ₚ ((p ∧ₚ q) ⊃ₚ (q ∧ₚ p)) :=
    PM.FirstEdition.Volume1.Star3.star_3_22 p q
  have line2 : ⊢ₚ ((q ∧ₚ p) ⊃ₚ (p ∧ₚ q)) :=
    PM.FirstEdition.Volume1.Star3.star_3_22 q p
  exact targetJoin line1 line2

/-- Audited scope reading of ✱4·5. -/
def star_4_5_reading (p q : PM.Elementary Γ) : PM.ElementaryReading Γ where
  printed := PM.pmPrinted "✱4·5.  ⊢ : p . q . ≡ . ∼(∼p ∨ ∼q)"
  parsed := (p ∧ₚ q) ≡ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))
  scopeReading := "The right side is exactly the ✱3·01 expansion of the product on the left."

/-- ✱4·5, following ✱4·2 and the definition ✱3·01. -/
theorem star_4_5 {Γ} (p q : PM.Elementary Γ) :
    ⊢ₚ ((p ∧ₚ q) ≡ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q)))) := by
  have line1 := star_4_2 (p ∧ₚ q)
  exact line1

end PM.FirstEdition.Volume1.Star4
