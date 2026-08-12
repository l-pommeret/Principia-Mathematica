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

/- PM-VERBATIM-BEGIN PM1:✱4·34
✱4·34.  p . q . r .=. (p . q) . r   Df
PM-VERBATIM-END PM1:✱4·34 -/

/- PM-VERBATIM-BEGIN PM1:✱4·36
✱4·36.  ⊢ : p ≡ q . ⊃ : p . r . ≡ . q . r   [Fact . ✱3·47]
PM-VERBATIM-END PM1:✱4·36 -/

/- PM-VERBATIM-BEGIN PM1:✱4·37
✱4·37.  ⊢ : p ≡ q . ⊃ : p ∨ r . ≡ . q ∨ r   [Sum . ✱3·47]
PM-VERBATIM-END PM1:✱4·37 -/

/- PM-VERBATIM-BEGIN PM1:✱4·38
✱4·38.  ⊢ : p ≡ r . q ≡ s . ⊃ : p . q . ≡ . r . s   [✱3·47 . ✱4·32 . ✱3·22]
PM-VERBATIM-END PM1:✱4·38 -/

/- PM-VERBATIM-BEGIN PM1:✱4·39
✱4·39.  ⊢ : p ≡ r . q ≡ s . ⊃ : p ∨ q . ≡ . r ∨ s   [✱3·48 . ✱4·32 . ✱3·22]
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
✱4·52.  ⊢ : ∼∼p . ∼q . ≡ . ∼(∼q ∨ q)   [✱4·5 ∼q/q . ✱4·13]
PM-VERBATIM-END PM1:✱4·52 -/

/- PM-VERBATIM-BEGIN PM1:✱4·53
✱4·53.  ⊢ : ∼∼(p . ∼q) . ≡ . ∼p ∨ q   [✱4·52·12]
PM-VERBATIM-END PM1:✱4·53 -/

/- PM-VERBATIM-BEGIN PM1:✱4·54
✱4·54.  ⊢ : ∼∼p . q . ≡ . ∼(p ∨ ∼q)   [✱4·5 ∼p/p . ✱4·13]
PM-VERBATIM-END PM1:✱4·54 -/

/- PM-VERBATIM-BEGIN PM1:✱4·55
✱4·55.  ⊢ : ∼∼(∼p . q) . ≡ . p ∨ ∼q   [✱4·54·12]
PM-VERBATIM-END PM1:✱4·55 -/

/- PM-VERBATIM-BEGIN PM1:✱4·56
✱4·56.  ⊢ : ∼∼∼(∼p . ∼q) . ≡ . ∼(p ∨ q)   [✱4·54 ∼q/q . ✱4·13]
PM-VERBATIM-END PM1:✱4·56 -/

/- PM-VERBATIM-BEGIN PM1:✱4·57
✱4·57.  ⊢ : ∼∼(p ∨ q) . ≡ . ∼p . ∼q   [✱4·56·13]
PM-VERBATIM-END PM1:✱4·57 -/

/- PM-VERBATIM-BEGIN PM1:✱4·6
✱4·6.  ⊢ : ∼p ⊃ q . ≡ . ∼p ∨ q   [✱4·2 . (✱1·01)]
PM-VERBATIM-END PM1:✱4·6 -/

/- PM-VERBATIM-BEGIN PM1:✱4·61
✱4·61.  ⊢ : ∼(p ⊃ q) . ≡ . p . ∼q   [✱4·6·11·52]
PM-VERBATIM-END PM1:✱4·61 -/

/- PM-VERBATIM-BEGIN PM1:✱4·62
✱4·62.  ⊢ : ∼∼p ⊃ ∼q . ≡ . ∼p ∨ ∼q   [✱4·6 ∼q/q]
PM-VERBATIM-END PM1:✱4·62 -/

/- PM-VERBATIM-BEGIN PM1:✱4·63
✱4·63.  ⊢ : ∼∼∼(p ⊃ ∼q) . ≡ . p . q   [✱4·62·11·5]
PM-VERBATIM-END PM1:✱4·63 -/

/- PM-VERBATIM-BEGIN PM1:✱4·64
✱4·64.  ⊢ : ∼∼∼p ⊃ q . ≡ . p ∨ q   [✱2·53·54]
PM-VERBATIM-END PM1:✱4·64 -/

/- PM-VERBATIM-BEGIN PM1:✱4·65
✱4·65.  ⊢ : ∼∼∼(∼p ⊃ q) . ≡ . ∼p . ∼q   [✱4·64·11·56]
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
✱4·74.  ⊢ : ∼p . ⊃ : q . ≡ . p ∨ q   [✱2·21 . ✱4·72]
PM-VERBATIM-END PM1:✱4·74 -/

/- PM-VERBATIM-BEGIN PM1:✱4·76
✱4·76.  ⊢ : p ⊃ q . p ⊃ r . ≡ : p . ⊃ . q . r   [✱4·41 ∼p/p . (✱1·01)]
PM-VERBATIM-END PM1:✱4·76 -/

/- PM-VERBATIM-BEGIN PM1:✱4·77
✱4·77.  ⊢ : q ⊃ p . r ⊃ p . ≡ : q ∨ r . ⊃ . p   [✱3·44 . Add . ✱2·2]
PM-VERBATIM-END PM1:✱4·77 -/

/- PM-VERBATIM-BEGIN PM1:✱4·86
✱4·86.  ⊢ : p ≡ q . ⊃ : p ≡ r . ≡ . q ≡ r   [✱4·21·22]
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
✱4·84.  ⊢ : p ≡ q . ⊃ : p ⊃ r . ≡ . q ⊃ r   [✱2·06 . ✱3·47]
PM-VERBATIM-END PM1:✱4·84 -/

/- PM-VERBATIM-BEGIN PM1:✱4·85
✱4·85.  ⊢ : p ≡ q . ⊃ : r ⊃ p . ≡ . r ⊃ q   [✱2·05 . ✱3·47]
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

end PM.Elementary

namespace PM.FirstEdition.Volume1.Star4

open PM
open PM.Elementary

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
    have pair := infer hab (infer hac (PM.FirstEdition.Volume1.Star3.star_3_2 (a ⊃ₚ b) (a ⊃ₚ c)))
    exact compose (dup a) (infer pair (PM.FirstEdition.Volume1.Star3.star_3_47 a a b c))
  let e := p ≡ₚ q
  have idr : ⊢ₚ (r ⊃ₚ r) := PM.FirstEdition.Volume1.Star2.star_2_08 r
  have er : ⊢ₚ (e ⊃ₚ (r ⊃ₚ r)) := infer idr (PM.FirstEdition.Volume1.Star2.star_2_02 e (r ⊃ₚ r))
  have f := compose (lift (PM.FirstEdition.Volume1.Star3.star_3_26 (p ⊃ₚ q) (q ⊃ₚ p)) er) (PM.FirstEdition.Volume1.Star3.star_3_47 (p ⊃ₚ q) (r ⊃ₚ r) (q ⊃ₚ p) (r ⊃ₚ r))
  have b := compose (lift (PM.FirstEdition.Volume1.Star3.star_3_27 (p ⊃ₚ q) (q ⊃ₚ p)) er) (PM.FirstEdition.Volume1.Star3.star_3_47 (q ⊃ₚ p) (r ⊃ₚ r) (p ⊃ₚ q) (r ⊃ₚ r))
  exact lift f b

end PM.FirstEdition.Volume1.Star4
