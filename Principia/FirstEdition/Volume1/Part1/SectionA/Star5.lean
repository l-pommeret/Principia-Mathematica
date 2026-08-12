/-!
# PM I, first edition, ✱5 — miscellaneous propositions

Diplomatic source record only; Lean formalization is tracked separately.
Canonical scan leaves: 152–153 (printed pp. 130–131).
-/

/- PM-VERBATIM-BEGIN PM1:✱5·1
✱5·1.  ⊢ : p . q . ⊃ . p ≡ q   [✱3·4·22]

✱5. Miscellaneous Propositions.

Summary of ✱5.

The present number consists chiefly of propositions of two sorts: (1) those which will be required as lemmas in one or more subsequent proofs, (2) those which are on their own account illustrative, or would be important in other developments than those that we wish to make. A few of the propositions of this number, however, will be used very frequently. These are:

✱5·1. ⊢ : p . q . ⊃ . p ≡ q

I.e. two propositions are equivalent if they are both true. (The statement that two propositions are equivalent if they are both false is ✱5·21.)

✱5·32. ⊢ :. p . ⊃ . q ≡ r : ≡ : p . q . ≡ . p . r

I.e. to say that, on the hypothesis p, q and r are equivalent, is equivalent to saying that the joint assertion of p and q is equivalent to the joint assertion of p and r. This is a very useful rule in inference.

✱5·6. ⊢ :. p . ∼q . ⊃ . r : ≡ : p . ⊃ . q ∨ r

I.e. “p and not-q imply r” is equivalent to “p implies q or r.”

Among propositions never subsequently referred to, but inserted for their intrinsic interest, are the following: ✱5·11·12·13·14, which state that, given any two propositions p, q, either p or ∼p must imply q, and p must imply either q or not-q, and either p implies q or q implies p; and given any third proposition r, either p implies q or q implies r*.

Other propositions not subsequently referred to are ✱5·22·23·24; in these it is shown that two propositions are not equivalent when, and only when, one is true and the other false, and that two propositions are equivalent when, and only when, both are true or both false. It follows (✱5·24) that the negation of “p . q . ∨ . ∼p . ∼q” is equivalent to “p . ∼q . ∨ . q . ∼p.” ✱5·54·55 state that both the product and the sum of p and q are equivalent, respectively, either to p or to q.

The proofs of the following propositions are all easy, and we shall therefore often merely indicate the propositions used in the proofs.

* Cf. Schröder, *Vorlesungen über Algebra der Logik*, Zweiter Band (Leipzig, 1891), pp. 270–271, where the apparent oddity of the above proposition is explained.
PM-VERBATIM-END PM1:✱5·1 -/

/- PM-VERBATIM-BEGIN PM1:✱5·11
✱5·11.  ⊢ : p ⊃ q . ∨ . ∼p ⊃ q   [✱2·51·54]
PM-VERBATIM-END PM1:✱5·11 -/
/- PM-VERBATIM-BEGIN PM1:✱5·12
✱5·12.  ⊢ : p ⊃ q . ∨ . p ⊃ ∼q   [✱2·52·54]
PM-VERBATIM-END PM1:✱5·12 -/
/- PM-VERBATIM-BEGIN PM1:✱5·13
✱5·13.  ⊢ : p ⊃ q . ∨ . q ⊃ p   [✱2·521]
PM-VERBATIM-END PM1:✱5·13 -/
/- PM-VERBATIM-BEGIN PM1:✱5·14
✱5·14.  ⊢ : p ⊃ q . ∨ . q ⊃ r   [Simp . Transp . ✱2·21]
PM-VERBATIM-END PM1:✱5·14 -/
/- PM-VERBATIM-BEGIN PM1:✱5·15
✱5·15.  ⊢ : p ≡ q . ∨ . p ≡ ∼q

Dem.
⊢ . ✱4·61 . ⊃ ⊢ : ∼(p ⊃ q) . ⊃ . p . ∼q :
[✱5·1] ⊃ . p ≡ ∼q :
[✱2·54] ⊃ ⊢ : p ⊃ q . ∨ . p ≡ ∼q   (1)
⊢ . ✱4·61 . ⊃ ⊢ : ∼(q ⊃ p) . ⊃ . q . ∼p :
[✱5·1] ⊃ . q ≡ ∼p :
[✱4·12] ⊃ . p ≡ ∼q :
[✱2·54] ⊃ ⊢ : q ⊃ p . ∨ . p ≡ ∼q   (2)
⊢ . (1) . (2) . ✱4·41 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱5·15 -/
/- PM-VERBATIM-BEGIN PM1:✱5·16
✱5·16.  ⊢ . ∼(p ≡ q . p ≡ ∼q)

Dem.
⊢ . ✱3·26 . ⊃ ⊢ : p ≡ q . p ⊃ ∼q . ⊃ . p ⊃ q . p ⊃ ∼q :
[✱4·82] ⊃ . ∼p   (1)
⊢ . ✱3·27 . ⊃ ⊢ : p ≡ q . p ⊃ ∼q . ⊃ . q ⊃ p . p ⊃ ∼q :
[Syll] ⊃ . q ⊃ ∼q :
[Abs] ⊃ . ∼q   (2)
⊢ . (1) . (2) . Comp . ⊃ ⊢ : p ≡ q . p ⊃ ∼q . ⊃ . ∼p . ∼q :
[✱4·65 (q,p)/(p,q)] ⊃ . ∼(∼q ⊃ p)   (3)
⊢ . (3) . Exp . ⊃ ⊢ : p ≡ q . ⊃ : p ⊃ ∼q . ⊃ . ∼(∼q ⊃ p) :
[Id . (✱1·01)] ⊃ : ∼(p ⊃ ∼q) . ∨ . ∼(∼q ⊃ p) :
[✱4·51 . (✱4·01)] ⊃ : ∼(p ≡ ∼q) :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱5·16 -/
/- PM-VERBATIM-BEGIN PM1:✱5·17
✱5·17.  ⊢ : p ∨ q . ∼(p . q) . ≡ . p ≡ ∼q

Dem.
⊢ . ✱4·64·21 . ⊃ ⊢ : p ∨ q . ≡ . ∼q ⊃ p   (1)
⊢ . ✱4·63 . Transp . ⊃ ⊢ : ∼(p . q) . ≡ . p ⊃ ∼q   (2)
⊢ . (1) . (2) . ✱4·38·21 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱5·17 -/

/- PM-VERBATIM-BEGIN PM1:✱5·18
✱5·18.  ⊢ : p ≡ q . ≡ . ∼(p ≡ ∼q)   [✱5·15·16 . ✱5·17 (p ≡ q, p ≡ ∼q)/(p, q)]
PM-VERBATIM-END PM1:✱5·18 -/
/- PM-VERBATIM-BEGIN PM1:✱5·19
✱5·19.  ⊢ . ∼(p ≡ ∼p)   [✱5·18 p/q . ✱4·2]
PM-VERBATIM-END PM1:✱5·19 -/
/- PM-VERBATIM-BEGIN PM1:✱5·21
✱5·21.  ⊢ : ∼p . ∼q . ⊃ . p ≡ q   [✱5·1 . ✱4·11]
PM-VERBATIM-END PM1:✱5·21 -/
/- PM-VERBATIM-BEGIN PM1:✱5·22
✱5·22.  ⊢ : ∼(p ≡ q) . ≡ : p . ∼q . ∨ . q . ∼p   [✱4·61·51·39]
PM-VERBATIM-END PM1:✱5·22 -/
/- PM-VERBATIM-BEGIN PM1:✱5·23
✱5·23.  ⊢ : p ≡ q . ≡ : p . q . ∨ . ∼p . ∼q   [✱5·18 . ✱5·22 ∼q/q . ✱4·13·36]
PM-VERBATIM-END PM1:✱5·23 -/
/- PM-VERBATIM-BEGIN PM1:✱5·24
✱5·24.  ⊢ : ∼(p . q . ∨ . ∼p . ∼q) . ≡ : p . ∼q . ∨ . q . ∼p   [✱5·22·23]
PM-VERBATIM-END PM1:✱5·24 -/
/- PM-VERBATIM-BEGIN PM1:✱5·25
✱5·25.  ⊢ : p ∨ q . ≡ : p ⊃ q . ⊃ . q   [✱2·62·68]

From ✱5·25 it appears that we might have taken implication, instead of disjunction, as a primitive idea, and have defined “p ∨ q” as meaning “p ⊃ q . ⊃ . q.” This course, however, requires more primitive propositions than are required by the method we have adopted.
PM-VERBATIM-END PM1:✱5·25 -/
/- PM-VERBATIM-BEGIN PM1:✱5·3
✱5·3.  ⊢ : p . q . ⊃ . r : ≡ : p . q . ⊃ . p . r   [Simp . Comp . Syll]
PM-VERBATIM-END PM1:✱5·3 -/
/- PM-VERBATIM-BEGIN PM1:✱5·31
✱5·31.  ⊢ : r . p ⊃ q . ⊃ : p . ⊃ . q . r   [Simp . Comp]
PM-VERBATIM-END PM1:✱5·31 -/
/- PM-VERBATIM-BEGIN PM1:✱5·32
✱5·32.  ⊢ : p . ⊃ . q ≡ r : ≡ : p . q . ≡ . p . r   [✱4·76 . ✱3·3·31 . ✱5·3]

This proposition is constantly required in subsequent proofs.
PM-VERBATIM-END PM1:✱5·32 -/
/- PM-VERBATIM-BEGIN PM1:✱5·33
✱5·33.  ⊢ : p . q ⊃ r . ≡ : p : p . q . ⊃ . r   [✱4·73·84 . ✱5·32]
PM-VERBATIM-END PM1:✱5·33 -/
/- PM-VERBATIM-BEGIN PM1:✱5·35
✱5·35.  ⊢ : p ⊃ q . p ⊃ r . ⊃ : p . ⊃ . q ≡ r   [Comp . ✱5·1]
PM-VERBATIM-END PM1:✱5·35 -/
/- PM-VERBATIM-BEGIN PM1:✱5·36
✱5·36.  ⊢ : p . p ≡ q . ≡ . q . p ≡ q   [Ass . ✱4·38]
PM-VERBATIM-END PM1:✱5·36 -/
/- PM-VERBATIM-BEGIN PM1:✱5·4
✱5·4.  ⊢ : p . ⊃ . p ⊃ q : ≡ . p ⊃ q   [Simp . ✱2·43]
PM-VERBATIM-END PM1:✱5·4 -/
/- PM-VERBATIM-BEGIN PM1:✱5·41
✱5·41.  ⊢ : p ⊃ q . ⊃ . p ⊃ r : ≡ : p . ⊃ . q ⊃ r   [✱2·77·86]
PM-VERBATIM-END PM1:✱5·41 -/
/- PM-VERBATIM-BEGIN PM1:✱5·42
✱5·42.  ⊢ : :p . ⊃ . q ⊃ r : ≡ : p . ⊃ : q . ⊃ . p . r   [✱5·3 . ✱4·87]
PM-VERBATIM-END PM1:✱5·42 -/
/- PM-VERBATIM-BEGIN PM1:✱5·44
✱5·44.  ⊢ : :p ⊃ q . ⊃ : p ⊃ r . ≡ : p . ⊃ . q . r   [✱4·76 . ✱5·3·32]
PM-VERBATIM-END PM1:✱5·44 -/
/- PM-VERBATIM-BEGIN PM1:✱5·5
✱5·5.  ⊢ : p . ⊃ : p ⊃ q . ≡ . q   [Ass . Exp . Simp]
PM-VERBATIM-END PM1:✱5·5 -/
/- PM-VERBATIM-BEGIN PM1:✱5·501
✱5·501.  ⊢ : p . ⊃ : q . ≡ . p ≡ q   [✱5·1 . Exp . Ass]
PM-VERBATIM-END PM1:✱5·501 -/
/- PM-VERBATIM-BEGIN PM1:✱5·53
✱5·53.  ⊢ : p ∨ q ∨ r . ⊃ . s : ≡ : p ⊃ s . q ⊃ s . r ⊃ s   [✱4·77]
PM-VERBATIM-END PM1:✱5·53 -/
/- PM-VERBATIM-BEGIN PM1:✱5·54
✱5·54.  ⊢ : p . q . ≡ . p : ∨ : p . q . ≡ . q   [✱4·73 . ✱4·44 . Transp . ✱5·1]
PM-VERBATIM-END PM1:✱5·54 -/
/- PM-VERBATIM-BEGIN PM1:✱5·55
✱5·55.  ⊢ : p ∨ q . ≡ . p : ∨ : p ∨ q . ≡ . q   [✱1·3 . ✱5·1 . ✱4·74]
PM-VERBATIM-END PM1:✱5·55 -/
/- PM-VERBATIM-BEGIN PM1:✱5·6
✱5·6.  ⊢ : p . ∼q . ⊃ . r : ≡ : p . ⊃ . q ∨ r   [✱4·87 ∼q/q . ✱4·64·85]
PM-VERBATIM-END PM1:✱5·6 -/
/- PM-VERBATIM-BEGIN PM1:✱5·61
✱5·61.  ⊢ : p ∨ q . ∼q . ≡ . p . ∼q   [✱4·74 . ✱5·32]
PM-VERBATIM-END PM1:✱5·61 -/
/- PM-VERBATIM-BEGIN PM1:✱5·62
✱5·62.  ⊢ : p . q . ∨ . ∼q : ≡ . p ∨ ∼q   [✱4·7 (q,p)/(p,q)]
PM-VERBATIM-END PM1:✱5·62 -/
/- PM-VERBATIM-BEGIN PM1:✱5·63
✱5·63.  ⊢ : p ∨ q . ≡ : p . ∨ . ∼p . q   [✱5·62 (∼p,q)/(q,p)]
PM-VERBATIM-END PM1:✱5·63 -/
/- PM-VERBATIM-BEGIN PM1:✱5·7
✱5·7.  ⊢ : p ∨ r . ≡ . q ∨ r : ≡ : r . ∨ . p ≡ q   [✱4·74 . ✱1·3 . ✱5·1 . ✱4·37]
PM-VERBATIM-END PM1:✱5·7 -/
/- PM-VERBATIM-BEGIN PM1:✱5·71
✱5·71.  ⊢ : q ⊃ ∼r . ⊃ : p ∨ q . r . ≡ . p . r

In the following proof, as always henceforth, “Hp” means the hypothesis of the proposition to be proved.

Dem.
⊢ . ✱4·4 . ⊃ ⊢ : p ∨ q . r . ≡ : p . r . ∨ . q . r   (1)
⊢ . ✱4·62·51 . ⊃ ⊢ : Hp . ⊃ : ∼(q . r) :
[✱4·74] ⊃ : p . r . ∨ . q . r . ≡ : p . r   (2)
⊢ . (1) . (2) . ✱4·22 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱5·71 -/

/- PM-VERBATIM-BEGIN PM1:✱5·74
✱5·74.  ⊢ : p . ⊃ . q ≡ r : ≡ : p ⊃ q . ≡ . p ⊃ r

Dem.
⊢ . ✱5·41 . ⊃ ⊢ :: p ⊃ q . ⊃ . p ⊃ r : ≡ : p . ⊃ . q ⊃ r :.
  p ⊃ r . ⊃ . p ⊃ q : ≡ : p . ⊃ . r ⊃ q   (1)
⊢ . (1) . ✱4·38 . ⊃ ⊢ :: p ⊃ q . ≡ . p ⊃ r . ≡ :.
  p . ⊃ . q ⊃ r : p . ⊃ . r ⊃ q :.
[✱4·76] ≡ :. p . ⊃ . q ≡ r :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱5·74 -/

/- PM-VERBATIM-BEGIN PM1:✱5·75
✱5·75.  ⊢ : r ⊃ ∼q . ⊃ : p ≡ q ∨ r . ⊃ : p . ∼q . ≡ . r

Dem.
⊢ . ✱5·6 . ⊃ ⊢ : Hp . ⊃ : p . ∼q . ⊃ . r   (1)
⊢ . ✱3·27 . ⊃ ⊢ : Hp . ⊃ : q ∨ r . ⊃ . p :
[✱4·77] ⊃ : r ⊃ p   (2)
⊢ . ✱3·26 . ⊃ ⊢ : Hp . ⊃ : r ⊃ ∼q   (3)
⊢ . (2) . (3) . Comp . ⊃ ⊢ : Hp . ⊃ : r ⊃ p . r ⊃ ∼q :
[Comp] ⊃ : r . ⊃ . p . ∼q   (4)
⊢ . (1) . (4) . Comp . ⊃ ⊢ : Hp . ⊃ : p . ∼q . ≡ . r : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱5·75 -/
