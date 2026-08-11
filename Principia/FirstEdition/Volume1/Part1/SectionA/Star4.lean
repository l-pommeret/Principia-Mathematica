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

end PM.FirstEdition.Volume1.Star4
