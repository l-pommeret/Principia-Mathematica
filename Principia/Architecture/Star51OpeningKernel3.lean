import Principia.Architecture.Star51OpeningKernel2

namespace PM.Architecture.Star51OpeningKernel3

open PM.Architecture.Star51OpeningKernel
open PM.Architecture.Star51OpeningKernel2

/-- ✱51·232: membership in a two-element class. -/
theorem star_51_232 (x y z : α) :
    Union (singleton x) (singleton y) z ↔ z = x ∨ z = y := by
  rfl

/-- ✱51·233: the pointwise characterization of a class equal to two
singletons. -/
theorem star_51_233 (A : Class α) (x y : α)
    (h : A = Union (singleton x) (singleton y)) :
    ∀ z, A z ↔ z = x ∨ z = y := by
  subst A
  intro z
  rfl

/-- ✱51·234: a predicate holds of every member of a two-element class exactly
when it holds of both displayed elements. -/
theorem star_51_234 (A : Class α) (x y : α) (φ : α → Prop)
    (h : A = Union (singleton x) (singleton y)) :
    (∀ z, A z → φ z) ↔ φ x ∧ φ y := by
  subst A
  constructor
  · intro hall
    exact ⟨hall x (Or.inl rfl), hall y (Or.inr rfl)⟩
  · rintro ⟨hx, hy⟩ z (hzx | hzy)
    · exact hzx ▸ hx
    · exact hzy ▸ hy

/-- ✱51·235: existential quantification over a two-element class. -/
theorem star_51_235 (A : Class α) (x y : α) (φ : α → Prop)
    (h : A = Union (singleton x) (singleton y)) :
    (∃ z, A z ∧ φ z) ↔ φ x ∨ φ y := by
  subst A
  constructor
  · rintro ⟨z, hzx | hzy, hz⟩
    · exact Or.inl (hzx ▸ hz)
    · exact Or.inr (hzy ▸ hz)
  · rintro (hx | hy)
    · exact ⟨x, Or.inl rfl, hx⟩
    · exact ⟨y, Or.inr rfl, hy⟩

/-- ✱51·236: membership after adjoining one element. -/
theorem star_51_236 (x z : α) (B : Class α) :
    Union (singleton x) B z ↔ z = x ∨ B z := by
  rfl

/-- ✱51·237: pointwise characterization after adjoining one element. -/
theorem star_51_237 (A B : Class α) (x : α)
    (h : A = Union (singleton x) B) :
    ∀ z, A z ↔ z = x ∨ B z := by
  subst A
  intro z
  rfl

/-- ✱51·238: universal quantification after adjoining one element. -/
theorem star_51_238 (A B : Class α) (x : α) (φ : α → Prop)
    (h : A = Union (singleton x) B) :
    (∀ z, A z → φ z) ↔ φ x ∧ (∀ z, B z → φ z) := by
  subst A
  constructor
  · intro hall
    exact ⟨hall x (Or.inl rfl), fun z hz => hall z (Or.inr hz)⟩
  · rintro ⟨hx, hB⟩ z (hzx | hzB)
    · exact hzx ▸ hx
    · exact hB z hzB

/-- ✱51·239: existential quantification after adjoining one element. -/
theorem star_51_239 (A B : Class α) (x : α) (φ : α → Prop)
    (h : A = Union (singleton x) B) :
    (∃ z, A z ∧ φ z) ↔ φ x ∨ ∃ z, B z ∧ φ z := by
  subst A
  constructor
  · rintro ⟨z, hzx | hzB, hz⟩
    · exact Or.inl (hzx ▸ hz)
    · exact Or.inr ⟨z, hzB, hz⟩
  · rintro (hx | ⟨z, hzB, hz⟩)
    · exact ⟨x, Or.inl rfl, hx⟩
    · exact ⟨z, Or.inr hzB, hz⟩

/-- ✱51·24: inclusion of a unit class in an adjoined class. -/
theorem star_51_24 (x y : α) (B : Class α) :
    Included (singleton y) (Union (singleton x) B) ↔ y = x ∨ B y := by
  constructor
  · intro h
    exact h y rfl
  · intro h z hzy
    exact hzy ▸ h

/-- ✱51·25: if a class included in `ιʻx ∪ B` does not contain `x`, it is
already included in `B`. -/
theorem star_51_25 (A B : Class α) (x : α) :
    Included A (Union (singleton x) B) → ¬A x → Included A B := by
  intro h hnot z hz
  exact (h z hz).resolve_left (fun hzx => hnot (hzx ▸ hz))

end PM.Architecture.Star51OpeningKernel3
