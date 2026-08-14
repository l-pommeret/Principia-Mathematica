import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.Star11Q282Kernel

open PM.CanonicalOrderedFormula
open PM.Architecture.CanonicalOrderedAdapters

/-!
# PM I ✱11·39–✱11·41

Exact `Raw` endpoints plus secondary modern readings of the five displayed
two-variable propositions. No PM derivation is claimed in this module.
-/

private def imp (p q : Raw Γ) : Raw Γ := rawImp p q
private def conj (p q : Raw Γ) : Raw Γ := .neg (.disj (.neg p) (.neg q))
private def equiv (p q : Raw Γ) : Raw Γ := conj (imp p q) (imp q p)
private def mImp (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :=
  Apparent.disj (Apparent.neg φ) ψ
private def mConj (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :=
  Apparent.neg (Apparent.disj (Apparent.neg φ) (Apparent.neg ψ))
private def mEquiv (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) :=
  mConj (mImp φ ψ) (mImp ψ φ)
private def all2 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .always (.quantified .always (ofApparent φ))
private def some2 (φ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  .quantified .sometimes (.quantified .sometimes (ofApparent φ))

def star_11_39_target (φ ψ χ θ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (conj (all2 (mImp φ ψ)) (all2 (mImp χ θ)))
    (all2 (mImp (mConj φ χ) (mConj ψ θ)))

def star_11_391_target (φ ψ χ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (conj (all2 (mImp φ ψ)) (all2 (mImp φ χ)))
    (all2 (mImp φ (mConj ψ χ)))

def star_11_4_target (φ ψ χ θ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (conj (all2 (mEquiv φ ψ)) (all2 (mEquiv χ θ)))
    (all2 (mEquiv (mConj φ χ) (mConj ψ θ)))

def star_11_401_target (φ ψ χ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  imp (all2 (mEquiv φ ψ)) (all2 (mEquiv (mConj φ χ) (mConj ψ χ)))

def star_11_41_target (φ ψ : Apparent Γ
    [.elementaryProposition, .elementaryProposition]) : Raw Γ :=
  equiv (.disj (some2 φ) (some2 ψ)) (some2 (Apparent.disj φ ψ))

/-- ✱11·39: two pointwise implications combine under conjunction. -/
theorem star_11_39_prop {α β : Type} (φ ψ χ θ : α → β → Prop) :
    (∀ x y, φ x y → ψ x y) →
    (∀ x y, χ x y → θ x y) →
    ∀ x y, φ x y ∧ χ x y → ψ x y ∧ θ x y := by
  intro hφ hχ x y h
  exact ⟨hφ x y h.1, hχ x y h.2⟩

/-- ✱11·391: two implications with a common antecedent are equivalent to
one implication into their conjunction. -/
theorem star_11_391_prop {α β : Type} (φ ψ χ : α → β → Prop) :
    ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, φ x y → χ x y)) ↔
      (∀ x y, φ x y → ψ x y ∧ χ x y) := by
  constructor
  · rintro ⟨hψ, hχ⟩ x y hφ
    exact ⟨hψ x y hφ, hχ x y hφ⟩
  · intro h
    exact ⟨fun x y hφ => (h x y hφ).1,
      fun x y hφ => (h x y hφ).2⟩

/-- ✱11·4: paired pointwise equivalences combine under conjunction. -/
theorem star_11_4_prop {α β : Type} (φ ψ χ θ : α → β → Prop) :
    (∀ x y, φ x y ↔ ψ x y) →
    (∀ x y, χ x y ↔ θ x y) →
    ∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ θ x y) := by
  intro hφ hχ x y
  exact and_congr (hφ x y) (hχ x y)

/-- ✱11·401: pointwise equivalence is preserved by conjunction with a
fixed pointwise factor. -/
theorem star_11_401_prop {α β : Type} (φ ψ χ : α → β → Prop) :
    (∀ x y, φ x y ↔ ψ x y) →
    ∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ χ x y) := by
  intro h x y
  exact and_congr (h x y) Iff.rfl

/-- ✱11·41: existential quantification distributes over disjunction in both
directions for the displayed pair of apparent variables. -/
theorem star_11_41_prop {α β : Type} (φ ψ : α → β → Prop) :
    ((∃ x y, φ x y) ∨ (∃ x y, ψ x y)) ↔
      (∃ x y, φ x y ∨ ψ x y) := by
  constructor
  · rintro (⟨x, y, h⟩ | ⟨x, y, h⟩)
    · exact ⟨x, y, Or.inl h⟩
    · exact ⟨x, y, Or.inr h⟩
  · rintro ⟨x, y, h | h⟩
    · exact Or.inl ⟨x, y, h⟩
    · exact Or.inr ⟨x, y, h⟩

end PM.Architecture.Star11Q282Kernel
