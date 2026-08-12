namespace PM.Architecture.Star11Q288Kernel

/-!
# PM I ✱11·71

The two independent apparent variables `z` and `w` are represented by the
types `α` and `β`. PM juxtaposition is `And`; formal implication is universal
closure of pointwise implication.
-/

/-- ✱11·71: provided both antecedent functions have an instance, their two
formal implications are jointly equivalent to the paired formal implication.
-/
theorem star_11_71 {α β : Type} (φ ψ : α → Prop) (χ θ : β → Prop) :
    ((∃ z, φ z) ∧ (∃ w, χ w)) →
      (((∀ z, φ z → ψ z) ∧ (∀ w, χ w → θ w)) ↔
        (∀ z w, φ z ∧ χ w → ψ z ∧ θ w)) := by
  rintro ⟨⟨z₀, hφ₀⟩, ⟨w₀, hχ₀⟩⟩
  constructor
  · rintro ⟨hφ, hχ⟩ z w ⟨hz, hw⟩
    exact ⟨hφ z hz, hχ w hw⟩
  · intro h
    constructor
    · intro z hz
      exact (h z w₀ ⟨hz, hχ₀⟩).1
    · intro w hw
      exact (h z₀ w ⟨hφ₀, hw⟩).2

end PM.Architecture.Star11Q288Kernel
