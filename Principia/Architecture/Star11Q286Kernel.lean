namespace PM.Architecture.Star11Q286Kernel

/-!
# PM I ✱11·57–✱11·59

Exact kernel-checked readings of the three displayed propositions. Since the
same unary matrices occur at both apparent-variable positions, `x` and `y`
have one common argument type.
-/

/-- ✱11·57: duplicating a universally quantified unary matrix over two
apparent variables does not change its assertion. -/
theorem star_11_57 {α : Type} (φ : α → Prop) :
    (∀ x, φ x) ↔ ∀ x y, φ x ∧ φ y := by
  constructor
  · intro h x y
    exact ⟨h x, h y⟩
  · intro h x
    exact (h x x).1

/-- ✱11·58: duplicating an existential witness for the same unary matrix
does not change its assertion. -/
theorem star_11_58 {α : Type} (φ : α → Prop) :
    (∃ x, φ x) ↔ ∃ x y, φ x ∧ φ y := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x, hx, hx⟩
  · rintro ⟨x, _y, hx, _hy⟩
    exact ⟨x, hx⟩

/-- ✱11·59: a unary formal implication is equivalent to the corresponding
two-variable implication between the duplicated conjunction matrices. -/
theorem star_11_59 {α : Type} (φ ψ : α → Prop) :
    (∀ x, φ x → ψ x) ↔
      ∀ x y, φ x ∧ φ y → ψ x ∧ ψ y := by
  constructor
  · intro h x y hφ
    exact ⟨h x hφ.1, h y hφ.2⟩
  · intro h x hφ
    exact (h x x ⟨hφ, hφ⟩).1

end PM.Architecture.Star11Q286Kernel
