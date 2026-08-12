namespace PM.Architecture.Star13Q294Kernel

/-!
# PM I ✱13·192–✱13·196

Exact kernel-checked readings of the five displayed identity propositions.
-/

/-- ✱13·192: an object extensionally identical to `b` satisfies `ψ` exactly
when `b` does. -/
theorem star_13_192 {α : Type} (b : α) (ψ : α → Prop) :
    (∃ c, (∀ x, (x = b ↔ x = c)) ∧ ψ c) ↔ ψ b := by
  constructor
  · rintro ⟨c, hc, hψ⟩
    have hbc : b = c := (hc b).mp rfl
    exact hbc ▸ hψ
  · intro hψ
    exact ⟨b, fun _ => Iff.rfl, hψ⟩

/-- ✱13·193: equality transports the conjoined predication. -/
theorem star_13_193 {α : Type} (φ : α → Prop) (x y : α) :
    (φ x ∧ x = y) ↔ (φ y ∧ x = y) := by
  constructor <;> rintro ⟨hφ, rfl⟩ <;> exact ⟨hφ, rfl⟩

/-- ✱13·194: under `x = y`, adjoining the transported predication is
equivalent to the original conjunction. -/
theorem star_13_194 {α : Type} (φ : α → Prop) (x y : α) :
    (φ x ∧ x = y) ↔ (φ x ∧ φ y ∧ x = y) := by
  constructor
  · rintro ⟨hφ, rfl⟩
    exact ⟨hφ, hφ, rfl⟩
  · rintro ⟨hφ, _hφy, hxy⟩
    exact ⟨hφ, hxy⟩

/-- ✱13·195: existential elimination against identity. -/
theorem star_13_195 {α : Type} (φ : α → Prop) (x : α) :
    (∃ y, y = x ∧ φ y) ↔ φ x := by
  constructor
  · rintro ⟨_y, rfl, hφ⟩
    exact hφ
  · intro hφ
    exact ⟨x, rfl, hφ⟩

/-- ✱13·196: failure of `φ` at `x` is equivalent to every `φ`-object being
distinct from `x`. -/
theorem star_13_196 {α : Type} (φ : α → Prop) (x : α) :
    ¬ φ x ↔ ∀ y, φ y → y ≠ x := by
  constructor
  · intro hn y hy hxy
    exact hn (hxy ▸ hy)
  · intro h hn
    exact h x hn rfl

end PM.Architecture.Star13Q294Kernel
