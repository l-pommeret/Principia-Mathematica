import Principia.Architecture.Star21Q328Definitions

namespace PM.Architecture.Star21Q333Kernel

open PM.Architecture.Star21Q328Definitions

/-- Extensional identity of two binary relation abstracts. -/
def RelationIdentity (ψ χ : RelationExtension α β) : Prop :=
  ∀ x y, ψ x y ↔ χ x y

/-- A propositional context on relation extensions, carrying exactly the
substitution-respect required of `f{R}`. -/
structure RelationContext (α : Sort u) (β : Sort v) where
  apply : RelationExtension α β → Prop
  respectsIdentity : ∀ {R S}, RelationIdentity R S → (apply R ↔ apply S)

/-- The eliminative contextual reading of `f{ẑxẑyψ(x,y)}`. -/
def RelationApplication (f : RelationContext α β)
    (ψ : RelationExtension α β) : Prop :=
  ∃ φ, RelationIdentity φ ψ ∧ f.apply φ

private theorem relationIdentity_refl (ψ : RelationExtension α β) :
    RelationIdentity ψ ψ := fun _ _ => Iff.rfl

private theorem application_iff (f : RelationContext α β)
    (ψ : RelationExtension α β) : RelationApplication f ψ ↔ f.apply ψ := by
  constructor
  · rintro ⟨φ, identity, hφ⟩
    exact (f.respectsIdentity identity).1 hφ
  · intro hψ
    exact ⟨ψ, relationIdentity_refl ψ, hψ⟩

/-- PM I ✱21·14. Relation identity eliminates to pointwise equivalence. -/
theorem star_21_14 (ψ χ : RelationExtension α β) :
    RelationIdentity ψ χ → ∀ x y, ψ x y ↔ χ x y :=
  fun identity => identity

/-- PM I ✱21·15. Pointwise equivalence is exactly relation identity. -/
theorem star_21_15 (ψ χ : RelationExtension α β) :
    (∀ x y, ψ x y ↔ χ x y) ↔ RelationIdentity ψ χ := by
  rfl

/-- PM I ✱21·151. Every binary relation extension has a predicative
representative in the documented simple-type embedding. -/
theorem star_21_151 (ψ : RelationExtension α β) :
    ∃ φ : RelationExtension α β, RelationIdentity ψ φ :=
  ⟨ψ, relationIdentity_refl ψ⟩

/-- PM I ✱21·16. There is a predicative representative on which the same
extensional relation context has an equivalent value. -/
theorem star_21_16 (f : RelationContext α β) (ψ : RelationExtension α β) :
    ∃ φ : RelationExtension α β, RelationApplication f ψ ↔ f.apply φ :=
  ⟨ψ, application_iff f ψ⟩

/-- PM I ✱21·17. A context true of every predicative representative is true
of an arbitrary relation through its eliminative application scope. -/
theorem star_21_17 (f : RelationContext α β) (ψ : RelationExtension α β) :
    (∀ φ : RelationExtension α β, f.apply φ) → RelationApplication f ψ := by
  intro universal
  exact ⟨ψ, relationIdentity_refl ψ, universal ψ⟩

end PM.Architecture.Star21Q333Kernel
