/-!
# PM I ✱20·64, ✱20·7, and ✱20·701–703

Typed classes are membership predicates. Predicative class functions use the
same Lean function spaces as their matrices; this explicitly documents the
unramified embedding used for the four reducibility propositions.
-/

namespace PM.Architecture.Star20Q325ClassFunctions

abbrev TypedClass (α : Sort _) := α → Prop
abbrev PredicativeClassFunction (α : Sort _) := TypedClass α → Prop
abbrev PredicativeClassObjectFunction (α β : Sort _) :=
  TypedClass α → β → Prop
abbrev PredicativeObjectClassFunction (α β : Sort _) :=
  α → TypedClass β → Prop
abbrev PredicativeTwoClassFunction (α β : Sort _) :=
  TypedClass α → TypedClass β → Prop

/-- ✱20·64. Two universal class assertions yield both displayed instances. -/
theorem star_20_64 {C : Sort _} (f g : C → Prop) (β : C) :
    (∀ α, f α) ∧ (∀ α, g α) → f β ∧ g β := by
  rintro ⟨hf, hg⟩
  exact ⟨hf β, hg β⟩

/-- ✱20·7. Unary class-function reducibility in the unramified embedding. -/
theorem star_20_7 {α : Sort _} (f : TypedClass α → Prop) :
    ∃ g : PredicativeClassFunction α, ∀ a, f a ↔ g a :=
  ⟨f, fun _ => Iff.rfl⟩

/-- ✱20·701. Reducibility for a class in the first and an object in the
second argument place. -/
theorem star_20_701 {α β : Sort _}
    (f : TypedClass α → β → Prop) :
    ∃ g : PredicativeClassObjectFunction α β,
      ∀ φ x, f φ x ↔ g φ x :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱20·702. The corresponding reversed argument-place form. -/
theorem star_20_702 {α β : Sort _}
    (f : α → TypedClass β → Prop) :
    ∃ g : PredicativeObjectClassFunction α β,
      ∀ x φ, f x φ ↔ g x φ :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- ✱20·703. Reducibility for two typed class argument places. -/
theorem star_20_703 {α β : Sort _}
    (f : TypedClass α → TypedClass β → Prop) :
    ∃ g : PredicativeTwoClassFunction α β,
      ∀ φ ψ, f φ ψ ↔ g φ ψ :=
  ⟨f, fun _ _ => Iff.rfl⟩

end PM.Architecture.Star20Q325ClassFunctions
