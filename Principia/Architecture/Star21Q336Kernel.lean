namespace PM.Architecture.Star21Q336Kernel

universe u v

abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

/-- The contextual, choice-free carrier of the description occurring in
✱21·55/56: a relation together with its displayed characterization. -/
abbrev RelationDescription (φ : RelationExtension α β) :=
  { R : RelationExtension α β // ∀ x y, R x y ↔ φ x y }

/-- The canonical witness of the relation description. -/
def describedRelation (φ : RelationExtension α β) : RelationDescription φ :=
  ⟨φ, fun _ _ => Iff.rfl⟩

/-- PM I ✱21·53. -/
theorem star_21_53 (R : RelationExtension α β)
    (φ : RelationExtension α β → Prop) :
    (∀ S : RelationExtension α β, S = R → φ S) ↔ φ R := by
  constructor
  · intro h
    exact h R rfl
  · intro h S hSR
    cases hSR
    exact h

/-- PM I ✱21·54. -/
theorem star_21_54 (R : RelationExtension α β)
    (φ : RelationExtension α β → Prop) :
    (∃ S : RelationExtension α β, S = R ∧ φ S) ↔ φ R := by
  constructor
  · rintro ⟨S, rfl, h⟩
    exact h
  · intro h
    exact ⟨R, rfl, h⟩

/-- PM I ✱21·55, with the incomplete description represented contextually. -/
theorem star_21_55 (φ : RelationExtension α β) :
    φ = (describedRelation φ).1 := rfl

/-- PM I ✱21·56: the displayed relation description exists uniquely. -/
theorem star_21_56 (φ : RelationExtension α β) :
    ∃ R : RelationExtension α β,
      (∀ x y, R x y ↔ φ x y) ∧
      ∀ S : RelationExtension α β,
        (∀ x y, S x y ↔ φ x y) → S = R := by
  refine ⟨φ, fun _ _ => Iff.rfl, ?_⟩
  intro R hR
  funext x y
  exact propext (hR x y)

/-- PM I ✱21·57: any function of relations respects the displayed identity. -/
theorem star_21_57 (φ description : RelationExtension α β)
    (g : RelationExtension α β → Prop) :
    φ = description → (g φ ↔ g description) := by
  intro h
  cases h
  exact Iff.rfl

end PM.Architecture.Star21Q336Kernel
