namespace PM.Architecture.Star21Q337Kernel

/-! Exact typed relation readings of PM I ✱21·58, ·6, ·61, ·62, ·63. -/

abbrev Relation (α : Type u) (β : Type v) := α → β → Prop

def extension (φ : α → β → Prop) : Relation α β := φ

/-- Contextual expansion of `ẑxẑyφ(x,y) = (℩R){R = ẑxẑyφ(x,y)}`.
The relation description is not made into a total term. -/
def RelationDescriptionEquals (φ : Relation α β) : Prop :=
  ∃ R : Relation α β, (∀ S, S = φ ↔ S = R) ∧ φ = R

/-- ✱21·58: a relation extension is the uniquely described relation equal
to that extension. -/
theorem star_21_58 (φ : Relation α β) : RelationDescriptionEquals φ := by
  exact ⟨φ, fun _ => Iff.rfl, rfl⟩

/-- ✱21·6: existential relation quantification is negated universal
negation, in PM's classical logic. -/
theorem star_21_6 (f : Relation α β → Prop) :
    (∃ R, f R) ↔ ¬(∀ R, ¬f R) := by
  classical
  simp

/-- ✱21·61: universal relation instantiation. -/
theorem star_21_61 (f : Relation α β → Prop) (S : Relation α β) :
    (∀ R, f R) → f S := by
  intro h
  exact h S

/-- ✱21·62: generalization from every admissible predicative binary
extension. The `extension` map makes the displayed admissible form explicit.
-/
theorem star_21_62 (f : Relation α β → Prop)
    (h : ∀ φ : α → β → Prop, f (extension φ)) :
    ∀ R : Relation α β, f R := by
  intro R
  exact h R

/-- ✱21·63: a fixed proposition may be moved outside universal relation
quantification. -/
theorem star_21_63 (p : Prop) (f : Relation α β → Prop) :
    (∀ R, p ∨ f R) → p ∨ (∀ R, f R) := by
  classical
  intro h
  by_cases hp : p
  · exact Or.inl hp
  · exact Or.inr (fun R => (h R).resolve_left hp)

end PM.Architecture.Star21Q337Kernel
