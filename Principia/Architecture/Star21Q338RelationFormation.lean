/-!
# PM I ✱21·631–64 — relation formation and quantifier analogues

The metalinguistic word “significant” is represented by an explicit formation
certificate for a proposition. Typed relation arguments make the source's
same-type side condition intrinsic.
-/

namespace PM.Architecture.Star21Q338RelationFormation

abbrev TypedRelation (α : Sort _) (β : Sort _) := α → β → Prop

/-- A minimal certificate that an expression has elaborated as a proposition;
it asserts no truth value for that proposition. -/
structure Significant (p : Prop) : Prop where
  formed : p = p

def significant (p : Prop) : Significant p := ⟨rfl⟩

/-- A function of a typed relation variable exists precisely as a uniformly
formed propositional family. -/
def RelationFunctionExists
    (f : TypedRelation α β → Prop) : Prop :=
  ∀ R, Significant (f R)

/-- ✱21·631. Substitution of a relation of the same indexed type preserves
and reflects significance. -/
theorem star_21_631
    (f : TypedRelation α β → Prop) (R S : TypedRelation α β) :
    Significant (f R) ↔ Significant (f S) := by
  exact ⟨fun _ => significant _, fun _ => significant _⟩

/-- ✱21·632. Having a propositional value at some relation is equivalent to
formation of the corresponding relation function. -/
theorem star_21_632 (f : TypedRelation α β → Prop) :
    (∃ R, Significant (f R)) ↔ RelationFunctionExists f := by
  constructor
  · intro _ R
    exact significant (f R)
  · intro hf
    let emptyRelation : TypedRelation α β := fun _ _ => False
    exact ⟨emptyRelation, hf emptyRelation⟩

/-- ✱21·633. The two universal relation binders may be interchanged. -/
theorem star_21_633
    (f : TypedRelation α β → TypedRelation γ δ → Prop) :
    (∀ R, ∀ S, f R S) → ∀ S, ∀ R, f R S := by
  exact fun h S R => h R S

/-- ✱21·64. Two universal relation assertions yield both displayed
instances at the relation `S`. -/
theorem star_21_64
    (f g : TypedRelation α β → Prop) (S : TypedRelation α β) :
    (∀ R, f R) ∧ (∀ R, g R) → f S ∧ g S := by
  rintro ⟨hf, hg⟩
  exact ⟨hf S, hg S⟩

end PM.Architecture.Star21Q338RelationFormation
