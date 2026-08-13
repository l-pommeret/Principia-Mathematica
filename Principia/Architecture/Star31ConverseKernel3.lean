import Principia.Architecture.Star31ConverseKernel2

namespace PM.Architecture.Star31ConverseKernel3

open PM.Architecture.Star31ConverseKernel
open PM.Architecture.Star31ConverseKernel2

/-! The complete five-proposition remainder of PM I ✱31. -/

private def subrelation (P Q : Relation α) : Prop :=
  ∀ x y, P x y → Q x y

private def relationExists (P : Relation α) : Prop :=
  ∃ x y, P x y

/-- ✱31·4. Relation inclusion is preserved and reflected by converse. -/
theorem star_31_4 (P Q : Relation α) :
    subrelation P Q ↔ subrelation (converse P) (converse Q) := by
  constructor
  · intro h x y
    exact h y x
  · intro h x y
    exact h y x

/-- ✱31·41. `P ⊂ Q̌` iff `P̌ ⊂ Q`. -/
theorem star_31_41 (P Q : Relation α) :
    subrelation P (converse Q) ↔ subrelation (converse P) Q := by
  constructor
  · intro h x y
    exact h y x
  · intro h x y
    exact h y x

/-- ✱31·5. A relation exists iff its converse exists. -/
theorem star_31_5 (P : Relation α) :
    relationExists P ↔ relationExists (converse P) := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨y, x, h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨y, x, h⟩

/-- ✱31·51. Universal quantification over converse relations is equivalent
to universal quantification over relations. -/
theorem star_31_51 (f : Relation α → Prop) :
    (∀ P, f (converse P)) ↔ ∀ P, f P := by
  constructor
  · intro h P
    simpa using h (converse P)
  · intro h P
    exact h (converse P)

/-- ✱31·52. Existential quantification over converse relations is equivalent
to existential quantification over relations. -/
theorem star_31_52 (f : Relation α → Prop) :
    (∃ P, f (converse P)) ↔ ∃ P, f P := by
  constructor
  · rintro ⟨P, h⟩
    exact ⟨converse P, by simpa using h⟩
  · rintro ⟨P, h⟩
    exact ⟨converse P, by simpa using h⟩

end PM.Architecture.Star31ConverseKernel3
