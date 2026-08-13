import Principia.Architecture.Star31ConverseKernel

namespace PM.Architecture.Star31ConverseKernel2

open PM.Architecture.Star31ConverseKernel

/-! Nine consecutive exact converse propositions following ✱31·16. -/

private def empty : Relation α := fun _ _ => False
private def universal : Relation α := fun _ _ => True

/-- The contextual definiens of `y = P̌ʻx`: `y` uniquely characterizes the
relata of `x` under `P`. -/
private def converseValueEquals (P : Relation α) (x y : α) : Prop :=
  ∀ z, P x z ↔ z = y

/-- Contextual existence of the descriptive value `P̌ʻx`. -/
private def converseValueExists (P : Relation α) (x : α) : Prop :=
  ∃ y, ∀ z, P x z ↔ z = y

/-- ✱31·17. `y = P̌ʻx ↔ (z)(xPz ↔ z=y)`. -/
theorem star_31_17 (P : Relation α) (x y : α) :
    converseValueEquals P x y ↔ (∀ z, P x z ↔ z = y) := Iff.rfl

/-- ✱31·18. Existence of `P̌ʻx` is existence of a uniquely characterized
relatum. -/
theorem star_31_18 (P : Relation α) (x : α) :
    converseValueExists P x ↔ ∃ y, ∀ z, P x z ↔ z = y := Iff.rfl

/-- ✱31·21. The converse of the null relation is null. -/
theorem star_31_21 : Cnv (empty : Relation α) = empty := rfl

/-- ✱31·22. The converse of the universal relation is universal. -/
theorem star_31_22 : Cnv (universal : Relation α) = universal := rfl

/-- ✱31·23. A relation's converse is universal iff the relation is. -/
theorem star_31_23 (P : Relation α) :
    converse P = universal ↔ P = universal := by
  constructor
  · intro h
    funext x y
    exact congrFun (congrFun h y) x
  · rintro rfl
    rfl

/-- ✱31·24. A relation's converse is null iff the relation is. -/
theorem star_31_24 (P : Relation α) :
    converse P = empty ↔ P = empty := by
  constructor
  · intro h
    funext x y
    exact congrFun (congrFun h y) x
  · rintro rfl
    rfl

/-- ✱31·32. Equality is preserved and reflected by converse. -/
theorem star_31_32 (P Q : Relation α) :
    P = Q ↔ converse P = converse Q := by
  constructor
  · rintro rfl
    rfl
  · intro h
    funext x y
    exact congrFun (congrFun h y) x

/-- ✱31·33. Converse is involutive. -/
theorem star_31_33 (P : Relation α) : Cnv (Cnv P) = P := rfl

/-- ✱31·34. `P = Q̌` iff `Q = P̌`. -/
theorem star_31_34 (P Q : Relation α) :
    P = converse Q ↔ Q = converse P := by
  constructor
  · intro h
    calc Q = converse (converse Q) := (star_31_33 Q).symm
      _ = converse P := congrArg converse h.symm
  · intro h
    calc P = converse (converse P) := (star_31_33 P).symm
      _ = converse Q := congrArg converse h.symm

end PM.Architecture.Star31ConverseKernel2
