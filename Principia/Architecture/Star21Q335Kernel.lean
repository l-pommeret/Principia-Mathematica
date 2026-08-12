namespace PM.Architecture.Star21Q335Kernel

/-- A type-correct binary relation, kept heterogeneous because PM's two
argument places need not have the same type. -/
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

/-- A predicative relation code and its extensional interpretation.  The
wrapper keeps the `φ!` code distinct from its extension. -/
structure PredicativeRelationCode (α : Sort u) (β : Sort v) where
  extension : Relation α β

/-- The class `Rel` consists exactly of extensions of predicative relation
codes, as in ✱21·03/·4. -/
def IsPredicativeRelation (R : Relation α β) : Prop :=
  ∃ φ : PredicativeRelationCode α β, R = φ.extension

/-- Exact relational re-abstraction at PM I ✱21·32. -/
theorem star_21_32 (φ : Relation α β) :
    (fun x y => φ x y) = φ := by
  rfl

/-- Exact extensional equality characterization at PM I ✱21·33. -/
theorem star_21_33 (R φ : Relation α β) :
    R = φ ↔ ∀ x y, R x y ↔ φ x y := by
  constructor
  · rintro rfl x y
    exact Iff.rfl
  · intro pointwise
    funext x y
    exact propext (pointwise x y)

/-- Exact membership reduction at PM I ✱21·4. -/
theorem star_21_4 (R : Relation α β) :
    IsPredicativeRelation R ↔
      ∃ φ : PredicativeRelationCode α β, R = φ.extension := by
  rfl

/-- Exact predicative-relation membership assertion at PM I ✱21·41.  Its
code is the local witness supplied by the prior ✱21·151 representability
principle; no global inverse or choice function is introduced. -/
theorem star_21_41 (φ : Relation α β) :
    IsPredicativeRelation φ := by
  exact ⟨⟨φ⟩, rfl⟩

/-- Exact application/re-extension identity at PM I ✱21·42. -/
theorem star_21_42 (R : Relation α β) :
    (fun x y => R x y) = R := by
  rfl

end PM.Architecture.Star21Q335Kernel
