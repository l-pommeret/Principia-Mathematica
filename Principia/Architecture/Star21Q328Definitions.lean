namespace PM.Architecture.Star21Q328Definitions

universe u v

/-- The explicit simple-type carrier of a PM binary relation extension. -/
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

/-- PM I ✱21·02: application of a relation abstract to its two arguments. -/
abbrev star_21_02 (φ : RelationExtension α β) (a : α) (b : β) : Prop :=
  φ a b

/-- PM I ✱21·03: the class of relations consists of extensions represented by
some predicative binary function.  In the documented simple-type embedding the
function and its extension share the same explicit carrier. -/
abbrev star_21_03 (α : Sort u) (β : Sort v) :
    RelationExtension α β → Prop :=
  fun R => ∃ φ : RelationExtension α β, R = φ

/-- Kernel reduction for the definiendum of ✱21·02. -/
theorem star_21_02_reduction (φ : RelationExtension α β) (a : α) (b : β) :
    star_21_02 φ a b ↔ φ a b := Iff.rfl

/-- Kernel reduction for the definiendum of ✱21·03. -/
theorem star_21_03_reduction (R : RelationExtension α β) :
    star_21_03 α β R ↔ ∃ φ : RelationExtension α β, R = φ := Iff.rfl

end PM.Architecture.Star21Q328Definitions
