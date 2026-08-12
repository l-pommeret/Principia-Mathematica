import Principia.Architecture.Star21Q327Definition

/-! Exact eliminative definitions for PM I, Q330 (✱21·07--✱21·081). -/

namespace PM.Architecture.Star21Q330Definitions

abbrev Relation (Left : Sort u) (Right : Sort v) :=
  Star21Q327Definition.BinaryRelation Left Right

/-- PM I ✱21·07. -/
def star_21_07 (f : Relation Left Right → Prop) : Prop :=
  ∀ φ : Left → Right → Prop, f φ

/-- PM I ✱21·071. -/
def star_21_071 (f : Relation Left Right → Prop) : Prop :=
  ∃ φ : Left → Right → Prop, f φ

/-- PM I ✱21·072. The description remains contextually scoped. -/
def star_21_072 (φ f : Relation Left Right → Prop) : Prop :=
  ∃ S : Relation Left Right, (∀ R, φ R ↔ R = S) ∧ f S

/-- PM I ✱21·08. -/
def star_21_08
    (ψ : Relation Left Right → Relation Left' Right' → Prop)
    (f : (Relation Left Right → Relation Left' Right' → Prop) → Prop) : Prop :=
  ∃ φ : Relation Left Right → Relation Left' Right' → Prop,
    (∀ R S, ψ R S ↔ φ R S) ∧ f φ

/-- PM I ✱21·081. -/
theorem star_21_081
    (φ : Relation Left Right → Relation Left' Right' → Prop)
    (P : Relation Left Right) (Q : Relation Left' Right') :
    φ P Q ↔ φ P Q := Iff.rfl

end PM.Architecture.Star21Q330Definitions
