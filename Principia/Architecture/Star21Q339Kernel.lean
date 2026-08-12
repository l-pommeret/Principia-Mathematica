import Principia.Architecture.Star20Q319Kernel
import Principia.Architecture.Star21Q328Definitions

namespace PM.Architecture.Star21Q339Kernel

open PM.Architecture.Star20Q319Kernel
open PM.Architecture.Star21Q328Definitions

/-- PM I ✱21·7: every proposition-valued function of a typed relation has a
predicative representative in the simple-type embedding. -/
theorem star_21_7 (f : RelationExtension α β → Prop) :
    ∃ g : RelationExtension α β → Prop, ∀ R, f R ↔ g R :=
  ⟨f, fun _ => Iff.rfl⟩

/-- PM I ✱21·701: relation/object function reducibility. -/
theorem star_21_701 (f : RelationExtension α β → γ → Prop) :
    ∃ g : RelationExtension α β → γ → Prop, ∀ R x, f R x ↔ g R x :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- PM I ✱21·702: object/relation function reducibility, with the predicative
representative in the printed `(R,x)` argument order. -/
theorem star_21_702 (f : γ → RelationExtension α β → Prop) :
    ∃ g : RelationExtension α β → γ → Prop, ∀ R x, f x R ↔ g R x :=
  ⟨fun R x => f x R, fun _ _ => Iff.rfl⟩

/-- PM I ✱21·703: function reducibility at two typed relation arguments. -/
theorem star_21_703
    (f : RelationExtension α β → RelationExtension γ δ → Prop) :
    ∃ g : RelationExtension α β → RelationExtension γ δ → Prop,
      ∀ R S, f R S ↔ g R S :=
  ⟨f, fun _ _ => Iff.rfl⟩

/-- PM I ✱21·704: function reducibility at a relation and a typed class
argument. -/
theorem star_21_704
    (f : RelationExtension α β → ClassExtension γ → Prop) :
    ∃ g : RelationExtension α β → ClassExtension γ → Prop,
      ∀ R a, f R a ↔ g R a :=
  ⟨f, fun _ _ => Iff.rfl⟩

end PM.Architecture.Star21Q339Kernel
