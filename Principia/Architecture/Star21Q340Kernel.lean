import Principia.Architecture.Star12Q289Reducibility
import Principia.Architecture.Star21Q327Definition

/-! Exact mixed-relation kernels for PM I, Q340 (✱21·705 and ✱21·71). -/

namespace PM.Architecture.Star21Q340Kernel

abbrev Relation (Left : Sort u) (Right : Sort v) :=
  Star21Q327Definition.BinaryRelation Left Right

/-- PM I ✱21·705.  The mixed matrix has one class argument and one genuinely
binary relation argument; ✱12·11 supplies its predicative representative. -/
theorem star_21_705 {ClassCarrier : Sort u} {Left : Sort v} {Right : Sort w}
    (f : ClassCarrier → Relation Left Right → Prop) :
    ∃ g : Star12Q289Reducibility.Predicative₂
        ClassCarrier (Relation Left Right),
      ∀ α R, f α R ↔ g α R := by
  exact Star12Q289Reducibility.star_12_11 f

/-- PM I ✱21·71. Relation identity is indiscernibility with respect to every
predicative propositional function of a relation argument. -/
theorem star_21_71 (R S : Relation Left Right) :
    R = S ↔ ∀ g : Relation Left Right → Prop, g R → g S := by
  constructor
  · rintro rfl g h
    exact h
  · intro h
    exact h (fun T => R = T) rfl

end PM.Architecture.Star21Q340Kernel
