import Principia.Architecture.Star34QProofBlock5

/-! # PM I, ✱34·1–12: the three remaining relative-product propositions. -/

namespace PM.Architecture.Star34QProofBlock7

open PM.Architecture.Star34QProofBlock
open PM.Architecture.Star34QProofBlock2

def meeting (P : Relation α β) (Q : Relation β γ) (x : α) (z : γ) :
    β → Prop := fun y => P x y ∧ Q y z

/-- ✱34·1. Pointwise membership in a relative product. -/
theorem star_34_1 (P : Relation α β) (Q : Relation β γ) (x : α) (z : γ) :
    compose P Q x z ↔ ∃ y, P x y ∧ Q y z := by
  rfl

/-- ✱34·11. A relative product holds exactly when the intermediate
meeting class is inhabited. -/
theorem star_34_11 (P : Relation α β) (Q : Relation β γ) (x : α) (z : γ) :
    compose P Q x z ↔ ∃ y, meeting P Q x z y := by
  rfl

/-- ✱34·12. The relative product is extensionally the relation whose
intermediate meeting class is inhabited. -/
theorem star_34_12 (P : Relation α β) (Q : Relation β γ) :
    compose P Q = fun x z => ∃ y, meeting P Q x z y := by
  rfl

end PM.Architecture.Star34QProofBlock7
