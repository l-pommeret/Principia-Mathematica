import Principia.Syntax.Apparent

/-!
# PM I ✱9·6 — same assigned proposition type

This is the smallest typed witness needed for PM's statement.  It does not
identify propositions or add a semantic type universe: inhabitance records
only that both displayed objects already elaborate in one and the same Lean
carrier, which is the canonical representation of one assigned PM type.
-/

namespace PM.Architecture

/-- Evidence that two proposition expressions occupy the same assigned
carrier.  The shared type parameter is the entire content of the judgement. -/
inductive SameAssignedType {α : Type u} (left right : α) : Prop
  | witness : SameAssignedType left right

/-- Four expressions occupying one assigned proposition carrier. -/
structure SameAssignedType4 {α : Type u} (a b c d : α) : Prop where
  ab : SameAssignedType a b
  ac : SameAssignedType a c
  ad : SameAssignedType a d

end PM.Architecture

namespace PM.FirstEdition.Volume1.Star9

/-- PM I (1910), p. 142, ✱9·6.  `(x).φx`, its negation, `(∃x).φx`, and
its negation all inhabit the same explicitly assigned first-order carrier. -/
theorem star_9_6 {Γ Δ}
    (body : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.Architecture.SameAssignedType4
      (PM.FirstOrder.always body)
      (PM.FirstOrder.neg (PM.FirstOrder.always body))
      (PM.FirstOrder.sometimes body)
      (PM.FirstOrder.neg (PM.FirstOrder.sometimes body)) :=
  ⟨.witness, .witness, .witness⟩

end PM.FirstEdition.Volume1.Star9
