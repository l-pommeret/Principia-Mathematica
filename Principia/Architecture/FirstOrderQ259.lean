import Principia.Deduction.Ordered

namespace PM.Architecture.FirstOrderQ259

/-! Exact order-one target formulas for PM I ✱9·3, ·31, ·32 and ·33.
They are formulas, not yet claimed derivations.  A later proof must supply an
explicit `OrderedRuleBook` for this assigned order; no all-orders primitive
rule is introduced here. -/

def star_9_3_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  let p := OrderedFormula.always φ
  (p ∨ₒ p) ⊃ₒ p

def star_9_31_target (φ : Apparent Γ [.elementaryProposition]) :
    OrderedFormula Γ 1 :=
  let p := OrderedFormula.sometimes φ
  (p ∨ₒ p) ⊃ₒ p

def star_9_32_target (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.impElementaryToFirst q (FirstOrder.always φ))

def star_9_33_target (q : Elementary Γ)
    (φ : Apparent Γ [.elementaryProposition]) : OrderedFormula Γ 1 :=
  .firstOrder (FirstOrder.impElementaryToFirst q (FirstOrder.sometimes φ))

end PM.Architecture.FirstOrderQ259
