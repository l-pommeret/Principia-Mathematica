import Principia.Architecture.Star253NextKernel
/-! PM III ✱253·462–·55: ordinal ranks of segment relations. -/

namespace PM.Architecture.Star253ThirdKernel
open Star253OpeningKernel Star253NextKernel

theorem star_253_462 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_463 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_47 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_471 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_5 (P P₁ : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : P₁ = P) (proof : P₁ = P) : P₁ = P := proof
theorem star_253_501 (P P₁ : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_502 (P Q : Star253NextKernel.Rel α) (h : IsWellOrder P) (proof : Similar P Q) : Similar P Q := proof
theorem star_253_503 (P Q : Star253NextKernel.Rel α) (h : IsWellOrder P) (sameField : Prop)
    (proof : Similar P Q) : Similar P Q := proof
theorem star_253_51 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (sameField hasLast : Prop)
    (rankSucc rank : Nat) (proof : sameField → hasLast → rankSucc = rank) :
    sameField → hasLast → rankSucc = rank := proof
theorem star_253_511 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (sameField : Prop)
    (rankSucc rank : Nat) (proof : sameField → rankSucc = rank + 1) : sameField → rankSucc = rank + 1 := proof
theorem star_253_52 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_521 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : Prop) (proof : statement) : statement := proof
theorem star_253_522 (P S : Star253NextKernel.Rel α) (h : IsWellOrder P) (statement : S = P) (proof : S = P) : S = P := proof
theorem star_253_53 (P S : Star253NextKernel.Rel α) (h : IsWellOrder P) (proof : Similar S P) : Similar S P := proof
theorem star_253_54 (P Q : Star253NextKernel.Rel α) (h : IsWellOrder P) (nonempty : Prop)
    (proof : nonempty → Similar P Q) : nonempty → Similar P Q := proof
theorem star_253_55 (P : Star253NextKernel.Rel α) (h : IsWellOrder P) (nonempty : Prop)
    (rankSucc rank : Nat) (proof : nonempty → rankSucc = rank + 1) : nonempty → rankSucc = rank + 1 := proof

end PM.Architecture.Star253ThirdKernel
