/-! # ✱70 — Relations whose classes of referents and relata belong to given classes.

Project Gutenberg 78050, PM I, pp. 440–445.
-/
/- PM-VERBATIM-BEGIN PM1:✱70·01
✱70·01. α →β = Ř (R⃗ʻʻᗡʻR ⊂α. R⃖ʻʻDʻR⊂β) Df
PM-VERBATIM-END PM1:✱70·01 -/
/- PM-VERBATIM-BEGIN PM1:✱70·1
✱70·1. ⊢: R ∈ α →β.≡. R⃗ʻʻᗡʻR ⊂α. R⃖ʻʻDʻR⊂β [✱20·3.(✱70·01)]
PM-VERBATIM-END PM1:✱70·1 -/
/- PM-VERBATIM-BEGIN PM1:✱70·11
✱70·11.
⊢:. R ∈α →β.≡: y∈ᗡʻR. ⊃_y.R⃗ʻy∈α:x∈DʻR. ⊃ₓ.R⃖ʻx∈β [✱37·702·703.✱70·1]
PM-VERBATIM-END PM1:✱70·11 -/
/- PM-VERBATIM-BEGIN PM1:✱70·12
✱70·12.
⊢: R ∈α →β.≡. R⃗ʻʻV ⊂ α∪ιʻΛ.R⃖ʻʻV ⊂ β∪ιʻΛ [✱70·1.✱53·62·621]
PM-VERBATIM-END PM1:✱70·12 -/
/- PM-VERBATIM-BEGIN PM1:✱70·13
✱70·13. ⊢:. R ∈α →β.≡: (y). R⃗ʻy∈ α∪ιʻΛ : (x). R⃖ʻx∈β∪ιʻΛ
PM-VERBATIM-END PM1:✱70·13 -/
/- PM-VERBATIM-BEGIN PM1:✱70·14
✱70·14.
⊢:: R∈α →β. ≡ :. (y): R⃗ʻy∈α .∨. R⃗ʻy=Λ:.(x):R⃖ʻx∈β.∨.R⃖ʻx=Λ [✱70·13.✱51·236]
PM-VERBATIM-END PM1:✱70·14 -/
/- PM-VERBATIM-BEGIN PM1:✱70·15
✱70·15. ⊢:. R∈α →β.≡: ∃!R⃗ʻy. ⊃_y.R⃗ʻy∈α : ∃! R⃖ʻx .⊃ₓ .R⃖ʻx∈β [✱24·51.✱4·6.✱70·14]
PM-VERBATIM-END PM1:✱70·15 -/
/- PM-VERBATIM-BEGIN PM1:✱70·16
✱70·16.
⊢: R∈α →β.≡. DʻR⃗ ⊂ α∪ιʻΛ.DʻR⃖ ⊂ β∪ιʻΛ [✱37·78·781.✱70·12]
PM-VERBATIM-END PM1:✱70·16 -/
/- PM-VERBATIM-BEGIN PM1:✱70·17
✱70·17. ⊢:: Λ∈α .⊃:. R∈α →β.≡: (y). R⃗ʻy∈α: ∃!R⃖ʻx.⊃ₓ. R⃖ʻx∈β
PM-VERBATIM-END PM1:✱70·17 -/
/- PM-VERBATIM-BEGIN PM1:✱70·171
✱70·171. ⊢:: Λ∈β.⊃:. R∈α →β .≡: ∃! R⃗ʻy.⊃_y.R⃗ʻy∈α: (x). R⃖ʻx∈β [Proof as in ✱70·17]
PM-VERBATIM-END PM1:✱70·171 -/
/- PM-VERBATIM-BEGIN PM1:✱70·18
✱70·18.
⊢:: Λ∈α.Λ∈β.⊃:. R∈α →β .≡:(y). R⃗ʻy∈α:(x).R⃖ʻx∈β [Proof as in ✱70·17]
PM-VERBATIM-END PM1:✱70·18 -/
/- PM-VERBATIM-BEGIN PM1:✱70·2
✱70·2. ⊢.α →β=(α∪ιʻΛ) →β=α →(β∪ιʻΛ)=(α∪ιʻΛ) →(β∪ιʻΛ)
PM-VERBATIM-END PM1:✱70·2 -/
/- PM-VERBATIM-BEGIN PM1:✱70·21
✱70·21. ⊢.α →β=(α-ιʻΛ) →β=α →(β-ιʻΛ)=(α-ιʻΛ) →(β-ιʻΛ)
PM-VERBATIM-END PM1:✱70·21 -/
/- PM-VERBATIM-BEGIN PM1:✱70·22
✱70·22. ⊢.β →α=Cnvʻʻ(α →β)
PM-VERBATIM-END PM1:✱70·22 -/
/- PM-VERBATIM-BEGIN PM1:✱70·3
✱70·3. ⊢.α⊂γ.β⊂δ.⊃.α →β⊂γ →δ
PM-VERBATIM-END PM1:✱70·3 -/
/- PM-VERBATIM-BEGIN PM1:✱70·31
✱70·31. ⊢.(α →β)∩(γ →δ)=(α∩γ) →(β∩δ)
PM-VERBATIM-END PM1:✱70·31 -/
/- PM-VERBATIM-BEGIN PM1:✱70·32
✱70·32. ⊢.(α →β)∪(γ →δ)⊂(α∪γ) →(β∪δ)
PM-VERBATIM-END PM1:✱70·32 -/
/- PM-VERBATIM-BEGIN PM1:✱70·4
✱70·4. ⊢.α →Cls=R̂(R⃗ʻʻᗡʻR⊂α)
PM-VERBATIM-END PM1:✱70·4 -/
/- PM-VERBATIM-BEGIN PM1:✱70·41
✱70·41. ⊢.Cls →β=R̂(R⃖ʻʻDʻR⊂β) [Proof as in ✱70·4]
PM-VERBATIM-END PM1:✱70·41 -/
/- PM-VERBATIM-BEGIN PM1:✱70·42
✱70·42. ⊢.α →β=(α →Cls)∩(Cls →β) [✱70·4·41]
PM-VERBATIM-END PM1:✱70·42 -/
/- PM-VERBATIM-BEGIN PM1:✱70·43
✱70·43. ⊢:. R∈α →Cls.≡:y∈ᗡʻR.⊃_y.R⃗ʻy∈α [As in ✱70·11]
PM-VERBATIM-END PM1:✱70·43 -/
/- PM-VERBATIM-BEGIN PM1:✱70·431
✱70·431. ⊢:. R∈Cls →β.≡:x∈DʻR.⊃ₓ.R⃖ʻx∈β [As in ✱70·11]
PM-VERBATIM-END PM1:✱70·431 -/
/- PM-VERBATIM-BEGIN PM1:✱70·44
✱70·44. ⊢:R∈α →Cls.≡.R⃗ʻʻV⊂α∪ιʻΛ [As in ✱70·12]
PM-VERBATIM-END PM1:✱70·44 -/
/- PM-VERBATIM-BEGIN PM1:✱70·441
✱70·441. ⊢:R∈Cls →β.≡.R⃖ʻʻV⊂β∪ιʻΛ [As in ✱70·12]
PM-VERBATIM-END PM1:✱70·441 -/
/- PM-VERBATIM-BEGIN PM1:✱70·45
✱70·45. ⊢:R∈α →Cls.≡.(y).R⃗ʻy∈α∪ιʻΛ [As in ✱70·13]
PM-VERBATIM-END PM1:✱70·45 -/
/- PM-VERBATIM-BEGIN PM1:✱70·451
✱70·451. ⊢:R∈Cls →β.≡.(x).R⃖ʻx∈β∪ιʻΛ [As in ✱70·13]
PM-VERBATIM-END PM1:✱70·451 -/
/- PM-VERBATIM-BEGIN PM1:✱70·46
✱70·46. ⊢:. R∈α →Cls.≡:(y):R⃗ʻy∈α.∨.R⃗ʻy=Λ [As in ✱70·14]
PM-VERBATIM-END PM1:✱70·46 -/
/- PM-VERBATIM-BEGIN PM1:✱70·461
✱70·461. ⊢:. R∈Cls →β.≡:(x):R⃖ʻx∈β.∨.R⃖ʻx=λ [As in ✱70·14]
PM-VERBATIM-END PM1:✱70·461 -/
/- PM-VERBATIM-BEGIN PM1:✱70·47
✱70·47. ⊢:. R∈α →Cls.≡:∃!R⃗ʻy.⊃_y.R⃗ʻy∈α [As in ✱70·15]
PM-VERBATIM-END PM1:✱70·47 -/
/- PM-VERBATIM-BEGIN PM1:✱70·471
✱70·471. ⊢:. R∈Cls →β.≡:∃!R⃖ʻx.⊃ₓ.R⃖ʻx∈β [As in ✱70·15]
PM-VERBATIM-END PM1:✱70·471 -/
/- PM-VERBATIM-BEGIN PM1:✱70·48
✱70·48. ⊢: R∈α →Cls.≡.DʻR⃗⊂α∪ιʻΛ [As in ✱70·16]
PM-VERBATIM-END PM1:✱70·48 -/
/- PM-VERBATIM-BEGIN PM1:✱70·481
✱70·481. ⊢: R∈Cls →β.≡.DʻR⃗⊂β∪ιʻΛ [As in ✱70·16]
PM-VERBATIM-END PM1:✱70·481 -/
/- PM-VERBATIM-BEGIN PM1:✱70·5
✱70·5. ⊢.Cls →α=Cnvʻʻ( →αCls).α →Cls=Cnvʻʻ(Cls →α) [✱70·22]
PM-VERBATIM-END PM1:✱70·5 -/
/- PM-VERBATIM-BEGIN PM1:✱70·51
✱70·51. ⊢:. ξ,η∈α.⊃_ξ,η.ξ∩η∈α∪ιʻΛ:⊃:R,S∈ →αCls.⊃.R∩̇S∈α →Cls
PM-VERBATIM-END PM1:✱70·51 -/
/- PM-VERBATIM-BEGIN PM1:✱70·52
✱70·52.
⊢:.ξ,η∈β.⊃_ξ,η.ξ∩η∈β∪ιʻΛ:⊃:R, S∈Cls →β.⊃.R∩̇S∈Cls →β [Proof as in ✱70·51]
PM-VERBATIM-END PM1:✱70·52 -/
/- PM-VERBATIM-BEGIN PM1:✱70·53
✱70·53. ⊢:.ξ,η∈α.⊃_ξ,η.ξ∩η∈α∪ιʻΛ:ξ,η∈ β.⊃_ξ,η.ξ∩η∈β∪ιʻΛ:⊃: R,S∈α →β.⊃.R∩̇S∈α →β
PM-VERBATIM-END PM1:✱70·53 -/
/- PM-VERBATIM-BEGIN PM1:✱70·54
✱70·54. ⊢:ᗡʻR∩ᗡʻS=λ.R,S∈α →Cls.⊃.R⊍S∈α →Cls
PM-VERBATIM-END PM1:✱70·54 -/
/- PM-VERBATIM-BEGIN PM1:✱70·55
✱70·55. ⊢:DʻR∩DʻS=Λ.R,S∈Cls →β.⊃.R⊍S∈Cls →β [Proof as in ✱70·54]
PM-VERBATIM-END PM1:✱70·55 -/
/- PM-VERBATIM-BEGIN PM1:✱70·56
✱70·56. ⊢:DʻR∩DʻS=Λ.ᗡʻR∩ᗡʻS=Λ.R,S∈α →β.⊃.R⊍S∈α →β [✱70·54·55·42]
PM-VERBATIM-END PM1:✱70·56 -/
/- PM-VERBATIM-BEGIN PM1:✱70·57
✱70·57. ⊢:CʻR∩CʻS=Λ.R, S∈α →β.⊃.R⊍S∈α →β
PM-VERBATIM-END PM1:✱70·57 -/
/- PM-VERBATIM-BEGIN PM1:✱70·6
✱70·6. ⊢:S∈α →Cls.Rʻʻʻα⊃α∪ιʻΛ.⊃.R| S∈α →Cls
PM-VERBATIM-END PM1:✱70·6 -/
/- PM-VERBATIM-BEGIN PM1:✱70·61
✱70·61. ⊢:R∈Cls →β.Šʻʻʻβ⊂β∪ιʻΛ.⊃.R| S∈Cls →β [As in ✱70·6]
PM-VERBATIM-END PM1:✱70·61 -/
/- PM-VERBATIM-BEGIN PM1:✱70·62
✱70·62. ⊢:R∈α →Cls.⊃.R↾∈α →Cls
PM-VERBATIM-END PM1:✱70·62 -/
/- PM-VERBATIM-BEGIN PM1:✱70·63
✱70·63. ⊢:R∈Cls →β.⊃.δ↿ R∈Cls →β [As in ✱70·62]
PM-VERBATIM-END PM1:✱70·63 -/

namespace PM.FirstEdition.Volume1.Star70Source

abbrev Set' (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
abbrev Class (α : Sort u) := Set' α → Prop

def empty : Set' α := fun _ => False
def image (R : Rel α) (y : α) : Set' α := fun x => R x y
def converseImage (R : Rel α) (x : α) : Set' α := fun y => R x y
def nonempty (s : Set' α) : Prop := ∃ x, s x
def Arrow (A B : Class α) (R : Rel α) : Prop :=
  (∀ y, nonempty (image R y) → A (image R y)) ∧
  (∀ x, nonempty (converseImage R x) → B (converseImage R x))
def Converse (R : Rel α) : Rel α := fun x y => R y x
def Inter (A B : Class α) : Class α := fun s => A s ∧ B s
def Union (A B : Class α) : Class α := fun s => A s ∨ B s
def Subclass (A B : Class α) : Prop := ∀ s, A s → B s
def RelUnion (R S : Rel α) : Rel α := fun x y => R x y ∨ S x y
def disjoint (s t : Set' α) : Prop := ∀ x, ¬ (s x ∧ t x)
def domainRestrict (R : Rel α) (c : Set' α) : Rel α := fun x y => c x ∧ R x y
def rangeRestrict (c : Set' α) (R : Rel α) : Rel α := fun x y => R x y ∧ c y

end PM.FirstEdition.Volume1.Star70Source
