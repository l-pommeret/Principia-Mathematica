/-! # Principia Mathematica I, ✱85 — source vocabulary -/
namespace PM.FirstEdition.Volume1.Star85Source

abbrev Set' (α : Sort u) := α → Prop
abbrev Rel (α : Sort u) := α → α → Prop
def comp (P Q : Rel α) : Rel α := fun x z => ∃ y, P x y ∧ Q y z
def domain (R : Rel α) : Set' α := fun x => ∃ y, R x y
def range (R : Rel α) : Set' α := fun y => ∃ x, R x y
def restrict (R : Rel α) (s : Set' α) : Rel α := fun x y => R x y ∧ s y
def Delta (F : Rel α → Prop) (s : Set' α) (R : Rel α) : Prop :=
  F R ∧ ∀ x y, R x y → s y
def Similar (F G : Rel α → Prop) : Prop :=
  ∃ f : Rel α → Rel α, (∀ R, F R → G (f R)) ∧
    ∀ S, G S → ∃ R, F R ∧ f R = S
def PairwiseDisjoint (K : Set' (Set' α)) : Prop :=
  ∀ s, K s → ∀ t, K t → s ≠ t → ∀ x, ¬ (s x ∧ t x)

end PM.FirstEdition.Volume1.Star85Source
/- PM-VERBATIM-BEGIN PM1:✱85·1
✱85·1. ⊢: Q↾ λ∈Cls→1.⊃.DʻʻQ_Δʻλ=Dʻʻ∈_ΔʻQ⃗ʻʻλ
PM-VERBATIM-END PM1:✱85·1 -/
/- PM-VERBATIM-BEGIN PM1:✱85·11
✱85·11. ⊢:Q⃗↾λ∈ 1→1.⊃.Dʻʻ(P|Q⃗)_Δʻλ=DʻʻP_ΔʻQ⃗ʻʻλ
PM-VERBATIM-END PM1:✱85·11 -/
/- PM-VERBATIM-BEGIN PM1:✱85·111
✱85·111. ⊢: M∈∈_ΔʻQ⃗ʻʻλ.⊃.Dʻ(M|Q⃗↾λ)=DʻM [*82·3]
PM-VERBATIM-END PM1:✱85·111 -/
/- PM-VERBATIM-BEGIN PM1:✱85·112
✱85·112. ⊢: M∈∈_ΔʻQ⃗ʻʻλ.⊃.M|Q⃗↾ λ∈ Q_Δʻλ [*82·221 ∈, Q⃗/P, Q.*62·26 ]
PM-VERBATIM-END PM1:✱85·112 -/
/- PM-VERBATIM-BEGIN PM1:✱85·12
✱85·12. ⊢:Q⃗↾ λ∈ 1→1.⊃.DʻʻQ_Δʻλ=Dʻʻ∈_ΔʻQ⃗ʻʻλ
PM-VERBATIM-END PM1:✱85·12 -/
/- PM-VERBATIM-BEGIN PM1:✱85·13
✱85·13. ⊢:Q⃗↾λ∈ 1→1.R∈ Q_Δʻλ.⊃.R|CnvʻQ⃗∈∈_ΔʻQ⃗ʻʻλ
PM-VERBATIM-END PM1:✱85·13 -/
/- PM-VERBATIM-BEGIN PM1:✱85·14
✱85·14. ⊢:Q↾λ∈Cls→1.⊃.Q_Δʻλ sm ∈_ΔʻQ⃗ʻʻλ
PM-VERBATIM-END PM1:✱85·14 -/
/- PM-VERBATIM-BEGIN PM1:✱85·21
✱85·21. ⊢:α∈κ.M∈ P_Δʻsʻκ.⊃.M↾α∈ P_Δʻα [*80·6.*40·13]
PM-VERBATIM-END PM1:✱85·21 -/
/- PM-VERBATIM-BEGIN PM1:✱85·22
✱85·22. ⊢:M∈ P_Δʻsʻκ.⊃.M↾ |κ ↿ P̌_Δ∈ ∈_ΔʻP_Δʻʻκ.ṡʻDʻ(M↾ |κ ↿ P̌_Δ)=M
PM-VERBATIM-END PM1:✱85·22 -/
/- PM-VERBATIM-BEGIN PM1:✱85·24
✱85·24. ⊢.P_Δʻsʻκ⊂ṡʻʻDʻʻ∈_ΔʻP_Δʻʻκ
PM-VERBATIM-END PM1:✱85·24 -/
/- PM-VERBATIM-BEGIN PM1:✱85·241
✱85·241. ⊢:X∈∈_ΔʻP_Δʻʻκ.α∈κ.⊃.XʻP_Δʻα∈ P_Δʻα
PM-VERBATIM-END PM1:✱85·241 -/
/- PM-VERBATIM-BEGIN PM1:✱85·243
✱85·243. ⊢:κ∈Cls² excl.X∈∈_ΔʻP_Δʻʻκ.⊃.ṡʻDʻX∈ 1→Cls
PM-VERBATIM-END PM1:✱85·243 -/
/- PM-VERBATIM-BEGIN PM1:✱85·244
✱85·244. ⊢:X∈ ∈_ΔʻP_Δʻʻκ.⊃.ṡʻDʻX⪽P
PM-VERBATIM-END PM1:✱85·244 -/
/- PM-VERBATIM-BEGIN PM1:✱85·245
✱85·245. ⊢:X∈ ∈_ΔʻP_Δʻʻκ.⊃.ᗡʻṡʻDʻX=sʻκ
PM-VERBATIM-END PM1:✱85·245 -/
/- PM-VERBATIM-BEGIN PM1:✱85·25
✱85·25. ⊢:κ∈Cls² excl.X∈∈_ΔʻP_Δʻʻκ.⊃.ṡʻDʻX∈ P_Δʻsʻκ [*85·243·244·245.*80·14]
PM-VERBATIM-END PM1:✱85·25 -/
/- PM-VERBATIM-BEGIN PM1:✱85·26
✱85·26. ⊢:κ∈Cls² excl.⊃.ṡʻʻDʻʻ∈_ΔʻP_Δʻʻκ⊂ P_Δʻsʻκ
PM-VERBATIM-END PM1:✱85·26 -/
/- PM-VERBATIM-BEGIN PM1:✱85·27
✱85·27. ⊢:κ∈Cls² excl.⊃.P_Δʻsʻκ=ṡʻʻDʻʻ∈_ΔʻP_Δʻʻκ [*85·24·26]
PM-VERBATIM-END PM1:✱85·27 -/
/- PM-VERBATIM-BEGIN PM1:✱85·28
✱85·28. ⊢:κ∈Cls² excl.⊃.∈_Δʻsʻκ=ṡʻʻDʻʻ∈_Δʻ∈_Δʻʻκ [*85·27 ∈/P ]
PM-VERBATIM-END PM1:✱85·28 -/
/- PM-VERBATIM-BEGIN PM1:✱85·3
✱85·3. ⊢: M∈ P_Δʻα.z∈α.⊃.Mʻz⪽ṡʻDʻM.Mʻz⪽ṡʻP⃗ʻz
PM-VERBATIM-END PM1:✱85·3 -/
/- PM-VERBATIM-BEGIN PM1:✱85·31
✱85·31. ⊢:. z,w∈α.z≠ w.⊃z,w.ṡʻP⃗ʻz∩̇ṡʻP⃗ʻw=Λ̇:⊃: M,N∈ P_Δʻα.ṡʻDʻM=ṡʻDʻN.⊃.M=N
PM-VERBATIM-END PM1:✱85·31 -/
/- PM-VERBATIM-BEGIN PM1:✱85·32
✱85·32. ⊢:. z,w∈α .z≠ w.⊃z,w.sʻ CʻʻP⃗ʻ z∩ sʻ CʻʻP⃗ʻ w=Λ:⊃: M,N∈ P_Δʻα .ṡʻ Dʻ M=ṡʻ Dʻ N.⊃ .M=N
PM-VERBATIM-END PM1:✱85·32 -/
/- PM-VERBATIM-BEGIN PM1:✱85·33
✱85·33. ⊢:. z,w∈α .z≠ w.⊃z,w.sʻ DʻʻP⃗ʻ z∩ sʻ DʻʻP⃗ʻ w=Λ :⊃: M,N∈ P_Δʻα .ṡDʻ M=ṡʻ Dʻ N.⊃ .M=N [*41·43.*33·32.*85·31]
PM-VERBATIM-END PM1:✱85·33 -/
/- PM-VERBATIM-BEGIN PM1:✱85·34
✱85·34. ⊢:. z,w∈α.z ≠ w.⊃z,w.sʻᗡʻʻP⃗ʻz∩ sʻᗡʻʻP⃗ʻw=Λ:⊃: M,N∈ P_Δʻα.ṡʻDʻM=ṡʻDʻN.⊃.M=N [*41·44.*33·33.*85·31]
PM-VERBATIM-END PM1:✱85·34 -/
/- PM-VERBATIM-BEGIN PM1:✱85·4
✱85·4. ⊢:. λ,μ∈κ.λ≠μ.⊃_λ,μ.ṡʻλ∩̇ṡʻμ=Λ̇:⊃: M,N∈∈_Δʻκ.ṡʻDʻM=ṡʻDʻN.⊃.M=N [*85·31 ∈/P.*62·2 ]
PM-VERBATIM-END PM1:✱85·4 -/
/- PM-VERBATIM-BEGIN PM1:✱85·41
✱85·41. ⊢:. κ∈Cls² excl.⊃:α,β∈κ.α≠β.⊃.ṡʻP_Δʻα∩̇ṡʻP_Δʻβ=Λ̇
PM-VERBATIM-END PM1:✱85·41 -/
/- PM-VERBATIM-BEGIN PM1:✱85·42
✱85·42. ⊢: κ∈Cls² excl.M,N∈∈_ΔʻP_Δʻʻκ.ṡʻDʻM=ṡʻDʻN.⊃.M=N
PM-VERBATIM-END PM1:✱85·42 -/
/- PM-VERBATIM-BEGIN PM1:✱85·43
✱85·43. ⊢:κ∈Cls² excl.⊃.P_Δʻsʻκ sm ∈_ΔʻP_Δʻʻκ
PM-VERBATIM-END PM1:✱85·43 -/
/- PM-VERBATIM-BEGIN PM1:✱85·44
✱85·44. ⊢:κ∈Cls² excl.⊃.∈_Δʻsʻκ sm ∈_Δʻ∈_Δʻʻκ [*85·43 ∈/P ]
PM-VERBATIM-END PM1:✱85·44 -/
/- PM-VERBATIM-BEGIN PM1:✱85·45
✱85·45. ⊢:κ∩λ=Λ.⊃.∈_Δʻκ∪λ sm ∈_Δʻ(ιʻ∈_Δʻκ∪ιʻ∈_Δʻλ)
PM-VERBATIM-END PM1:✱85·45 -/
/- PM-VERBATIM-BEGIN PM1:✱85·5
✱85·5. P↧y=↓ yʻʻP⃗ʻy Df
PM-VERBATIM-END PM1:✱85·5 -/
/- PM-VERBATIM-BEGIN PM1:✱85·51
✱85·51. ⊢ .P_Δʻιʻx=↓ xʻʻP⃗ʻ x=P ↧ [*80·45.(*85·5)]
PM-VERBATIM-END PM1:✱85·51 -/
/- PM-VERBATIM-BEGIN PM1:✱85·52
✱85·52. ⊢ .P_Δʻʻιʻʻα =P↧ʻʻα [*37·35.*85·51]
PM-VERBATIM-END PM1:✱85·52 -/
/- PM-VERBATIM-BEGIN PM1:✱85·53
✱85·53. ⊢ .P_Δʻα =ṡʻʻ Dʻʻ∈_Δʻ P↧ʻʻα
PM-VERBATIM-END PM1:✱85·53 -/
/- PM-VERBATIM-BEGIN PM1:✱85·54
✱85·54. ⊢ .P_Δʻα sm ∈_Δʻ P↧ʻʻα
PM-VERBATIM-END PM1:✱85·54 -/
/- PM-VERBATIM-BEGIN PM1:✱85·55
✱85·55. ⊢ . P_Δʻα sm Dʻʻ∈_Δʻ P↧ʻʻα .P↧ʻʻα∈Cls² excl
PM-VERBATIM-END PM1:✱85·55 -/
/- PM-VERBATIM-BEGIN PM1:✱85·56
✱85·56. ⊢ :P↾α∈Cls→1.⊃ .∈_ΔʻP⃗ʻʻα sm ∈_Δʻ P↧ʻʻα [*85·14·54]
PM-VERBATIM-END PM1:✱85·56 -/
/- PM-VERBATIM-BEGIN PM1:✱85·6
✱85·6. ⊢ . ∈_Δʻʻιʻʻκ = μ̂{(∃β).β∈κ .μ = ↓ βʻʻβ}=∈↧ʻʻκ
PM-VERBATIM-END PM1:✱85·6 -/
/- PM-VERBATIM-BEGIN PM1:✱85·601
✱85·601. ⊢ .∈ ↧ α =↓ αʻʻ α .∈ ↧ α sm α .∈ ↧ʻʻ κ sm κ .∈ ↧ ∈ 1→1.E!∈ ↧ʻα
PM-VERBATIM-END PM1:✱85·601 -/
/- PM-VERBATIM-BEGIN PM1:✱85·61
✱85·61. ⊢ .∈ ↧ʻʻ κ ∈ Cls²excl.∈_Δʻ κ =ṡʻʻ Dʻʻ ∈_Δʻ ∈ ↧ ʻʻ κ .∈_Δʻ κ sm ∈_Δʻ ∈ ↧ʻʻ κ [*85·53·54·55 ∈/P ]
PM-VERBATIM-END PM1:✱85·61 -/
/- PM-VERBATIM-BEGIN PM1:✱85·62
✱85·62. ⊢ :∃ !∈_Δʻ κ .≡ .∃ !∈_Δʻ ∈ ↧ ʻʻ κ [*85·61.*73·36]
PM-VERBATIM-END PM1:✱85·62 -/
/- PM-VERBATIM-BEGIN PM1:✱85·63
✱85·63. ⊢ :∈ ↧ʻʻ Cl exʻ α ∈ Cls ex²excl:∃ !∈_Δʻ Cl exʻ α .≡ .∃ !∈_Δʻ ∈ ↧ʻʻ Cl exʻ α
PM-VERBATIM-END PM1:✱85·63 -/
/- PM-VERBATIM-BEGIN PM1:✱85·7
✱85·7. ⊢ :. β ∈ λ .⊃ _β .Rʻ β ⊂ β :M∈ ∈_Δʻ Rʻʻ λ :⊃. M| R↾ λ ∈ ∈_Δʻ λ .Dʻ (M| R↾ λ )=Dʻ M
PM-VERBATIM-END PM1:✱85·7 -/
/- PM-VERBATIM-BEGIN PM1:✱85·701
✱85·701. ⊢ :. β ∈ λ .⊃ _β .Rʻ β ⊂ β :⊃ .Dʻʻ ∈_Δʻ Rʻʻ λ ⊂ Dʻʻ ∈_Δʻ λ [*85·7]
PM-VERBATIM-END PM1:✱85·701 -/
/- PM-VERBATIM-BEGIN PM1:✱85·702
✱85·702. ⊢ :. β ∈ λ .⊃ _β .RʻClʻ β ∈Clʻβ :⊃ .Dʻʻ ∈_Δʻ RʻʻClʻʻ λ ⊂ Dʻʻ ∈_Δʻ λ [*85·701R| Cl/R ]
PM-VERBATIM-END PM1:✱85·702 -/
/- PM-VERBATIM-BEGIN PM1:✱85·71
✱85·71. ⊢ :R∈ ∈_ΔʻClʻʻλ .⊃ .Dʻʻ ∈_ΔʻDʻ R⊂ Dʻʻ ∈_Δʻ λ [*85·702.*83·2]
PM-VERBATIM-END PM1:✱85·71 -/
/- PM-VERBATIM-BEGIN PM1:✱85·72
✱85·72. ⊢ :. (Sʻʻ β )↿ S∈ 1→1:β ∈ λ .⊃ _β .Rʻ β ⊂ Sʻ β :⊃. Dʻʻ ∈_Δʻ Rʻʻ λ ⊂ Dʻʻ ∈_Δʻ Sʻʻ λ
PM-VERBATIM-END PM1:✱85·72 -/
/- PM-VERBATIM-BEGIN PM1:✱85·81
✱85·81. ⊢:. λ∈ Cls²excl:β∈λ.⊃_β.sʻᗡʻʻTʻ β⊂β:R∈∈_ΔʻTʻʻλ:⊃: β∈λ.⊃_β.(šʻDʻR)↾ β=RʻTʻβ
PM-VERBATIM-END PM1:✱85·81 -/
