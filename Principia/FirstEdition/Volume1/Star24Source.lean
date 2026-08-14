/-! # Source-critical transcription: *24, null and universal classes -/

/- PM-VERBATIM-BEGIN PM1:✱24·01
✱24·01. V = ẑx(x = x)  Df
PM-VERBATIM-END PM1:✱24·01 -/
/- PM-VERBATIM-BEGIN PM1:✱24·02
✱24·02. Λ = −V  Df
PM-VERBATIM-END PM1:✱24·02 -/
/- PM-VERBATIM-BEGIN PM1:✱24·03
✱24·03. ∃!α .= . (∃x) . x ε α  Df
PM-VERBATIM-END PM1:✱24·03 -/
/- PM-VERBATIM-BEGIN PM1:✱24·1
✱24·1. ⊢ . Λ ≠ V  [✱22·351.(✱24·02)]
PM-VERBATIM-END PM1:✱24·1 -/
/- PM-VERBATIM-BEGIN PM1:✱24·101
✱24·101. ⊢ . V = −Λ  [✱22·831.(✱24·02)]
PM-VERBATIM-END PM1:✱24·101 -/
/- PM-VERBATIM-BEGIN PM1:✱24·102
✱24·102. ⊢ : (x) . φx .≡ . ẑz(φz) = V
Dem.
⊢.*13·15.*5·501. ⊃⊢:. φ x.≡:φ x.≡.x=x:.
[*10·11·271] ⊃⊢:. (x).φ x.≡:(x):φ x.≡.x = x:
[*20·15] ≡:ẑ(φ z)=ẑ(x=x):
[*24·01)] ≡:ẑ(φ z)=V:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·102 -/
/- PM-VERBATIM-BEGIN PM1:✱24·103
✱24·103. ⊢ : (x) . ∼φx .≡ . ẑz(φz) = Λ
Dem.
⊢.*24·102.⊃⊢:.(x).∼φ x. ≡:ẑ(∼φ z)=V:
[*22·392] ≡:-ẑ(φ z)=V:
[*22·831] ≡:ẑ(φ z)=-V:
[(*24·02)] ≡:ẑ(φ z)=Λ:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·103 -/
/- PM-VERBATIM-BEGIN PM1:✱24·104
✱24·104. ⊢ . (x) . x ε V
Dem.
⊢.*20·3.⊃⊢: x∈V.≡.x=x (1)
⊢.(1).*13·15.*10·11·271.⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·104 -/
/- PM-VERBATIM-BEGIN PM1:✱24·105
✱24·105. ⊢ . (x) . x ∼ε Λ
Dem.
⊢.*22·35. ⊃⊢: x∈Λ.≡.x∼∈V:
[*4·12] ⊃⊢: x∼∈V.≡.x∈V (1)
⊢.[(1).*10·11·271.*24·104]. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·105 -/
/- PM-VERBATIM-BEGIN PM1:✱24·11
✱24·11. ⊢ . (α) . α ⊂ V
Dem.
⊢.*24·104.*10·1. ⊃⊢.x∈V.
[Simp] ⊃⊢: x∈α.⊃.x∈V:
[*10·11.*22·1] ⊃⊢: α⊂V
[*10·11] ⊃⊢:(α).α⊂V:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·11 -/
/- PM-VERBATIM-BEGIN PM1:✱24·12
✱24·12. ⊢ . (α) . Λ ⊂ α
Dem.
⊢.*24·105.*10·1. ⊃⊢.x∼∈Λ.
[*2·21] ⊃⊢: x∈Λ.⊃.x∈α (1)
⊢.(1).*10·11.*22·1.⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·12 -/
/- PM-VERBATIM-BEGIN PM1:✱24·13
✱24·13. ⊢ : α = Λ .≡ . α ⊂ Λ
Dem.
⊢.*24·12.*4·73.⊃⊢: α⊂Λ. ≡.α⊂Λ.Λ⊂α.
[*22·41] ≡.α = Λ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·13 -/
/- PM-VERBATIM-BEGIN PM1:✱24·14
✱24·14. ⊢ : (x) . x ε α .≡ . α = V
Dem.
⊢.*24·102.⊃⊢:(x).x ∈ α. ≡.x̂(x ∈ α)=V.
[*20·32] ≡.α = V:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·14 -/
/- PM-VERBATIM-BEGIN PM1:✱24·141
✱24·141. ⊢ : V ⊂ α .≡ . V = α
Dem.
⊢.*24·11.*4·73.⊃⊢:V⊂ α. ≡.α⊂V.V⊂α.
[*22·41] ≡.α=V:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·141 -/
/- PM-VERBATIM-BEGIN PM1:✱24·15
✱24·15. ⊢ : (x) . x ∼ε α .≡ . α = Λ
Dem.
⊢.*24·103.⊃⊢:(x).x∼∈α. ≡.x̂(x ∈ α)=Λ.
[*20·32] ≡.α =Λ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·15 -/
/- PM-VERBATIM-BEGIN PM1:✱24·17
✱24·17. ⊢ : α = V .≡ . −α = Λ  [✱22·83.(✱24·02)]
PM-VERBATIM-END PM1:✱24·17 -/
/- PM-VERBATIM-BEGIN PM1:✱24·21
✱24·21. ⊢ . α ∩ −α = V  [✱24·103.*22·89]
PM-VERBATIM-END PM1:✱24·21 -/
/- PM-VERBATIM-BEGIN PM1:✱24·22
✱24·22. ⊢ . α ∪ −α = V  [✱22·88.*24·102]
PM-VERBATIM-END PM1:✱24·22 -/
/- PM-VERBATIM-BEGIN PM1:✱24·23
✱24·23. ⊢ . α ∩ Λ = Λ  [✱24·12.*22·621]
PM-VERBATIM-END PM1:✱24·23 -/
/- PM-VERBATIM-BEGIN PM1:✱24·24
✱24·24. ⊢ . α ∪ Λ = α  [✱24·12.*22·62]
PM-VERBATIM-END PM1:✱24·24 -/
/- PM-VERBATIM-BEGIN PM1:✱24·26
✱24·26. ⊢ . α ∩ V = α  [✱22·621.*24·11]
PM-VERBATIM-END PM1:✱24·26 -/
/- PM-VERBATIM-BEGIN PM1:✱24·27
✱24·27. ⊢ . α ∪ V = V  [✱22·62.*24·11]
PM-VERBATIM-END PM1:✱24·27 -/
/- PM-VERBATIM-BEGIN PM1:✱24·3
✱24·3. ⊢ : α ⊂ β .≡ . α − β = Λ
Dem.
⊢.*4·53·6.⊃
⊢:. x ∈ α.⊃.x ∈ β: ≡:∼(x ∈ α.x∼β):
[*22·35] ≡:∼(x ∈ α.x ∈ - β):
[*22·33] ≡:∼(x ∈ α - β) (1)
⊢.(1).*10·11·271.⊃
⊢: α⊂β.≡.(x).∼(x ∈ α - β).
[*24·15] ≡.α - β =Λ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·3 -/
/- PM-VERBATIM-BEGIN PM1:✱24·31
✱24·31. ⊢ : α ⊂ β .≡ . −α ∪ β = V
Dem.
⊢.*4·6. ⊃⊢:. x ∈ α.⊃.x∈ β:≡:x∼∈ α.∨.x∈ β:.
[*10·11·271] ⊃⊢:. α⊂β.≡:(x): x∼∈ α.∨.x∈ β:
[*22·35] ≡:(x):x∈ - α.∨.x∈ β:
[*22·34] ≡:(x).x∈(-α∪β):
[*24·14] ≡: -α∪β=V:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·31 -/
/- PM-VERBATIM-BEGIN PM1:✱24·311
✱24·311. ⊢ : α ⊂ −β .≡ . α ∩ β = Λ
Dem.
⊢.*22·35.⊃⊢:. x∈ α.⊃.x∈ - β: ≡: x∈ α.⊃.x∼∈ β:
[*4·51·62] ≡:∼(x∈ α.x∈ β):
[*22·33] ≡:∼(x∈ α∩β) (1)
⊢.(1).*10·11·271.⊃⊢: α⊂ - β. ≡.(x).x∼∈ α∩β.
[*24·15] ≡.α∩β=Λ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·311 -/
/- PM-VERBATIM-BEGIN PM1:✱24·312
✱24·312. ⊢ : −α ⊂ β .≡ . α ∪ β = V
Dem.
⊢.*22·35.⊃⊢:. - α⊂β. ≡:x∼∈ α.⊃ₓ.x∈ β:
[*4·64] ≡:(x):x∈ α.∨.x∈ β:
[*22·34] ≡:(x).x∈ α∪β:
[*24·14] ≡:α∪β=V:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·312 -/
/- PM-VERBATIM-BEGIN PM1:✱24·313
✱24·313. ⊢ : α ∩ β = Λ .≡ . α = α − β  [✱24·311.*22·621]
PM-VERBATIM-END PM1:✱24·313 -/
/- PM-VERBATIM-BEGIN PM1:✱24·32
✱24·32. ⊢ : α ∪ β = Λ .≡ . α = Λ . β = Λ
Dem.
⊢.*24·13.⊃⊢:. α∪β=Λ. ≡:α∪β⊂Λ:
[*22·59] ≡: α⊂Λ.β⊂Λ:
[*24·13] ≡: α=Λ.β=Λ:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱24·32 -/
/- PM-VERBATIM-BEGIN PM1:✱24·33
✱24·33. ⊢ : α = V .⊃ . α ∪ β = V
PM-VERBATIM-END PM1:✱24·33 -/
/- PM-VERBATIM-BEGIN PM1:✱24·34
✱24·34. ⊢ : α = Λ .⊃ . α ∩ β = Λ  [✱22·481.*24·23]
PM-VERBATIM-END PM1:✱24·34 -/
/- PM-VERBATIM-BEGIN PM1:✱24·35
✱24·35. ⊢ : α = V .⊃ . α ∩ β = β  [✱22·481.*24·26]
PM-VERBATIM-END PM1:✱24·35 -/
/- PM-VERBATIM-BEGIN PM1:✱24·36
✱24·36. ⊢ : α = Λ .⊃ . α ∪ β = β  [✱22·551.*24·24]
PM-VERBATIM-END PM1:✱24·36 -/
/- PM-VERBATIM-BEGIN PM1:✱24·37
✱24·37. ⊢ : α ∩ β = Λ .≡ : x ε α . y ε β .⊃ₓ,ᵧ . x ≠ y
PM-VERBATIM-END PM1:✱24·37 -/
/- PM-VERBATIM-BEGIN PM1:✱24·38
✱24·38. ⊢ : α ∩ β = Λ .⊃ : α ≠ β .∨ . α = Λ . β = Λ
PM-VERBATIM-END PM1:✱24·38 -/
/- PM-VERBATIM-BEGIN PM1:✱24·39
✱24·39. ⊢ : α ∩ β = Λ .≡ : x ε α .⊃ₓ . x ∼ε β  [✱24·311.*22·35]
PM-VERBATIM-END PM1:✱24·39 -/
/- PM-VERBATIM-BEGIN PM1:✱24·4
✱24·4. ⊢ : α ∩ β = Λ .≡ . (α ∪ β) − α = β .≡ . (α ∪ β) − β = α
PM-VERBATIM-END PM1:✱24·4 -/
/- PM-VERBATIM-BEGIN PM1:✱24·401
✱24·401. ⊢ : β ⊂ α .⊃ . (β ∪ γ) − α = γ − α
PM-VERBATIM-END PM1:✱24·401 -/
/- PM-VERBATIM-BEGIN PM1:✱24·402
✱24·402. ⊢ : α ∩ β = Λ . ξ ⊂ α . η ⊂ β .⊃ . ξ ∩ η = Λ
PM-VERBATIM-END PM1:✱24·402 -/
/- PM-VERBATIM-BEGIN PM1:✱24·41
✱24·41. ⊢ . α = (α ∩ β) ∪ (α − β)
PM-VERBATIM-END PM1:✱24·41 -/
/- PM-VERBATIM-BEGIN PM1:✱24·411
✱24·411. ⊢ : β ⊂ α .⊃ . α = β ∪ (α − β)
PM-VERBATIM-END PM1:✱24·411 -/
/- PM-VERBATIM-BEGIN PM1:✱24·412
✱24·412. ⊢ : β ⊂ α . γ ⊂ β .⊃ . (α − β) ∪ (β − γ) = α − γ
PM-VERBATIM-END PM1:✱24·412 -/
/- PM-VERBATIM-BEGIN PM1:✱24·42
✱24·42. ⊢ : α ∩ β ⊂ γ . α − β ⊂ γ .≡ . α ⊂ γ
PM-VERBATIM-END PM1:✱24·42 -/
/- PM-VERBATIM-BEGIN PM1:✱24·43
✱24·43. ⊢ : α − β ⊂ γ .≡ . α ⊂ β ∪ γ
PM-VERBATIM-END PM1:✱24·43 -/
/- PM-VERBATIM-BEGIN PM1:✱24·431
✱24·431. ⊢ . (α ∪ γ) ∩ (β ∪ −γ) = (α ∩ γ) ∪ (α − γ) ∪ (β ∩ γ)
PM-VERBATIM-END PM1:✱24·431 -/
/- PM-VERBATIM-BEGIN PM1:✱24·432
✱24·432. ⊢ . (α − γ) ∪ (β ∩ γ) = (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ)
PM-VERBATIM-END PM1:✱24·432 -/
/- PM-VERBATIM-BEGIN PM1:✱24·44
✱24·44. ⊢ . (α ∪ γ) ∩ (β ∪ −γ) = (α ∩ −γ) ∪ (β ∩ γ)  [✱24·431·432]
PM-VERBATIM-END PM1:✱24·44 -/
/- PM-VERBATIM-BEGIN PM1:✱24·45
✱24·45. ⊢ : (α ∩ γ) ∪ (β − γ) = Λ .≡ . β ⊂ γ . γ ⊂ −α
PM-VERBATIM-END PM1:✱24·45 -/
/- PM-VERBATIM-BEGIN PM1:✱24·46
✱24·46. ⊢ : (α ∩ γ) ∪ (β − γ) = Λ .⊃ . α ∩ β = Λ
PM-VERBATIM-END PM1:✱24·46 -/

/- PM-VERBATIM-BEGIN PM1:✱24·55
✱24·55. ⊢:∼(α⊃β).≡.∃!α - β [✱24·3.Transp.✱24·54]
PM-VERBATIM-END PM1:✱24·55 -/
/- PM-VERBATIM-BEGIN PM1:✱24·56
✱24·56. ⊢:. ∃!(α∪β).≡:∃!α.∨.∃!β [✱10·42.✱22·34]
PM-VERBATIM-END PM1:✱24·56 -/
/- PM-VERBATIM-BEGIN PM1:✱24·561
✱24·561. ⊢: ∃!(α∩β).⊃.∃!α.∃!β [✱10·5.✱22·33]
PM-VERBATIM-END PM1:✱24·561 -/
/- PM-VERBATIM-BEGIN PM1:✱24·47
✱24·47. ⊢:α∩β=Λ.α∪β=γ.≡.α⊂γ.β=γ - α
PM-VERBATIM-END PM1:✱24·47 -/
/- PM-VERBATIM-BEGIN PM1:✱24·48
✱24·48. ⊢:. ξ⊂α.ξ'⊂α.η⊂β.η'⊂β.α∩β =Λ.⊃: ξ∪η=ξ'∪η'.≡.ξ=ξ'.η=η'
PM-VERBATIM-END PM1:✱24·48 -/
/- PM-VERBATIM-BEGIN PM1:✱24·481
✱24·481. ⊢:. α∩β=Λ.α∩γ=Λ.⊃: α∪β=α∪γ.≡.β=γ
PM-VERBATIM-END PM1:✱24·481 -/
/- PM-VERBATIM-BEGIN PM1:✱24·482
✱24·482. ⊢:. ξ⊂α.η⊂β.α∩β=Λ.⊃: ξ∪η=α∪β.≡.ξ=α.η=β [✱24·48 α, β/ξ', η'.✱22·42 ]
PM-VERBATIM-END PM1:✱24·482 -/
/- PM-VERBATIM-BEGIN PM1:✱24·49
✱24·49. ⊢:.α∩β=Λ.⊃:α⊂β∪γ.≡.α⊂γ
PM-VERBATIM-END PM1:✱24·49 -/
/- PM-VERBATIM-BEGIN PM1:✱24·491
✱24·491. ⊢:β∩γ=Λ. α⊂β∪γ. ⊃.α - β=α∩γ.α - γ=α∩β.α=(α - β)∪(α - γ)
PM-VERBATIM-END PM1:✱24·491 -/
/- PM-VERBATIM-BEGIN PM1:✱24·492
✱24·492. ⊢:β⊂α.α - β=γ.⊃.α - γ=β
PM-VERBATIM-END PM1:✱24·492 -/
/- PM-VERBATIM-BEGIN PM1:✱24·493
✱24·493. ⊢:β∩γ=Λ.⊃.α=(α - β)∪(α - γ)
PM-VERBATIM-END PM1:✱24·493 -/
/- PM-VERBATIM-BEGIN PM1:✱24·494
✱24·494. ⊢:ξ⊂α.η⊂β.α∩β=Λ.⊃.(ξ∪η)- α=η.(ξ∪η)- β=ξ
PM-VERBATIM-END PM1:✱24·494 -/
/- PM-VERBATIM-BEGIN PM1:✱24·495
✱24·495. ⊢:α∩γ=Λ.⊃.(α∪γ)-(β∪γ)=α - β
PM-VERBATIM-END PM1:✱24·495 -/
/- PM-VERBATIM-BEGIN PM1:✱24·5
✱24·5. ⊢:∃!α.≡.(∃ x).x ∈ α [✱4·2.(✱24·03)]
PM-VERBATIM-END PM1:✱24·5 -/
/- PM-VERBATIM-BEGIN PM1:✱24·52
✱24·52. ⊢.∃!V [✱24·51·1.Transp]
PM-VERBATIM-END PM1:✱24·52 -/
/- PM-VERBATIM-BEGIN PM1:✱24·53
✱24·53. ⊢.∼∃!Λ [✱24·51.✱20·2]
PM-VERBATIM-END PM1:✱24·53 -/
/- PM-VERBATIM-BEGIN PM1:✱24·54
✱24·54. ⊢:∃!α.≡.α≠Λ [✱24·51.Transp]
PM-VERBATIM-END PM1:✱24·54 -/
/- PM-VERBATIM-BEGIN PM1:✱24·57
✱24·57. ⊢:. α∩β=Λ.⊃:∃!α.⊃.α≠ β
PM-VERBATIM-END PM1:✱24·57 -/
/- PM-VERBATIM-BEGIN PM1:✱24·571
✱24·571. ⊢:∃!α.α=β.⊃.∃!(α∩β)
PM-VERBATIM-END PM1:✱24·571 -/
/- PM-VERBATIM-BEGIN PM1:✱24·58
✱24·58. ⊢:.α⊃β.⊃:∃!α.⊃.∃!β [✱10·28]
PM-VERBATIM-END PM1:✱24·58 -/
/- PM-VERBATIM-BEGIN PM1:✱24·6
✱24·6. ⊢:.α⊃β.⊃:α≠β.≡.∃!β - α
PM-VERBATIM-END PM1:✱24·6 -/
/- PM-VERBATIM-BEGIN PM1:✱24·61
✱24·61. ⊢:∼∃!β.⊃.α∪β=α [✱24·51·24]
PM-VERBATIM-END PM1:✱24·61 -/
/- PM-VERBATIM-BEGIN PM1:✱24·62
✱24·62. ⊢:∼∃!β.⊃.α∩β=Λ [✱24·51·23]
PM-VERBATIM-END PM1:✱24·62 -/
/- PM-VERBATIM-BEGIN PM1:✱24·63
✱24·63. ⊢:.Λ∼∈κ.≡:α∈κ.⊃_α.∃!α
PM-VERBATIM-END PM1:✱24·63 -/
