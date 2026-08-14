/- PM-VERBATIM-BEGIN PM1:✱50·01
✱50·01. I = ẑxẑy(x = y)  Df
PM-VERBATIM-END PM1:✱50·01 -/

/- PM-VERBATIM-BEGIN PM1:✱50·02
✱50·02. J = −̇I  Df
PM-VERBATIM-END PM1:✱50·02 -/

/- PM-VERBATIM-BEGIN PM1:✱50·1
✱50·1. ⊢ : xIy .≡. x = y  [✱21·3.(✱50·01)]
PM-VERBATIM-END PM1:✱50·1 -/

/- PM-VERBATIM-BEGIN PM1:✱50·11
✱50·11. ⊢ : xJy .≡. x ≠ y  [✱23·35.✱50·1.(✱50·02)]
PM-VERBATIM-END PM1:✱50·11 -/

/- PM-VERBATIM-BEGIN PM1:✱50·12
✱50·12. ⊢ . J = ẑxẑy(x ≠ y)  [✱50·11.✱21·33]
PM-VERBATIM-END PM1:✱50·12 -/

/- PM-VERBATIM-BEGIN PM1:✱50·13
✱50·13. ⊢ . ∃̇!I  [✱13·19.✱10·24·281.✱50·1]
PM-VERBATIM-END PM1:✱50·13 -/

/- PM-VERBATIM-BEGIN PM1:✱50·14
✱50·14. ⊢ . Iʻy = y  [✱30·3.✱50·1.✱10·11]
PM-VERBATIM-END PM1:✱50·14 -/

/- PM-VERBATIM-BEGIN PM1:✱50·15
✱50·15. ⊢ . (y).∃!Iʻy  [✱50·14.✱14·21.✱10·11]
PM-VERBATIM-END PM1:✱50·15 -/

/- PM-VERBATIM-BEGIN PM1:✱50·16
✱50·16. ⊢ . Iʻʻα = α
Dem.
⊢ . ✱37·1 .⊃ ⊢ : x ∈ Iʻʻα .≡. (∃y).y ∈ α . xIy
[✱50·1] ≡. (∃y).y ∈ α . x = y
[✱13·195] ≡. x ∈ α : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·16 -/

/- PM-VERBATIM-BEGIN PM1:✱50·17
✱50·17. ⊢ : x ∈ α .⊃ₓ. Rʻx = x : ⊃ . Rʻʻα = α
Dem.
⊢ . ✱14·21 .⊃ ⊢ : Hp .⊃. E‼Rʻʻα  (1)
⊢ . ✱50·14 .⊃ ⊢ : Hp .⊃ : x ∈ α .⊃ₓ. Rʻx = Iʻx :
[✱37·69.(1)] ⊃ : Rʻʻα = Iʻʻα :
[✱50·16] ⊃ : Rʻʻα = α :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·17 -/

/- Source: Project Gutenberg 78050, PM I pp. 349–350; first ten entries of
✱50, collated in printed order. -/

/- PM-VERBATIM-BEGIN PM1:✱50·2
✱50·2. ⊢ . I = CnvʻI
Dem.
⊢ . ✱50·1 .⊃ ⊢ : xIy .≡. x = y
[✱13·16] ≡. y = x
[✱50·1] ≡. yIx
[✱31·11] ≡. x CnvʻI y : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·2 -/

/- PM-VERBATIM-BEGIN PM1:✱50·21
✱50·21. ⊢ . J = CnvʻJ
Dem.
⊢ . ✱21·2.(✱50·02) .⊃ ⊢ . J = −̇I  (1)
[✱50·2.✱23·83] = −̇CnvʻI
[✱31·16] = Cnvʻ−̇I [(1).✱31·32] = CnvʻJ .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·21 -/

/- PM-VERBATIM-BEGIN PM1:✱50·22
✱50·22. ⊢ : R ⊂̇ I .≡. CnvʻR ⊂̇ I
PM-VERBATIM-END PM1:✱50·22 -/

/- PM-VERBATIM-BEGIN PM1:✱50·23
✱50·23. ⊢ : R ⊂̇ J .≡. CnvʻR ⊂̇ J
PM-VERBATIM-END PM1:✱50·23 -/

/- PM-VERBATIM-BEGIN PM1:✱50·24
✱50·24. ⊢ : R ⊂̇ J .≡. (x)∼(xRx)
Dem.
⊢ . ✱50·11 .⊃ ⊢ : R ⊂̇ J .≡ : xRy .⊃ₓᵧ. x ≠ y :
[Transp] ≡ : x = y .⊃ₓᵧ. ∼(xRy) :
[✱13·191] ≡ : (x).∼(xRx) :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·24 -/

/- PM-VERBATIM-BEGIN PM1:✱50·3
✱50·3. ⊢ . (x).xIx
PM-VERBATIM-END PM1:✱50·3 -/

/- PM-VERBATIM-BEGIN PM1:✱50·31
✱50·31. ⊢ . DʻI = V . ᗡʻI = V
Dem.
⊢ . ✱50·3.✱10·24 .⊃ ⊢ : (x) : (∃y).xIy : (x) : (∃y).yIx :.
[✱33·13·131] ⊃ ⊢ : (x).x ∈ DʻI : (x).x ∈ ᗡʻI :
[✱24·14] ⊃ ⊢ . DʻI = V . ᗡʻI = V .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·31 -/

/- PM-VERBATIM-BEGIN PM1:✱50·32
✱50·32. ⊢ . CʻI = V
PM-VERBATIM-END PM1:✱50·32 -/

/- PM-VERBATIM-BEGIN PM1:✱50·33
✱50·33. ⊢ : ∃̇!J .⊃. DʻJ = V . ᗡʻJ = V . CʻJ = V
Dem.
⊢ . ✱13·171.Transp .⊃ ⊢ : y ≠ z .⊃ : x ≠ y .∨. x ≠ z :.
[✱50·11] ⊃ ⊢ : yJz .⊃ : xJy .∨. xJz :
[✱33·14] ⊃ : x ∈ DʻJ  (1)
⊢ . (1).✱11·11·35 .⊃ ⊢ : ∃̇!J .⊃. x ∈ DʻJ :
[✱10·11·21] ⊃ ⊢ : ∃̇!J .⊃. (x).x ∈ DʻJ
[✱24·14] ⊃. DʻJ = V  (2)
⊢ . (2).✱50·21 .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·33 -/

/- PM-VERBATIM-BEGIN PM1:✱50·34
✱50·34. ⊢ . ∃̇!(J ↾ Cls)
Dem.
⊢ . ✱20·41.✱22·38.(✱24·01·02) .⊃ ⊢ . Λ,V ∈ Cls
[✱24·1] ⊃ ⊢ . Λ ≠ V . Λ,V ∈ Cls
[✱36·13.✱50·11] ⊃ ⊢ . Λ{J ↾ Cls}V
[✱10·24] ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·34 -/

/- PM-VERBATIM-BEGIN PM1:✱50·35
✱50·35. ⊢ . ∃̇!(J ↾ Rel)
[Proof as in ✱50·34]
PM-VERBATIM-END PM1:✱50·35 -/

/- PM-VERBATIM-BEGIN PM1:✱50·4
✱50·4. ⊢ . R | I = I | R = R
Dem.
⊢ . ✱34·1 .⊃ ⊢ : x(R | I)z .≡. (∃y).xRy . yIz
[✱50·1] ≡. (∃y).xRy . y = z
[✱13·195] ≡. xRz  (1)
⊢ . ✱34·1 .⊃ ⊢ : x(I | R)z .≡. (∃y).xIy . yRz
[✱50·1] ≡. (∃y).x = y . yRz
[✱13·195] ≡. xRz  (2)
⊢ . (1).(2) .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·4 -/

/- PM-VERBATIM-BEGIN PM1:✱50·41
✱50·41. ⊢ : R | CnvʻP ⊂̇ J .≡. CnvʻR | P ⊂̇ J .≡. R ∩̇ P = Λ̇
Dem.
⊢ . ✱34·1.✱50·11 .⊃ ⊢ : R | CnvʻP ⊂̇ J .≡ : (∃y).xRy . y CnvʻP z .⊃ₓ,z. x ≠ z :
[✱13·196] ≡ : (x).∼(∃y).xRy . y CnvʻP x :
[✱10·252] ≡ : ∼(∃x,y).xRy . y CnvʻP x :
[✱31·11] ≡ : ∼(∃x,y).xRy . xPy :
[✱23·33.✱25·51] ≡ : R ∩̇ P = Λ̇ :  (1)
[✱31·14·24] ≡ : CnvʻR ∩̇ CnvʻP = Λ̇ :
[(1) CnvʻR,CnvʻP/R,P] ≡ : CnvʻR | CnvʻCnvʻP ⊂̇ J :
[✱34·203] ≡ : CnvʻR | P ⊂̇ J  (2)
⊢ . (1).(2) .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·41 -/

/- PM-VERBATIM-BEGIN PM1:✱50·42
✱50·42. ⊢ . I² = I
Dem.
⊢ . ✱34·5 .⊃ ⊢ : xI²z .≡. (∃y).xIy . yIz
[✱50·1] ≡. (∃y).xIy . y = z
[✱13·195] ≡. xIz : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·42 -/

/- PM-VERBATIM-BEGIN PM1:✱50·43
✱50·43. ⊢ : R² ⊂̇ J .≡. R ∩̇ CnvʻR = Λ̇
PM-VERBATIM-END PM1:✱50·43 -/

/- PM-VERBATIM-BEGIN PM1:✱50·44
✱50·44. ⊢ : ∃̇!(R ∩̇ I) .⊃. ∃̇!(R² ∩̇ I)
Dem.
⊢ . ✱23·33.✱50·1 .⊃ ⊢ : ∃̇!(R ∩̇ I) .≡. (∃x,y).xRy . x = y
[✱13·195] ≡. (∃x).xRx
[✱34·54] ⊃. (∃x).xR²x
[✱13·195] ⊃. (∃x,y).xR²y . x = y
[✱23·33.✱50·1] ⊃. ∃̇!(R² ∩̇ I) : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·44 -/

/- PM-VERBATIM-BEGIN PM1:✱50·45
✱50·45. ⊢ : R² ⊂̇ J .⊃. R ⊂̇ J
PM-VERBATIM-END PM1:✱50·45 -/

/- PM-VERBATIM-BEGIN PM1:✱50·46
✱50·46. ⊢ : R ∩̇ CnvʻR = Λ̇ .⊃. R ⊂̇ J
PM-VERBATIM-END PM1:✱50·46 -/

/- PM-VERBATIM-BEGIN PM1:✱50·47
✱50·47. ⊢ : R² ⊂̇ R .⊃ : R ⊂̇ J .≡. R² ⊂̇ J .≡. R ∩̇ CnvʻR = Λ̇
Dem.
⊢ . ✱23·44 .⊃ ⊢ : Hp .⊃ : R ⊂̇ J .⊃. R² ⊂̇ J  (1)
⊢ . (1).✱50·45·43 .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·47 -/

/- PM-VERBATIM-BEGIN PM1:✱50·5
✱50·5. ⊢ . α ◁ I = I ▷ α = α ◁ I ▷ α
Dem.
⊢ . ✱35·1 .⊃ ⊢ : x(α ◁ I)y .≡. x ∈ α . xIy
[✱50·1] ≡. x ∈ α . x = y
[✱13·193] ≡. y ∈ α . x = y
[✱50·1] ≡. xIy . y ∈ α
[✱35·101] ≡. x(I ▷ α)y  (1)
⊢ . (1).✱23·5 .⊃ ⊢ . α ◁ I = α ◁ I ∩̇ I ▷ α
[✱35·11] ≡ α ◁ I ▷ α  (2)
⊢ . (1).(2) .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·5 -/

/- PM-VERBATIM-BEGIN PM1:✱50·51
✱50·51. ⊢ . Cnvʻ(α ◁ I) = α ◁ I
PM-VERBATIM-END PM1:✱50·51 -/

/- PM-VERBATIM-BEGIN PM1:✱50·52
✱50·52. ⊢ . Dʻ(α ◁ I) = ᗡʻ(α ◁ I) = Cʻ(α ◁ I) = α
Dem.
⊢ . ✱35·61 .⊃ ⊢ . Dʻ(α ◁ I) = α ∩ DʻI
[✱50·31] = α ∩ V
[✱24·26] = α  (1)
Similarly ⊢ . ᗡʻ(α ◁ I) = α  (2)
⊢ . (1).(2).✱33·18 .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·52 -/

/- PM-VERBATIM-BEGIN PM1:✱50·53
✱50·53. ⊢ . α ◁ I ▷ β = (α ∩ β) ◁ I = I ▷ (α ∩ β)
Dem.
⊢ . ✱35·21.✱50·5 .⊃ ⊢ . α ◁ I ▷ β = α ◁ (β ◁ I)
[✱35·32] = (α ∩ β) ◁ I  (1)
⊢ . (1).✱50·5 .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·53 -/

/- PM-VERBATIM-BEGIN PM1:✱50·54
✱50·54. ⊢ . (α ◁ I)² = α ◁ I
Dem.
⊢ . ✱50·5 .⊃ ⊢ . (α ◁ I)² = (α ◁ I) | (I ▷ α)
[✱35·12] = α ◁ I² ▷ α
[✱50·42] = α ◁ I ▷ α
[✱50·5] = α ◁ I .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·54 -/

/- PM-VERBATIM-BEGIN PM1:✱50·55
✱50·55. ⊢ : α ∩ β = Λ .≡. α ↑ β ⊂̇ J
Dem.
⊢ . ✱24·37.✱50·11 .⊃
⊢ : α ∩ β = Λ .≡ : x ∈ α . y ∈ β .⊃ₓᵧ. xJy :
[✱35·103] ≡ : α ↑ β ⊂̇ J :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·55 -/

/- PM-VERBATIM-BEGIN PM1:✱50·56
✱50·56. ⊢ : ∃!(α ∩ β) .≡. ∃̇!{(α ↑ β) ∩̇ I}
Dem.
⊢ . ✱50·55.Transp.✱24·54 .⊃
⊢ : ∃!(α ∩ β) .≡. ∼{α ↑ β ⊂̇ J}
[✱25·55] ≡. ∃̇(α ↑ β)−̇J
[✱23·831.(✱50·02)] ≡. ∃̇!{(α ↑ β) ∩̇ I} : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·56 -/

/- PM-VERBATIM-BEGIN PM1:✱50·57
✱50·57. ⊢ . I ∩̇ α ◁ R = I ∩̇ R ▷ α = I ∩̇ α ◁ R ▷ α
Dem.
⊢ . ✱35·16 .⊃ ⊢ . I ∩̇ α ◁ R = α ◁ I ∩̇ R
[✱50·5] = I ▷ α ∩̇ R
[✱35·17] = I ∩̇ R ▷ α  (1)
[✱50·5] = α ◁ I ▷ α ∩̇ R
[✱35·16·17·21] = I ∩̇ α ◁ R ▷ α  (2)
⊢ . (1).(2) .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·57 -/

/- PM-VERBATIM-BEGIN PM1:✱50·58
✱50·58. ⊢ : α ◁ R ⊂̇ J .≡. R ▷ α ⊂̇ J .≡. α ◁ R ▷ α ⊂̇ J
Dem.
⊢ . ✱50·57 .⊃ ⊢ : I ∩̇ α ◁ R = Λ̇ .≡. I ∩̇ R ▷ α = Λ̇ .≡. I ∩̇ α ◁ R ▷ α = Λ̇  (1)
⊢ . (1).✱50·41 .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·58 -/

/- PM-VERBATIM-BEGIN PM1:✱50·59
✱50·59. ⊢ . (I ▷ α)ʻʻβ = α ∩ β
Dem.
⊢ . ✱37·412 .⊃ ⊢ . (I ▷ α)ʻʻβ = Iʻʻ(α ∩ β)
[✱50·16] = α ∩ β .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·59 -/

/- PM-VERBATIM-BEGIN PM1:✱50·6
✱50·6. ⊢ . R | (I ▷ α) = R ▷ α
Dem.
⊢ . ✱35·23 .⊃ ⊢ . R | (I ▷ α) = (R | I) ▷ α
[✱50·4] = R ▷ α .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·6 -/
/- PM-VERBATIM-BEGIN PM1:✱50·61
✱50·61. ⊢ . I ▷ α | R = α ◁ R
Dem.
⊢ . ✱35·354 .⊃ ⊢ . I ▷ α | R = I | (α ◁ R)
[✱50·4] = α ◁ R .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·61 -/
/- PM-VERBATIM-BEGIN PM1:✱50·62
✱50·62. ⊢ : ᗡʻR ⊂ α .⊃. R | (I ▷ α) = R
PM-VERBATIM-END PM1:✱50·62 -/
/- PM-VERBATIM-BEGIN PM1:✱50·63
✱50·63. ⊢ : DʻR ⊂ α .⊃. I ▷ α | R = R
PM-VERBATIM-END PM1:✱50·63 -/
/- PM-VERBATIM-BEGIN PM1:✱50·64
✱50·64. ⊢ . R | (I ▷ ᗡʻR) = R | (I ▷ CʻR) = R
PM-VERBATIM-END PM1:✱50·64 -/
/- PM-VERBATIM-BEGIN PM1:✱50·65
✱50·65. ⊢ . I ▷ (DʻR) | R = I ▷ (CʻR) | R = R
PM-VERBATIM-END PM1:✱50·65 -/
/- PM-VERBATIM-BEGIN PM1:✱50·7
✱50·7. ⊢ : ᗡʻR ⊂ α .⊃. R |ʻ(I ▷ α) = R
PM-VERBATIM-END PM1:✱50·7 -/
/- PM-VERBATIM-BEGIN PM1:✱50·71
✱50·71. ⊢ : DʻR ⊂ α .⊃. |Rʻ(I ▷ α) = R
PM-VERBATIM-END PM1:✱50·71 -/
/- PM-VERBATIM-BEGIN PM1:✱50·72
✱50·72. ⊢ . R ∥ʻ(I ▷ CʻR) = |Rʻ(I ▷ CʻR) = R
PM-VERBATIM-END PM1:✱50·72 -/
/- PM-VERBATIM-BEGIN PM1:✱50·73
✱50·73. ⊢ . R ∥ʻI = |RʻI = R
PM-VERBATIM-END PM1:✱50·73 -/
/- PM-VERBATIM-BEGIN PM1:✱50·74
✱50·74. ⊢ . R ∥ I = R |
Dem.
⊢ . ✱43·112 .⊃ ⊢ . (R | I)ʻQ = R | Q | I
[✱50·4] = R | Q
[✱43·11] = R |ʻQ  (1)
⊢ . (1).✱30·41 .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·74 -/
/- PM-VERBATIM-BEGIN PM1:✱50·75
✱50·75. ⊢ . I ∥ R = |R
[Proof as in ✱50·74]
PM-VERBATIM-END PM1:✱50·75 -/
/- PM-VERBATIM-BEGIN PM1:✱50·76
✱50·76. ⊢ : P | = R | .≡. P = R
Dem.
⊢ . ✱34·27.✱30·41 .⊃ ⊢ : P = R .⊃. P | = R |  (1)
⊢ . ✱50·73.✱30·36 .⊃ ⊢ : P | = R | .⊃. P = R  (2)
⊢ . (1).(2) .⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱50·76 -/
/- PM-VERBATIM-BEGIN PM1:✱50·761
✱50·761. ⊢ : |P = |R .≡. P = R
[Proof as in ✱50·76]
PM-VERBATIM-END PM1:✱50·761 -/
