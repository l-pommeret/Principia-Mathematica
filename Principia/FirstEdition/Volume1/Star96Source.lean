/-!
PM I, ✱96·01–·102. Canonical witness: Project Gutenberg ebook 78050 and
the 1910 Volume I facsimile, printed page 640 (scan leaf 662).
-/

/- PM-VERBATIM-BEGIN PM1:✱96·01
✱96·01. I_Rʻx=R⃖_∗ʻx∩ ẑ(zRₚₒz) Dft [✱96]
✱96·01. I_Rʻx = R_*⃖ʻx ∩ ẑz(z R_po z) Dft [✱96]
PM-VERBATIM-END PM1:✱96·01 -/
/- PM-VERBATIM-BEGIN PM1:✱96·02
✱96·02. J_Rʻx=R⃖_∗ʻx-I_Rʻx Dft [✱96]
✱96·02. J_Rʻx = R_*⃖ʻx − I_Rʻx Dft [✱96]
PM-VERBATIM-END PM1:✱96·02 -/
/- PM-VERBATIM-BEGIN PM1:✱96·1
✱96·1. ⊢:z∈ I_Rʻx.≡.xR_∗z.zRₚₒz [✱20·3.✱32·181.(✱96·01)]
✱96·1. ⊢ : z ∈ I_Rʻx .≡. x R_* z . z R_po z
PM-VERBATIM-END PM1:✱96·1 -/
/- PM-VERBATIM-BEGIN PM1:✱96·101
✱96·101. ⊢:z∈ J_Rʻx.≡.xR_∗z.∼(zRₚₒz) [✱96·1.✱22·93.(✱96·02)]
✱96·101. ⊢ : z ∈ J_Rʻx .≡. x R_* z . ∼(z R_po z)
PM-VERBATIM-END PM1:✱96·101 -/
/- PM-VERBATIM-BEGIN PM1:✱96·102
✱96·102. ⊢.R⃖_∗ʻx=J_Rʻx∪ I_Rʻx.J_Rʻx∩ I_Rʻx=Λ [✱24·41·21.(✱96·01·02)]
✱96·102. ⊢ . R_*⃖ʻx = J_Rʻx ∪ I_Rʻx . J_Rʻx ∩ I_Rʻx = Λ
PM-VERBATIM-END PM1:✱96·102 -/

namespace PM.FirstEdition.Volume1.Star96Source
/- PM-VERBATIM-BEGIN PM1:✱96·103
✱96·103. ⊢.(J_Rʻx)↿ Rₚₒ⪽J
Dem.
⊢.✱96·101.⊃⊢:. y{(J_Rʻx)↿ Rₚₒ}z. ≡:xR_∗y.∼(yRₚₒy).yRₚₒz:
[✱13·14] ⊃:y ≠ z:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱96·103 -/
/- PM-VERBATIM-BEGIN PM1:✱96·104
✱96·104. ⊢:I_Rʻx=Λ.≡.(R⃖_∗ʻx)↿ Rₚₒ⪽J.≡.J_Rʻx=R⃖_∗ʻx
Dem.
⊢.✱96·1.⊃⊢:. I_Rʻx=Λ. ≡:xR_∗y.⊃y.∼(yRₚₒy):
[✱13·196] ≡:xR_∗y.yRₚₒz.⊃y,z.y ≠ z:
[✱35·1] ≡:(R⃖_∗ʻx)↿ Rₚₒ⪽J (1)
⊢.(1).✱96·102.⊃⊢.Prop
PM-VERBATIM-END PM1:✱96·104 -/
/- PM-VERBATIM-BEGIN PM1:✱96·11
✱96·11. ⊢.(α↿ R)ₚₒ⪽α↿ Rₚₒ
Dem.
⊢.✱91·502.✱35·46. ⊃⊢.α↿ R⪽α↿ Rₚₒ (1)
⊢.✱35·1.⊃
⊢:. P⪽α↿ Rₚₒ. ⊃:xPy.y(α↿ R)z.⊃.x∈ α.xRₚₒy.yRz.
[✱91·511.✱35·1] ⊃.x(α↿ Rₚₒ)z.
[✱34·1] ⊃:P| (α↿ R)⪽α↿ Rₚₒ (2)
⊢.(1).(2).✱91·171. ⊃⊢:P∈ Potʻ(α↿ R).⊃.P⪽α↿ Rₚₒ:
[✱41·151] ⊃⊢.(α↿ R)ₚₒ⪽α↿ Rₚₒ.⊃⊢.Prop
PM-VERBATIM-END PM1:✱96·11 -/
/- PM-VERBATIM-BEGIN PM1:✱96·121
✱96·121. ⊢:Rʻʻα⊂ α.⊃.(R↾ α)ₚₒ=Rₚₒ↾ α [Proof as in ✱96·111]
✱96·121. ⊢ : Rʻʻα ⊂ α .⊃. (R↾α)_po = R_po↾α
PM-VERBATIM-END PM1:✱96·121 -/
/- PM-VERBATIM-BEGIN PM1:✱96·14
✱96·14. ⊢:x∈ CʻR.⊃.R⃖_∗ʻx=ιʻx∪ R⃖ₚₒʻx [✱91·54.✱32·33]
✱96·14. ⊢ : x ∈ CʻR .⊃. R_*⃖ʻx = ιʻx ∪ R_po⃖ʻx
PM-VERBATIM-END PM1:✱96·14 -/
/- PM-VERBATIM-BEGIN PM1:✱96·111
✱96·111. ⊢:Řʻʻα⊂ α.⊃.(α↿ R)ₚₒ=α↿ Rₚₒ
Dem.
⊢.✱91·502. ⊃⊢.α↿ R⪽(α↿ R)ₚₒ (1)
⊢.✱90·22.✱91·54. ⊃⊢:. Hp.⊃:P∈ PotʻR.x∈ α.xPy.⊃.y∈ α:
[✱35·1.Fact] ⊃:P∈ PotʻR.x(α↿ P)y.yRz.⊃.y(α↿ R)z:
[✱91·511] ⊃:P∈ PotʻR.α↿ P⪽(α↿ R)ₚₒ.⊃.(α↿ P)| R⪽(α↿ R)ₚₒ (2)
⊢.(1).(2).✱91·373.⊃⊢:. Hp. ⊃:P∈ PotʻR.⊃.α↿ P⪽(α↿ R)ₚₒ:
[✱41·52] ⊃:α↿ Rₚₒ⪽(α↿ R)ₚₒ:
[✱96·11] ⊃:α↿ Rₚₒ=(α↿ R)ₚₒ:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱96·111 -/
/- PM-VERBATIM-BEGIN PM1:✱96·112
✱96·112. ⊢:α⊂ DʻR.Řʻʻα⊂ α.⊃.(α↿ R)_∗=α↿ R_∗
✱96·112. ⊢ : α ⊂ DʻR . Řʻʻα ⊂ α .⊃. (α↼hR)_* = α↼hR_*
PM-VERBATIM-END PM1:✱96·112 -/
/- PM-VERBATIM-BEGIN PM1:✱96·122
✱96·122. ⊢:α⊂ ᗡʻR.Rʻʻα⊂ α.⊃.(R↾ α)_∗=R_∗↾ α [Proof as in ✱96·112]
✱96·122. ⊢ : α ⊂ ᗡʻR . Rʻʻα ⊂ α .⊃. (R↾α)_* = R_*↾α
PM-VERBATIM-END PM1:✱96·122 -/
/- PM-VERBATIM-BEGIN PM1:✱96·13
✱96·13. ⊢.(R⃖_∗ʻx)↿ Rₚₒ={(R⃖_∗ʻx)↿ R}ₚₒ [✱96·111.✱90·163]
✱96·13. ⊢ . (R_*⃖ʻx)↼hR_po = {(R_*⃖ʻx)↼hR}_po
PM-VERBATIM-END PM1:✱96·13 -/
/- PM-VERBATIM-BEGIN PM1:✱96·131
✱96·131. ⊢.x∈ DʻR.⊃.(R⃖_∗ʻx)↿ R_∗={(R⃖_∗ʻx)↿ R}_∗ [✱96·112.✱90·163]
✱96·131. ⊢ . x ∈ DʻR .⊃. (R_*⃖ʻx)↼hR_* = {(R_*⃖ʻx)↼hR}_*
PM-VERBATIM-END PM1:✱96·131 -/
/- PM-VERBATIM-BEGIN PM1:✱96·141
✱96·141. ⊢.Cʻ(α↿ R_∗)=Ř_∗ʻʻα
✱96·141. ⊢ . Cʻ(α↼hR_*) = Ř_*ʻʻα
PM-VERBATIM-END PM1:✱96·141 -/
/- PM-VERBATIM-BEGIN PM1:✱96·142
✱96·142. ⊢.Cʻ(α↿ Rₚₒ)=(α∩ DʻR)∪ Řₚₒʻʻα [✱35·61.✱37·4.✱91·504]
✱96·142. ⊢ . Cʻ(α↼hR_po) = (α ∩ DʻR) ∪ Ř_poʻʻα
PM-VERBATIM-END PM1:✱96·142 -/
/- PM-VERBATIM-BEGIN PM1:✱96·143
✱96·143. ⊢.Cʻ(α↿ Rₚₒ)=Ř_∗ʻʻ(α∩ DʻR)
✱96·143. ⊢ . Cʻ(α↼hR_po) = Ř_*ʻʻ(α ∩ DʻR)
PM-VERBATIM-END PM1:✱96·143 -/
/- PM-VERBATIM-BEGIN PM1:✱96·144
✱96·144. ⊢:α∩ ᗡʻR⊂ Ř_∗ʻʻ(α∩ DʻR).⊃.Cʻ(α↿ Rₚₒ)=Ř_∗ʻʻα
✱96·144. ⊢ : α ∩ ᗡʻR ⊂ Ř_*ʻʻ(α ∩ DʻR) .⊃. Cʻ(α↼hR_po) = Ř_*ʻʻα
PM-VERBATIM-END PM1:✱96·144 -/
/- PM-VERBATIM-BEGIN PM1:✱96·15
✱96·15. ⊢:Dʻ{(R⃖_∗ʻx)↿ R}=R⃖_∗ʻx∩ DʻR.ᗡʻ(R⃖_∗ʻx)↿ R=R⃖ₚₒʻx
✱96·15. ⊢ : Dʻ{(R_*⃖ʻx)↼hR} = R_*⃖ʻx ∩ DʻR . ᗡʻ{(R_*⃖ʻx)↼hR} = R_po⃖ʻx
PM-VERBATIM-END PM1:✱96·15 -/
/- PM-VERBATIM-BEGIN PM1:✱96·151
✱96·151. ⊢:x∈ DʻR.⊃.Cʻ{(R⃖_∗ʻx)↿ R}=R⃖_∗ʻx
✱96·151. ⊢ : x ∈ DʻR .⊃. Cʻ{(R_*⃖ʻx)↼hR} = R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·151 -/
/- PM-VERBATIM-BEGIN PM1:✱96·152
✱96·152. ⊢.Ř_∗ʻʻR⃖_∗ʻx=R⃖_∗ʻx [✱90·17]
✱96·152. ⊢ . Ř_*ʻʻR_*⃖ʻx = R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·152 -/
/- PM-VERBATIM-BEGIN PM1:✱96·153
✱96·153. ⊢.Ř_∗ʻʻR⃖ₚₒʻx=ŘₚₒʻʻR⃖_∗ʻx=R⃖ₚₒʻx [✱91·574]
✱96·153. ⊢ . Ř_*ʻʻR_po⃖ʻx = Ř_poʻʻR_*⃖ʻx = R_po⃖ʻx
PM-VERBATIM-END PM1:✱96·153 -/
/- PM-VERBATIM-BEGIN PM1:✱96·154
✱96·154. ⊢.Cʻ{(R⃖_∗ʻx)↿ R_∗}=R⃖_∗ʻx [✱96·141·152]
✱96·154. ⊢ . Cʻ{(R_*⃖ʻx)↼hR_*} = R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·154 -/
/- PM-VERBATIM-BEGIN PM1:✱96·155
✱96·155. ⊢.Dʻ{(R⃖_∗ʻx)↿ Rₚₒ}=R⃖_∗ʻx∩ DʻR.ᗡʻ{(R⃖_∗ʻx)↿ Rₚₒ}=R⃖ₚₒʻx
✱96·155. ⊢ . Dʻ{(R_*⃖ʻx)↼hR_po} = R_*⃖ʻx ∩ DʻR . ᗡʻ{(R_*⃖ʻx)↼hR_po} = R_po⃖ʻx
PM-VERBATIM-END PM1:✱96·155 -/
/- PM-VERBATIM-BEGIN PM1:✱96·156
✱96·156. ⊢.Cʻ{(R⃖_∗ʻx)↿ Rₚₒ}=(ιʻx∩ DʻR)∪ R⃖ₚₒʻx
✱96·156. ⊢ . Cʻ{(R_*⃖ʻx)↼hR_po} = (ιʻx ∩ DʻR) ∪ R_po⃖ʻx
PM-VERBATIM-END PM1:✱96·156 -/
/- PM-VERBATIM-BEGIN PM1:✱96·157
✱96·157. ⊢:x∈ DʻR.⊃.Cʻ{(R⃖_∗ʻx)↿ Rₚₒ}=R⃖_∗ʻx [✱96·156·14]
✱96·157. ⊢ : x ∈ DʻR .⊃. Cʻ{(R_*⃖ʻx)↼hR_po} = R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·157 -/
/- PM-VERBATIM-BEGIN PM1:✱96·158
✱96·158. ⊢:x∼∈ DʻR.⊃.(R⃖_∗ʻx)↿ Rₚₒ=Λ̇
✱96·158. ⊢ : x ∼∈ DʻR .⊃. (R_*⃖ʻx)↼hR_po = Λ̇
PM-VERBATIM-END PM1:✱96·158 -/
/- PM-VERBATIM-BEGIN PM1:✱96·159
✱96·159. ⊢:∃̇!(R⃖_∗ʻx)↿ Rₚₒ.⊃.Cʻ{(R⃖_∗ʻx)↿ Rₚₒ}=R⃖_∗ʻx [✱96·157·158]
✱96·159. ⊢ : ∃̇!(R_*⃖ʻx)↼hR_po .⊃. Cʻ{(R_*⃖ʻx)↼hR_po} = R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·159 -/
/- PM-VERBATIM-BEGIN PM1:✱96·16
✱96·16. ⊢.(R⃖_∗ʻx)↿ R=R ⥏ R⃖_∗ʻx
✱96·16. ⊢ . (R_*⃖ʻx)↼hR = R ⧏ R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·16 -/
/- PM-VERBATIM-BEGIN PM1:✱96·2
✱96·2. ⊢:R∈ 1→Cls.⊃.(R⃖_∗ʻx)↿ R=R↾ R⃖ₚₒʻx
✱96·2. ⊢ : R ∈ 1→Cls .⊃. (R_*⃖ʻx)↼hR = R↾R_po⃖ʻx
PM-VERBATIM-END PM1:✱96·2 -/
/- PM-VERBATIM-BEGIN PM1:✱96·21
✱96·21. ⊢:R∈ 1→Cls.xBR.⊃.(R⃖_∗ʻx)↿ R=R↾ R⃖_∗ʻx
✱96·21. ⊢ : R ∈ 1→Cls . xBR .⊃. (R_*⃖ʻx)↼hR = R↾R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·21 -/
/- PM-VERBATIM-BEGIN PM1:✱96·22
✱96·22. ⊢:R∈ 1→Cls.∼(xRx).⊃.(R⃖_∗ʻx)↿ R⪽J
✱96·22. ⊢ : R ∈ 1→Cls . ∼(xRx) .⊃. (R_*⃖ʻx)↼hR ⊂ J
PM-VERBATIM-END PM1:✱96·22 -/
/- PM-VERBATIM-BEGIN PM1:✱96·23
✱96·23. ⊢:R∈ 1→Cls.xBR.⊃.I_Rʻx=Λ.(R⃖_∗ʻx)↿ Rₚₒ⪽J
✱96·23. ⊢ : R ∈ 1→Cls . xBR .⊃. I_Rʻx = Λ . (R_*⃖ʻx)↼hR_po ⊂ J
PM-VERBATIM-END PM1:✱96·23 -/
/- PM-VERBATIM-BEGIN PM1:✱96·24
✱96·24. ⊢:R∈ 1→Cls.CʻR=Ř_∗ʻʻB⃗ʻR.⊃.Rₚₒ⪽J
✱96·24. ⊢ : R ∈ 1→Cls . CʻR = Ř_*ʻʻB⃗ʻR .⊃. R_po ⊂ J
PM-VERBATIM-END PM1:✱96·24 -/
/- PM-VERBATIM-BEGIN PM1:✱96·25
✱96·25. ⊢:. R∈ 1→Cls.xBR.xR_∗y:yR_∗z.∨.zR_∗y:⊃.xR_∗z
✱96·25. ⊢ :: R ∈ 1→Cls . xBR . xR_*y : yR_*z .∨. zR_*y :⊃. xR_*z
PM-VERBATIM-END PM1:✱96·25 -/
/- PM-VERBATIM-BEGIN PM1:✱96·3
✱96·3. ⊢:xR_∗y.⊃.R⃖_∗ʻy⊂ R⃖_∗ʻx [✱90·17]
✱96·3. ⊢ : xR_*y .⊃. R_*⃖ʻy ⊂ R_*⃖ʻx
PM-VERBATIM-END PM1:✱96·3 -/
/- PM-VERBATIM-BEGIN PM1:✱96·301
✱96·301. ⊢:xR_∗y.⊃.R⃗_∗ʻx⊂ R⃗_∗ʻy [✱90·17]
✱96·301. ⊢ : xR_*y .⊃. R_*⃗ʻx ⊂ R_*⃗ʻy
PM-VERBATIM-END PM1:✱96·301 -/
/- PM-VERBATIM-BEGIN PM1:✱96·302
✱96·302. ⊢:. R∈ Cls→1.xR_∗y.xR_∗z.⊃:yR_∗z.∨.zR_∗y [✱92·311]
✱96·302. ⊢ :: R ∈ Cls→1 . xR_*y . xR_*z .⊃. yR_*z .∨. zR_*y
PM-VERBATIM-END PM1:✱96·302 -/
/- PM-VERBATIM-BEGIN PM1:✱96·303
✱96·303. ⊢:. R∈ Cls→1.xR_∗y.xR_∗z.y ≠ z.⊃:yRₚₒz.∨.zRₚₒy [✱96·302.✱91·542]
✱96·303. ⊢ :: R ∈ Cls→1 . xR_*y . xR_*z . y ≠ z .⊃. yR_po z .∨. zR_po y
PM-VERBATIM-END PM1:✱96·303 -/
def records : List (String × String) := [
  ("✱96·01", "I_Rʻx = R_*⃖ʻx ∩ ẑz(z R_po z)  Dft [✱96]"),
  ("✱96·02", "J_Rʻx = R_*⃖ʻx − I_Rʻx  Dft [✱96]"),
  ("✱96·1", "⊢ : z ∈ I_Rʻx .≡. x R_* z . z R_po z"),
  ("✱96·101", "⊢ : z ∈ J_Rʻx .≡. x R_* z . ∼(z R_po z)"),
  ("✱96·102", "⊢ . R_*⃖ʻx = J_Rʻx ∪ I_Rʻx . J_Rʻx ∩ I_Rʻx = Λ"),
  ("✱96·103", "⊢ . (J_Rʻx)↼hR_po ⊂ J"),
  ("✱96·104", "⊢ : I_Rʻx = Λ .≡. (R_*⃖ʻx)↼hR_po ⊂ J .≡. J_Rʻx = R_*⃖ʻx")]
  ++ [
  ("✱96·11", "⊢ . (α↼hR)_po ⊂ α↼hR_po"),
  ("✱96·121", "⊢ : Rʻʻα ⊂ α .⊃. (R↾α)_po = R_po↾α"),
  ("✱96·14", "⊢ : x ∈ CʻR .⊃. R_*⃖ʻx = ιʻx ∪ R_po⃖ʻx"),
  ("✱96·111", "⊢ : Řʻʻα ⊂ α .⊃. (α↼hR)_po = α↼hR_po"),
  ("✱96·112", "⊢ : α ⊂ DʻR . Řʻʻα ⊂ α .⊃. (α↼hR)_* = α↼hR_*"),
  ("✱96·122", "⊢ : α ⊂ ᗡʻR . Rʻʻα ⊂ α .⊃. (R↾α)_* = R_*↾α"),
  ("✱96·13", "⊢ . (R_*⃖ʻx)↼hR_po = {(R_*⃖ʻx)↼hR}_po"),
  ("✱96·131", "⊢ . x ∈ DʻR .⊃. (R_*⃖ʻx)↼hR_* = {(R_*⃖ʻx)↼hR}_*"),
  ("✱96·141", "⊢ . Cʻ(α↼hR_*) = Ř_*ʻʻα"),
  ("✱96·142", "⊢ . Cʻ(α↼hR_po) = (α ∩ DʻR) ∪ Ř_poʻʻα"),
  ("✱96·143", "⊢ . Cʻ(α↼hR_po) = Ř_*ʻʻ(α ∩ DʻR)"),
  ("✱96·144", "⊢ : α ∩ ᗡʻR ⊂ Ř_*ʻʻ(α ∩ DʻR) .⊃. Cʻ(α↼hR_po) = Ř_*ʻʻα"),
  ("✱96·15", "⊢ : Dʻ{(R_*⃖ʻx)↼hR} = R_*⃖ʻx ∩ DʻR . ᗡʻ{(R_*⃖ʻx)↼hR} = R_po⃖ʻx"),
  ("✱96·151", "⊢ : x ∈ DʻR .⊃. Cʻ{(R_*⃖ʻx)↼hR} = R_*⃖ʻx"),
  ("✱96·152", "⊢ . Ř_*ʻʻR_*⃖ʻx = R_*⃖ʻx"),
  ("✱96·153", "⊢ . Ř_*ʻʻR_po⃖ʻx = Ř_poʻʻR_*⃖ʻx = R_po⃖ʻx"),
  ("✱96·154", "⊢ . Cʻ{(R_*⃖ʻx)↼hR_*} = R_*⃖ʻx"),
  ("✱96·155", "⊢ . Dʻ{(R_*⃖ʻx)↼hR_po} = R_*⃖ʻx ∩ DʻR . ᗡʻ{(R_*⃖ʻx)↼hR_po} = R_po⃖ʻx"),
  ("✱96·156", "⊢ . Cʻ{(R_*⃖ʻx)↼hR_po} = (ιʻx ∩ DʻR) ∪ R_po⃖ʻx"),
  ("✱96·157", "⊢ : x ∈ DʻR .⊃. Cʻ{(R_*⃖ʻx)↼hR_po} = R_*⃖ʻx"),
  ("✱96·158", "⊢ : x ∼∈ DʻR .⊃. (R_*⃖ʻx)↼hR_po = Λ̇"),
  ("✱96·159", "⊢ : ∃̇!(R_*⃖ʻx)↼hR_po .⊃. Cʻ{(R_*⃖ʻx)↼hR_po} = R_*⃖ʻx"),
  ("✱96·16", "⊢ . (R_*⃖ʻx)↼hR = R ⧏ R_*⃖ʻx"),
  ("✱96·2", "⊢ : R ∈ 1→Cls .⊃. (R_*⃖ʻx)↼hR = R↾R_po⃖ʻx"),
  ("✱96·21", "⊢ : R ∈ 1→Cls . xBR .⊃. (R_*⃖ʻx)↼hR = R↾R_*⃖ʻx"),
  ("✱96·22", "⊢ : R ∈ 1→Cls . ∼(xRx) .⊃. (R_*⃖ʻx)↼hR ⊂ J"),
  ("✱96·23", "⊢ : R ∈ 1→Cls . xBR .⊃. I_Rʻx = Λ . (R_*⃖ʻx)↼hR_po ⊂ J"),
  ("✱96·24", "⊢ : R ∈ 1→Cls . CʻR = Ř_*ʻʻB⃗ʻR .⊃. R_po ⊂ J"),
  ("✱96·25", "⊢ :: R ∈ 1→Cls . xBR . xR_*y : yR_*z .∨. zR_*y :⊃. xR_*z"),
  ("✱96·3", "⊢ : xR_*y .⊃. R_*⃖ʻy ⊂ R_*⃖ʻx"),
  ("✱96·301", "⊢ : xR_*y .⊃. R_*⃗ʻx ⊂ R_*⃗ʻy"),
  ("✱96·302", "⊢ :: R ∈ Cls→1 . xR_*y . xR_*z .⊃. yR_*z .∨. zR_*y"),
  ("✱96·303", "⊢ :: R ∈ Cls→1 . xR_*y . xR_*z . y ≠ z .⊃. yR_po z .∨. zR_po y")]
end PM.FirstEdition.Volume1.Star96Source

/- PM-VERBATIM-BEGIN PM1:✱96·311
✱96·311. ⊢:R∈ 1→Cls.xR_∗y.⊃.R⃗_∗ʻy⊂ R⃗_∗ʻx∪ R⃖_∗ʻx [✱92·31]
PM-VERBATIM-END PM1:✱96·311 -/
/- PM-VERBATIM-BEGIN PM1:✱96·32
✱96·32. ⊢:R∈ 1→1.xR_∗y.⊃.R⃗_∗ʻx∪ R⃖_∗ʻx=R⃗_∗ʻy∪ R⃖_∗ʻy
PM-VERBATIM-END PM1:✱96·32 -/
/- PM-VERBATIM-BEGIN PM1:✱96·33
✱96·33. ⊢:R∈ Cls→1.xRx.⊃.R⃖_∗ʻx=ιʻx
PM-VERBATIM-END PM1:✱96·33 -/
/- PM-VERBATIM-BEGIN PM1:✱96·331
✱96·331. ⊢:R∈ Cls→1.xRy.yRx.⊃.R⃖_∗ʻx=ιʻx∪ ιʻy
PM-VERBATIM-END PM1:✱96·331 -/
/- PM-VERBATIM-BEGIN PM1:✱96·34
✱96·34. ⊢:R∈ Cls→1.⊃.Řₚₒʻʻẑ(zRₚₒz)⊂ ẑ(zRₚₒz)
PM-VERBATIM-END PM1:✱96·34 -/
/- PM-VERBATIM-BEGIN PM1:✱96·341
✱96·341. ⊢:R∈ Cls→1.⊃.ŘₚₒʻʻI_Rʻx⊂ I_Rʻx
PM-VERBATIM-END PM1:✱96·341 -/
/- PM-VERBATIM-BEGIN PM1:✱96·342
✱96·342. ⊢:R∈ Cls→1.⊃.Ř_∗ʻʻI_Rʻx⊂ I_Rʻx [✱96·341.✱91·71]
PM-VERBATIM-END PM1:✱96·342 -/
/- PM-VERBATIM-BEGIN PM1:✱96·35
✱96·35. ⊢:. R∈ Cls→1.⊃:∼(wRₚₒw).zRₚₒw.⊃.∼(zRₚₒz) [✱96·34.Transp]
PM-VERBATIM-END PM1:✱96·35 -/
/- PM-VERBATIM-BEGIN PM1:✱96·351
✱96·351. ⊢:R∈ Cls→1.⊃.RₚₒʻʻJ_Rʻx∩ R⃖_∗ʻx⊂ J_Rʻx
PM-VERBATIM-END PM1:✱96·351 -/
/- PM-VERBATIM-BEGIN PM1:✱96·352
✱96·352. ⊢:R∈ Cls→1.⊃.R_∗ʻʻJ_Rʻx∩ R⃖_∗ʻx⊂ J_Rʻx [✱91·543.✱96·351]
PM-VERBATIM-END PM1:✱96·352 -/
/- PM-VERBATIM-BEGIN PM1:✱96·4
✱96·4. ⊢:R∈ Cls→1.S, T∈ PotʻR.ySy.yTz.⊃.zSz
PM-VERBATIM-END PM1:✱96·4 -/
/- PM-VERBATIM-BEGIN PM1:✱96·401
✱96·401. ⊢:R∈ Cls→1.S, T∈ PotʻR.ySy.yTz.yRw.zRw.⊃.wSw.wTw
PM-VERBATIM-END PM1:✱96·401 -/
/- PM-VERBATIM-BEGIN PM1:✱96·402
✱96·402. ⊢:R∈ Cls→1.T∈ PotʻR.yRy.yTz.yRw.zRw.⊃.y=w.y=z
PM-VERBATIM-END PM1:✱96·402 -/
/- PM-VERBATIM-BEGIN PM1:✱96·403
✱96·403. ⊢:R∈ Cls→1.S, T∈ PotʻR.yS| Ry.yTz.yRw. zRw.⊃. wSy.wSz.y=z
PM-VERBATIM-END PM1:✱96·403 -/
/- PM-VERBATIM-BEGIN PM1:✱96·41
✱96·41. ⊢:R∈ Cls→1.S, T∈ PotʻR.ySy.yTz.yRw.zRw.⊃.y=z
PM-VERBATIM-END PM1:✱96·41 -/
/- PM-VERBATIM-BEGIN PM1:✱96·42
✱96·42. ⊢:R∈ Cls→1.yRw.zRw.yRₚₒz.⊃.zRₚₒz
PM-VERBATIM-END PM1:✱96·42 -/
/- PM-VERBATIM-BEGIN PM1:✱96·421
✱96·421. ⊢:. R∈ Cls→1.y, z∈ R⃖_∗ʻx.yRw.zRw.y ≠ z.⊃:yRₚₒy.∨.zRₚₒz
PM-VERBATIM-END PM1:✱96·421 -/
/- PM-VERBATIM-BEGIN PM1:✱96·431
✱96·431. ⊢:R∈ Cls→1.y∈ J_Rʻx.z∈ I_Rʻx.⊃.yRₚₒz
PM-VERBATIM-END PM1:✱96·431 -/
/- PM-VERBATIM-BEGIN PM1:✱96·432
✱96·432. ⊢:R∈ Cls→1.y,z∈ I_Rʻx.yRw.zRw.⊃.y=z
PM-VERBATIM-END PM1:✱96·432 -/
/- PM-VERBATIM-BEGIN PM1:✱96·44
✱96·44. ⊢:. R∈ Cls→1.y,z∈ R⃖_∗ʻx.yRw.zRw.y ≠ z.⊃:y∈ I_Rʻx.∨.z∈ I_Rʻx [✱96·421·1]
PM-VERBATIM-END PM1:✱96·44 -/
/- PM-VERBATIM-BEGIN PM1:✱96·441
✱96·441. ⊢:. R∈ Cls→1.y,z∈ R⃖_∗ʻx.yRw.zRw.y ≠ z.⊃: w∈ I_Rʻx:y∈ J_Rʻx.z∈ I_Rʻx.∨.y∈ I_Rʻx.z∈ J_Rʻx
PM-VERBATIM-END PM1:✱96·441 -/
/- PM-VERBATIM-BEGIN PM1:✱96·442
✱96·442. ⊢:R∈ Cls→1.y, z∈ J_Rʻx.yRw.zRw.⊃.y=z [✱96·44.Transp]
PM-VERBATIM-END PM1:✱96·442 -/
/- PM-VERBATIM-BEGIN PM1:✱96·45
✱96·45. ⊢:R∈ Cls→1.⊃.(J_Rʻx)↿ R,(I_Rʻx)↿ R∈ 1→1 [✱96·442·432]
PM-VERBATIM-END PM1:✱96·45 -/
/- PM-VERBATIM-BEGIN PM1:✱96·451
✱96·451. ⊢:. R∈ Cls→1:J_Rʻx=Λ.∨.I_Rʻx=Λ:⊃.(R⃖_∗ʻx)↿ R∈ 1→1 [✱96·45·102]
PM-VERBATIM-END PM1:✱96·451 -/
/- PM-VERBATIM-BEGIN PM1:✱96·452
✱96·452. ⊢:. R∈ Cls→1.⊃:∃ !J_Rʻx.≡.x∈ J_Rʻx
PM-VERBATIM-END PM1:✱96·452 -/
/- PM-VERBATIM-BEGIN PM1:✱96·453
✱96·453. ⊢:. R∈ Cls→1:xRₚₒx.∨.(R⃖_∗ʻx)↿ Rₚₒ⪽J:⊃.(R⃖_∗ʻx)↿ R∈ 1→1
PM-VERBATIM-END PM1:✱96·453 -/
/- PM-VERBATIM-BEGIN PM1:✱96·46
✱96·46. ⊢:R∈ Cls→1.y,y'∈ J_Rʻx.Řʻy,Řʻy'∈ I_Rʻx.⊃.y=y'
PM-VERBATIM-END PM1:✱96·46 -/
/- PM-VERBATIM-BEGIN PM1:✱96·461
✱96·461. ⊢:R∈ Cls→1.y∈ J_Rʻx.Řʻy∈ I_Rʻx.⊃.y=max_RʻJ_Rʻx
PM-VERBATIM-END PM1:✱96·461 -/
/- PM-VERBATIM-BEGIN PM1:✱96·462
✱96·462. ⊢:R ∈ Cls→1.y∈ J_Rʻx.z∈ I_Rʻx.yRw.zRw.⊃. y=max_RʻJ_Rʻx.w=Řʻmax_RʻJ_Rʻx.z={(I_Rʻx)↿ R}ʻŘʻmax_RʻJ_Rʻx
PM-VERBATIM-END PM1:✱96·462 -/
/- PM-VERBATIM-BEGIN PM1:✱96·47
✱96·47. ⊢:. R∈ Cls→1.y,z∈ R⃖_∗ʻx.yRw.zRw.y ≠ z.⊃:w=Řʻmax_RʻJ_Rʻx: y = max_RʻJ_Rʻx.z={(I_Rʻx)↿ R}ʻŘʻmax_RʻJ_Rʻx.∨. z = max_RʻJ_Rʻx.y={(I_Rʻx)↿ R}ʻŘʻmax_RʻJ_Rʻx [✱96·441·462]
PM-VERBATIM-END PM1:✱96·47 -/
/- PM-VERBATIM-BEGIN PM1:✱96·472
✱96·472. ⊢:R∈ Cls→1.∃ !J_Rʻx.∃ !I_Rʻx.⊃.(∃ y).y∈ J_Rʻx.Řʻy∈ I_Rʻx
PM-VERBATIM-END PM1:✱96·472 -/
/- PM-VERBATIM-BEGIN PM1:✱96·473
✱96·473. ⊢:R∈ Cls→1.∃ !J_Rʻx.∃ !I_Rʻx.⊃.E!max_RʻJ_Rʻx.E!Řʻmax_RʻJ_Rʻx [✱96·461·472]
PM-VERBATIM-END PM1:✱96·473 -/
/- PM-VERBATIM-BEGIN PM1:✱96·474
✱96·474. ⊢: R∈ Cls→1.w=Řʻmax_RʻJ_Rʻx.⊃. E!{(I_Rʻx)↿ R}ʻw.E!max_RʻJ_Rʻx.{(J_Rʻx)↿ R}ʻw=max_RʻJ_Rʻx
PM-VERBATIM-END PM1:✱96·474 -/
/- PM-VERBATIM-BEGIN PM1:✱96·475
✱96·475. ⊢:. R∈ Cls→1.⊃:E!Řʻmax_RʻJ_Rʻx.≡.∃ !J_Rʻx.∃ !I_Rʻx [✱96·473·474]
PM-VERBATIM-END PM1:✱96·475 -/
/- PM-VERBATIM-BEGIN PM1:✱96·48
✱96·48. ⊢:. R ∈ Cls→1.S=(R⃖_∗ʻx)↿ R.w∈ R⃖ₚₒʻx.⊃: ∼(w=Řʻmax_RʻJ_Rʻx).≡.S⃗ʻw∈ 1:w=Řʻmax_RʻJ_Rʻx.≡.S⃗ʻw∈ 2
PM-VERBATIM-END PM1:✱96·48 -/
/- PM-VERBATIM-BEGIN PM1:✱96·49
✱96·49. ⊢:: R∈ Cls→1.x∈ Dʻ R.⊃:. (R⃖_∗ʻx)↿ R∈ 1→1.≡:I_Rʻx=Λ.∨.J_Rʻx=Λ
PM-VERBATIM-END PM1:✱96·49 -/
/- PM-VERBATIM-BEGIN PM1:✱96·491
✱96·491. ⊢:. R∈ 1→1.⊃:I_Rʻx=Λ.∨.J_Rʻx=Λ
PM-VERBATIM-END PM1:✱96·491 -/
/- PM-VERBATIM-BEGIN PM1:✱96·492
✱96·492. ⊢:. R∈ 1→1.x∈ DʻR. ⊃: ∼(xRₚₒx).≡.I_Rʻx=Λ:xRₚₒx.≡.J_Rʻx=Λ
PM-VERBATIM-END PM1:✱96·492 -/
/- PM-VERBATIM-BEGIN PM1:✱96·5
✱96·5. ⊢:R∈ 1→1.x∈ DʻR.⊃.R⃗ₚₒʻŘʻx=R⃗_∗ʻx=R⃗ₚₒʻx∪ ιʻx
PM-VERBATIM-END PM1:✱96·5 -/
/- PM-VERBATIM-BEGIN PM1:✱96·501
✱96·501. ⊢:R∈ 1→1.x∈ ᗡʻR.⊃.R⃖ₚₒʻRʻx=R⃖_∗ʻx=R⃖ₚₒʻx∪ ιʻx
PM-VERBATIM-END PM1:✱96·501 -/
/- PM-VERBATIM-BEGIN PM1:✱96·502
✱96·502. ⊢:R∈ 1→Cls.xRy.⊃.R⃗_∗ʻy=R⃗_∗ʻx∪ ιʻy
PM-VERBATIM-END PM1:✱96·502 -/
/- PM-VERBATIM-BEGIN PM1:✱96·51
✱96·51. ⊢:R∈ 1→1.α⊂ Ř_∗ʻʻB⃗ʻR.α⊂ Řₚₒʻʻα.⊃.α=Λ
PM-VERBATIM-END PM1:✱96·51 -/
/- PM-VERBATIM-BEGIN PM1:✱96·52
✱96·52. ⊢:R∈ 1→1.α⊂ Ř_∗ʻʻB⃗ʻR.∃ !α.⊃.∃ !min⃗(Rₚₒ)ʻα
PM-VERBATIM-END PM1:✱96·52 -/
