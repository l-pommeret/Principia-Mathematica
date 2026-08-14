/-!
# PM II ✱122 — progressions, opening macro-lot

Canonical Gutenberg 78255, volume II pp. 256–259. Inventory: ✱122·01, ·1,
·11, ·12, ·14, ·141, ·142, ·143, ·15, ·151, ·152, ·16, ·17, ·2,
·21, ·22, ·23, ·231.
-/
/- PM-VERBATIM-BEGIN PM2:✱122·01
✱122·01. Prog = (1→1)∩R̂(DʻR = R̅_*ʻBʻR) Df
PM-VERBATIM-END PM2:✱122·01 -/
/- PM-VERBATIM-BEGIN PM2:✱122·1
✱122·1. ⊢ : R∈Prog .≡. R∈1→1 . DʻR=R̅_*ʻBʻR
PM-VERBATIM-END PM2:✱122·1 -/
/- PM-VERBATIM-BEGIN PM2:✱122·11
✱122·11. ⊢ : R∈Prog .≡: R∈1→1 . E!BʻR : x∈DʻR .≡_x. x∈R̅_*ʻBʻR
Dem.
⊢ .*122·1.*14·205.⊃
⊢ :: R∈ Prog. ≡ :. R∈ 1→ 1:(∃ a).a = BʻR.DʻR = R⃖_*ʻa:.
[*20·43] ≡ :. R∈ 1→ 1:. (∃ a):a = BʻR:x∈ DʻR.≡ ₓ.x∈ R⃖_*ʻa:.
[*14·15] ≡ :. R∈ 1→ 1:. (∃ a):a = BʻR:x∈ DʻR.≡ ₓ.x∈ R⃖_*ʻBʻR:.
[*14·204] ≡ :. R∈ 1→ 1.E!BʻR:x∈ DʻR.≡ ₓ.x∈ R⃖_*ʻBʻR:: ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·11 -/
/- PM-VERBATIM-BEGIN PM2:✱122·12
✱122·12. ⊢ :: R∈Prog .≡: R∈1→1 . E!BʻR : x∈DʻR .≡_x: BʻR∈α . R̆ʻʻα⊂α .⊃_α. x∈α
PM-VERBATIM-END PM2:✱122·12 -/
/- PM-VERBATIM-BEGIN PM2:✱122·14
✱122·14. ⊢ : R∈Prog .⊃. R̅_poʻBʻR=ᗡʻR
Dem.
⊢ .*122·1.*37·25. ⊃ ⊢ :Hp.⊃ .ᗡʻR =Ř ʻʻR⃖_*ʻBʻR
[*91·52] =R⃖ₚₒʻBʻR:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·14 -/
/- PM-VERBATIM-BEGIN PM2:✱122·141
✱122·141. ⊢ : R∈Prog .⊃. ᗡʻR⊂DʻR . CʻR=DʻR
Dem.
⊢ .*122·1.*37·25. ⊃ ⊢ :Hp. ⊃ .ᗡʻR=Ř ʻʻR⃖_*ʻBʻR.
[*90·163] ⊃ .ᗡʻR⊂ R⃖_*ʻBʻR.
[*122·1.*33·181] ⊃ .ᗡʻR⊂ DʻR.CʻR=DʻR:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·141 -/
/- PM-VERBATIM-BEGIN PM2:✱122·142
✱122·142. ⊢ : R∈Prog . P∈PotʻR .⊃. DʻP=DʻR
PM-VERBATIM-END PM2:✱122·142 -/
/- PM-VERBATIM-BEGIN PM2:✱122·143
✱122·143. ⊢ : R∈Prog . P∈PotʻR .⊃. ᗡʻP⊂DʻP
PM-VERBATIM-END PM2:✱122·143 -/
/- PM-VERBATIM-BEGIN PM2:✱122·15
✱122·15. ⊢ : R∈Prog .⊃. R=(R⃖∗ʻBʻR)↿R=R↾(R⃖poʻBʻR)=R↾(R⃖∗ʻBʻR)
Dem.
⊢ .*122·1.*35·63. ⊃ ⊢ :Hp.⊃ .R =(R⃖_*ʻBʻR)↿ R
[*96·2] =R↾ (R⃖ₚₒʻBʻR)
[*96·21] =R↾ (R⃖_*ʻBʻR):⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·15 -/
/- PM-VERBATIM-BEGIN PM2:✱122·151
✱122·151. ⊢ : R∈Prog .⊃. R∗=(R⃖∗ʻBʻR)↿R∗=R∗↾(R⃖∗ʻBʻR)
PM-VERBATIM-END PM2:✱122·151 -/
/- PM-VERBATIM-BEGIN PM2:✱122·152
✱122·152. ⊢ : R∈Prog .⊃. Rpo=(R⃖∗ʻBʻR)↿Rpo=Rpo↾(R⃖poʻBʻR)=Rpo↾(R⃖∗ʻBʻR)
PM-VERBATIM-END PM2:✱122·152 -/
/- PM-VERBATIM-BEGIN PM2:✱122·16
✱122·16. ⊢ : R∈Prog .⊃. Rpo⪽J
PM-VERBATIM-END PM2:✱122·16 -/
/- PM-VERBATIM-BEGIN PM2:✱122·17
✱122·17. ⊢ : R∈Prog .≡. R∈Cls→1 . Rpo⪽J . DʻR=R⃖∗ʻBʻR
Dem.
⊢ .*35·63. ⊃ ⊢ :DʻR=R⃖_*ʻBʻR.⊃ .R=(R⃖_*ʻBʻR)↿ R (1)
⊢ .*96·453. ⊃ ⊢ :R∈ Cls→ 1.(R⃖_*ʻBʻR)↿ Rₚₒ ⪽ J.⊃ .(R⃖_*ʻBʻR)↿ R∈ 1→ 1 (2)
⊢ .(1).(2).*122·1. ⊃ ⊢ :DʻR=R⃖_*ʻBʻR.R∈ Cls→ 1.Rₚₒ ⪽ J.⊃ .R∈ Prog (3)
⊢ .(3).*122·1·16.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·17 -/
/- PM-VERBATIM-BEGIN PM2:✱122·2
✱122·2. ⊢ : R∈Prog . x,y∈CʻR .⊃: xR∗y ∨ yR∗x
PM-VERBATIM-END PM2:✱122·2 -/
/- PM-VERBATIM-BEGIN PM2:✱122·21
✱122·21. ⊢ : R∈Prog . x,y∈CʻR .⊃: xRpo y ∨ x=y ∨ yRpo x
PM-VERBATIM-END PM2:✱122·21 -/
/- PM-VERBATIM-BEGIN PM2:✱122·22
✱122·22. ⊢ : R∈Prog . α⊂DʻR . x,y∈α−R̆poʻʻα .⊃. x=y
Dem.
⊢ .*122·21. ⊃ ⊢ :. Hp.⊃ :xRₚₒy.∨.x=y.∨.yRₚₒx (1)
⊢ .*37·105. ⊃ ⊢ :x∈ α .xRₚₒy.⊃ .y∈ Ř ₚₒʻʻα :
[Transp] ⊃ ⊢ :x∈ α .y∼∈ Ř ₚₒʻʻα .⊃ .∼(xRₚₒy) (2)
⊢ .(2). ⊃ ⊢ :Hp.⊃ .∼(xRₚₒy).∼(yRₚₒx) (3)
⊢ .(1).(3). ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·22 -/
/- PM-VERBATIM-BEGIN PM2:✱122·23
✱122·23. ⊢ : R∈Prog . α⊂DʻR . ∃!α .⊃. E!min(Rpo)ʻα . α−R̆poʻʻα=ιʻmin(Rpo)ʻα
Dem.
⊢ .*96·52. ⊃ ⊢ :Hp.⊃ .∃ !min⃗(Rₚₒ)ʻα (1)
⊢ .*93·111.*122·22. ⊃ ⊢ :. Hp.⊃ :x,y∈ min⃗(Rₚₒ)ʻα .⊃ ₓ,y.x=y (2)
⊢ .(1).(2).*32·4.*93·111.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·23 -/
/- PM-VERBATIM-BEGIN PM2:✱122·231
✱122·231. ⊢ : R∈Prog . α⊂R̆poʻʻα .⊃. α=Λ
Dem.
⊢ .*91·504. ⊃ ⊢ :Hp.⊃ .α ⊂ ᗡʻR (1)
⊢ .*93·11. ⊃ ⊢ :Hp.⊃.∼E!min⃗(Rₚₒ)ʻα (2)
⊢ .(1).(2).*122·23·141.Transp.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱122·231 -/
namespace PM.Architecture.Star122Source
def canonicalSource : String :=
 "https://www.gutenberg.org/files/78255/78255-h/78255-h.htm#Page_256"
def propositionIds : List String :=
 ["122.01","122.1","122.11","122.12","122.14","122.141","122.142",
  "122.143","122.15","122.151","122.152","122.16","122.17","122.2",
  "122.21","122.22","122.23","122.231"]
end PM.Architecture.Star122Source
