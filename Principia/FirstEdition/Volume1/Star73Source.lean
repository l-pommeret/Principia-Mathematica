namespace PM.FirstEdition.Volume1.Star73Source

/- Diplomatic proposition records, Project Gutenberg 78050, PM I ✱73. -/
def records : List (String × String) := [
  ("✱73·01", "α sm̅ β = 1→1 ∩ D⃖ʻα ∩ ʗ⃖ʻβ  Df"),
  ("✱73·02", "sm = α̂β̂(∃!α sm̅ β)  Df"),
  ("✱73·03", "⊢ : R ∈ α sm̅ β .≡. R ∈ 1→1 . α = DʻR . β = ʗʻR"),
  ("✱73·04", "⊢ : α sm β .≡. ∃!α sm̅ β"),
  ("✱73·1", "⊢ : α sm β .≡. (∃R). R ∈ 1→1 . α = DʻR . β = ʗʻR"),
  ("✱73·11", "⊢ : α sm β .≡. (∃R). R ∈ 1→1 . α ⊂ DʻR . β = Řʻʻα"),
  ("✱73·12", "⊢ : α sm β .≡. (∃R). R ∈ 1→1 . β ⊂ ʗʻR . α = Rʻʻβ"),
  ("✱73·13", "⊢ : α sm β .≡. (∃R). R ∈ 1→Cls . R↾β ∈ Cls→1 . β ⊂ ʗʻR . α = Rʻʻβ"),
  ("✱73·131", "⊢ : α sm β .≡. (∃R). R ∈ Cls→1 . α↼hR ∈ 1→Cls . α ⊂ DʻR . β = Řʻʻα"),
  ("✱73·14", "⊢ : α sm β .≡. (∃R). R ∈ 1→Cls . β ⊂ ʗʻR . α = Rʻʻβ . R↾β ∈ 1→1"),
  ("✱73·141", "⊢ : α sm β .≡. (∃R). R ∈ Cls→1 . α ⊂ DʻR . β = Řʻʻα . α↼hR ∈ 1→1"),
  ("✱73·142", "⊢ : R↾β ∈ α sm̅ β .≡. R↾β ∈ 1→1 . β ⊂ ʗʻR . α = Rʻʻβ"),
  ("✱73·15", "⊢ : α sm β .≡. (∃R). R↾β ∈ 1→1 . β ⊂ ʗʻR . α = Rʻʻβ"),
  ("✱73·2", "⊢ : R ∈ 1→1 .⊃. DʻR sm ʗʻR . ʗʻR sm DʻR"),
  ("✱73·21", "⊢ : R ∈ 1→1 . α ⊂ DʻR .⊃. α sm Řʻʻα . α↼hR ∈ α sm̅ (Řʻʻα)")]

end PM.FirstEdition.Volume1.Star73Source

/- PM-VERBATIM-BEGIN PM1:✱73·01
✱73·01. α sm̅β=1 → 1∩ D⃖ʻα∩ ᗡ⃖ʻβ Df
PM-VERBATIM-END PM1:✱73·01 -/
/- PM-VERBATIM-BEGIN PM1:✱73·02
✱73·02. sm =α̂β̂(∃ !α sm̅β) Df
PM-VERBATIM-END PM1:✱73·02 -/
/- PM-VERBATIM-BEGIN PM1:✱73·03
✱73·03. ⊢:R∈ α sm̅β.≡.R∈ 1 → 1.α=DʻR.β=ᗡʻR [*33·6·61.(*73·01)]
PM-VERBATIM-END PM1:✱73·03 -/
/- PM-VERBATIM-BEGIN PM1:✱73·04
✱73·04. ⊢:α sm β.≡.∃ !α sm̅β [(*73·02)]
PM-VERBATIM-END PM1:✱73·04 -/
/- PM-VERBATIM-BEGIN PM1:✱73·1
✱73·1. ⊢:α sm β.≡.(∃ R).R∈ 1 → 1.α=DʻR.β=ᗡʻR [*73·03·04]
PM-VERBATIM-END PM1:✱73·1 -/
/- PM-VERBATIM-BEGIN PM1:✱73·11
✱73·11. ⊢:α sm β.≡.(∃ R).R∈ 1 → 1.α⊂ DʻR.β=Řʻʻα
PM-VERBATIM-END PM1:✱73·11 -/
/- PM-VERBATIM-BEGIN PM1:✱73·12
✱73·12. ⊢:α sm β.≡.(∃ R).R∈ 1 → 1.β⊂ ᗡʻR.α=Rʻʻβ [Proof as in *73·11]
PM-VERBATIM-END PM1:✱73·12 -/
/- PM-VERBATIM-BEGIN PM1:✱73·13
✱73·13. ⊢:α sm β.≡.(∃ R).R∈ 1 → Cls.R↾ β∈ Cls → 1.β⊂ ᗡʻR.α=Rʻʻβ
PM-VERBATIM-END PM1:✱73·13 -/
/- PM-VERBATIM-BEGIN PM1:✱73·131
✱73·131. ⊢:α sm β.≡.(∃ R).R∈ Cls → 1.α ↿ R∈ 1 → Cls.α⊂ DʻR.β=Řʻʻα [Proof as in *73·13]
PM-VERBATIM-END PM1:✱73·131 -/
/- PM-VERBATIM-BEGIN PM1:✱73·14
✱73·14. ⊢:. α sm β.≡:(∃ R):R∈ 1 → Cls.β⊂ ᗡʻR.α=Rʻʻβ: y,z∈ β.Rʻy=Rʻz.⊃y,z.y=z
PM-VERBATIM-END PM1:✱73·14 -/
/- PM-VERBATIM-BEGIN PM1:✱73·141
✱73·141. ⊢:. α sm β.≡:(∃ R):R∈ Cls → 1.α⊂ DʻR.β=Řʻʻα: y,z∈ α.Řʻy=Řʻz.⊃y,z.y=z [Proof as in *73·14]
PM-VERBATIM-END PM1:✱73·141 -/
/- PM-VERBATIM-BEGIN PM1:✱73·142
✱73·142. ⊢:R↾ β∈ α sm̅β.≡.R↾ β∈ 1 → 1.β⊂ ᗡʻR.α=Rʻʻβ
PM-VERBATIM-END PM1:✱73·142 -/
/- PM-VERBATIM-BEGIN PM1:✱73·15
✱73·15. ⊢:α sm β.≡.(∃ R).R↾ β∈ 1 → 1.β⊂ ᗡʻR.α=Rʻʻβ
PM-VERBATIM-END PM1:✱73·15 -/
/- PM-VERBATIM-BEGIN PM1:✱73·2
✱73·2. ⊢:R∈ 1 → 1.⊃.DʻR sm ᗡʻR.ᗡʻR sm DʻR
PM-VERBATIM-END PM1:✱73·2 -/
/- PM-VERBATIM-BEGIN PM1:✱73·21
✱73·21. ⊢:R∈ 1 → 1.α⊂ DʻR.⊃.α sm Řʻʻα.α↿ R∈ α sm̅(Řʻʻα) [*73·11]
PM-VERBATIM-END PM1:✱73·21 -/
/- PM-VERBATIM-BEGIN PM1:✱73·22
✱73·22. ⊢:R∈ 1 → 1.β⊂ ᗡʻR.⊃.Rʻʻβ sm β.R↾ β∈ (Rʻʻβ) sm̅β [*73·12]
PM-VERBATIM-END PM1:✱73·22 -/
/- PM-VERBATIM-BEGIN PM1:✱73·23
✱73·23. ⊢:R∈ 1 → Cls.β⊂ ᗡʻR. R↾ β∈ Cls → 1.⊃. Rʻʻβ sm β.R↾ β∈ (Rʻʻβ) sm̅β [*73·13]
PM-VERBATIM-END PM1:✱73·23 -/
/- PM-VERBATIM-BEGIN PM1:✱73·231
✱73·231. ⊢:R∈ Cls → 1.α⊂ DʻR. α↿ R∈ 1 → Cls.⊃. α sm Řʻʻα.α↿ R∈ α sm̅(Řʻʻα) [*73·131]
PM-VERBATIM-END PM1:✱73·231 -/
/- PM-VERBATIM-BEGIN PM1:✱73·24
✱73·24. ⊢:. R∈ 1 → Cls.β⊂ ᗡʻR:y, z∈ β.Rʻy=Rʻz.⊃y,z.y=z:⊃. Rʻʻβ sm β.R↾ β∈ (Rʻʻβ) sm̅β [*73·14·142]
PM-VERBATIM-END PM1:✱73·24 -/
/- PM-VERBATIM-BEGIN PM1:✱73·241
✱73·241. ⊢:. R∈ Cls → 1.α⊂ DʻR: y, z∈ α.Řʻy=Řʻz.⊃y,z.y=z:⊃. α sm Řʻʻα.α↿ R∈ α sm̅Řʻʻα [*73·141·03]
PM-VERBATIM-END PM1:✱73·241 -/
/- PM-VERBATIM-BEGIN PM1:✱73·25
✱73·25. ⊢:. (y).E!Rʻy:y,z∈ β.Rʻy=Rʻz.⊃y,z.y=z:⊃.Rʻʻβ sm β
PM-VERBATIM-END PM1:✱73·25 -/
/- PM-VERBATIM-BEGIN PM1:✱73·26
✱73·26. ⊢:. (y).E!Rʻy:R∈ 1 → 1:⊃.Rʻʻβ sm β.R↾ β∈ (Rʻʻβ) sm̅β
PM-VERBATIM-END PM1:✱73·26 -/
/- PM-VERBATIM-BEGIN PM1:✱73·27
✱73·27. ⊢:. Rʻy=Rʻz.≡y,z.y=z:⊃.Rʻʻβ sm β.R↾ β∈ (Rʻʻβ) sm̅β [*73·26.*71·57]
PM-VERBATIM-END PM1:✱73·27 -/
/- PM-VERBATIM-BEGIN PM1:✱73·28
✱73·28. ⊢:: y, z ∈ β.⊃y,z:Rʻy=Rʻz.≡.y= z:. ⊃. Rʻʻβ sm β.R↾ β∈ (Rʻʻβ) sm̅β
PM-VERBATIM-END PM1:✱73·28 -/
/- PM-VERBATIM-BEGIN PM1:✱73·3
✱73·3. ⊢.α sm α.I↾ α∈ α sm̅α
PM-VERBATIM-END PM1:✱73·3 -/
/- PM-VERBATIM-BEGIN PM1:✱73·301
✱73·301. ⊢:R∈ α sm̅β.≡.Ř∈ β sm̅α
PM-VERBATIM-END PM1:✱73·301 -/
/- PM-VERBATIM-BEGIN PM1:✱73·31
✱73·31. ⊢:α sm β.≡.β sm α [*73·301·04.*31·52]
PM-VERBATIM-END PM1:✱73·31 -/
/- PM-VERBATIM-BEGIN PM1:✱73·311
✱73·311. ⊢:R∈ α sm̅β.S∈ β sm̅γ.⊃.R| S∈ α sm̅γ
PM-VERBATIM-END PM1:✱73·311 -/
/- PM-VERBATIM-BEGIN PM1:✱73·32
✱73·32. ⊢:α sm β.β sm γ.⊃.α sm γ [*73·311·04]
PM-VERBATIM-END PM1:✱73·32 -/
/- PM-VERBATIM-BEGIN PM1:✱73·33
✱73·33. ⊢.Cnvʻ sm = sm [*73·31.*31·131]
PM-VERBATIM-END PM1:✱73·33 -/
/- PM-VERBATIM-BEGIN PM1:✱73·34
✱73·34. ⊢. sm ²= sm
PM-VERBATIM-END PM1:✱73·34 -/
/- PM-VERBATIM-BEGIN PM1:✱73·35
✱73·35. ⊢.Dʻ sm =ᗡʻ sm =Cls
PM-VERBATIM-END PM1:✱73·35 -/
/- PM-VERBATIM-BEGIN PM1:✱73·36
✱73·36. ⊢:. α sm β.⊃:∃ !α.≡.∃ !β
PM-VERBATIM-END PM1:✱73·36 -/
/- PM-VERBATIM-BEGIN PM1:✱73·37
✱73·37. ⊢:. α sm β.⊃:γ sm α.≡.γ sm β
PM-VERBATIM-END PM1:✱73·37 -/
/- PM-VERBATIM-BEGIN PM1:✱73·4
✱73·4. ⊢.Cnvʻʻλ sm λ.Cnv↾ λ∈ (Cnvʻʻλ) sm̅λ [*73·26.*72·11.*31·13]
PM-VERBATIM-END PM1:✱73·4 -/
/- PM-VERBATIM-BEGIN PM1:✱73·41
✱73·41. ⊢.ιʻʻα sm α.ι↾ α∈ (ιʻʻα) sm̅α [*73·26.*72·18.*51·12]
PM-VERBATIM-END PM1:✱73·41 -/
/- PM-VERBATIM-BEGIN PM1:✱73·42
✱73·42. ⊢:α⊂ 1.⊃.α sm ι̌ʻʻα
PM-VERBATIM-END PM1:✱73·42 -/
/- PM-VERBATIM-BEGIN PM1:✱73·43
✱73·43. ⊢.ιʻx sm ιʻy.x↓ y∈ (ιʻx) sm̅(ιʻy) [*55·15.*72·182.*73·2]
PM-VERBATIM-END PM1:✱73·43 -/
/- PM-VERBATIM-BEGIN PM1:✱73·44
✱73·44. ⊢:. α∈ 1.⊃:β sm α.≡.β∈ 1
PM-VERBATIM-END PM1:✱73·44 -/
/- PM-VERBATIM-BEGIN PM1:✱73·45
✱73·45. ⊢.1=β̂(β sm ιʻx)
PM-VERBATIM-END PM1:✱73·45 -/
/- PM-VERBATIM-BEGIN PM1:✱73·46
✱73·46. ⊢.Λ sm Λ [*72·1.*33·29.*73·2]
PM-VERBATIM-END PM1:✱73·46 -/
/- PM-VERBATIM-BEGIN PM1:✱73·47
✱73·47. ⊢:β sm Λ.≡.β=Λ
PM-VERBATIM-END PM1:✱73·47 -/
/- PM-VERBATIM-BEGIN PM1:✱73·48
✱73·48. ⊢.0=β̂(β sm Λ) [*73·46.*51·11.(*54·01)]
PM-VERBATIM-END PM1:✱73·48 -/
/- PM-VERBATIM-BEGIN PM1:✱73·5
✱73·5. ⊢:R∈ 1 → 1.≡.R_∈↾ ClʻᗡʻR⪽ sm
PM-VERBATIM-END PM1:✱73·5 -/
/- PM-VERBATIM-BEGIN PM1:✱73·501
✱73·501. ⊢:R∈ 1 → 1.≡.(Ř)_∈↾ ClʻDʻR⪽ sm
PM-VERBATIM-END PM1:✱73·501 -/
/- PM-VERBATIM-BEGIN PM1:✱73·51
✱73·51. ⊢:R∈ 1 → Cls.α⊂ DʻR.⊃.R⃖ʻʻα sm α
PM-VERBATIM-END PM1:✱73·51 -/
/- PM-VERBATIM-BEGIN PM1:✱73·511
✱73·511. ⊢:R∈ Cls → 1.α⊂ ᗡʻR.⊃.R⃗ʻʻα sm α [*73·51 Ř/R.*71·211.*33·2.*32·241 ]
PM-VERBATIM-END PM1:✱73·511 -/
/- PM-VERBATIM-BEGIN PM1:✱73·52
✱73·52. ⊢:R∈ 1 → Cls.α⊂ ClsʻDʻR.⊃.(Ř)_∈ʻʻα sm α
PM-VERBATIM-END PM1:✱73·52 -/
/- PM-VERBATIM-BEGIN PM1:✱73·521
✱73·521. ⊢:R∈ Cls → 1.β⊂ ClʻᗡʻR.⊃.R_∈ʻʻβ sm β [Proof as in *73·52]
PM-VERBATIM-END PM1:✱73·521 -/
/- PM-VERBATIM-BEGIN PM1:✱73·53
✱73·53. ⊢:R∈ 1 → Cls.α⊂ ClʻDʻR.⊃.Řʻʻʻα sm α [*73·52.(*37·04)]
PM-VERBATIM-END PM1:✱73·53 -/
/- PM-VERBATIM-BEGIN PM1:✱73·531
✱73·531. ⊢:R∈ Cls → 1.β⊂ ClʻᗡʻR.⊃.Rʻʻʻβ sm β [*73·521.(*37·04)]
PM-VERBATIM-END PM1:✱73·531 -/
/- PM-VERBATIM-BEGIN PM1:✱73·61
✱73·61. ⊢.x↓ ʻʻα sm α.(x↓ )↾ α∈ (x↓ ʻʻα) sm̅α [*73·27.*55·2]
PM-VERBATIM-END PM1:✱73·61 -/
/- PM-VERBATIM-BEGIN PM1:✱73·611
✱73·611. ⊢.↓ xʻʻα sm α.(↓ x)↾ α∈ (↓ xʻʻα) sm̅α [*73·27.*55·201]
PM-VERBATIM-END PM1:✱73·611 -/
/- PM-VERBATIM-BEGIN PM1:✱73·62
✱73·62. ⊢:λ⊂ Dʻx↓.⊃.ᗡʻʻλ sm λ.ᗡ↾ λ∈ (ᗡʻʻλ) sm̅λ [*73·23.*72·131·8]
PM-VERBATIM-END PM1:✱73·62 -/
/- PM-VERBATIM-BEGIN PM1:✱73·621
✱73·621. ⊢:λ⊂ Dʻ↓ x.⊃.Dʻʻλ sm λ.D↾ λ∈ (Dʻʻλ) sm̅λ [*73·23.*72·13·81]
PM-VERBATIM-END PM1:✱73·621 -/
/- PM-VERBATIM-BEGIN PM1:✱73·63
✱73·63. ⊢:S∈ α sm̅β.T↾ α,T↾ β∈ 1 → 1.α∪ β⊂ ᗡʻT.⊃.T| S| Ť∈ (Tʻʻα) sm̅(Tʻʻβ)
PM-VERBATIM-END PM1:✱73·63 -/
/- PM-VERBATIM-BEGIN PM1:✱73·69
✱73·69. ⊢:R∈ α sm̅β.α∩ γ=Λ.β∩ γ=Λ.⊃.R⊍I↾ γ∈ (α∪ γ) sm̅(β∪ γ)
PM-VERBATIM-END PM1:✱73·69 -/
/- PM-VERBATIM-BEGIN PM1:✱73·7
✱73·7. ⊢:α sm β.α∩ γ=Λ.β∩ γ=Λ.⊃.(α∪ γ) sm (β∪ γ) [*73·69·04]
PM-VERBATIM-END PM1:✱73·7 -/
/- PM-VERBATIM-BEGIN PM1:✱73·701
✱73·701. ⊢:R∈ α sm̅β.S∈ γ sm̅δ.α∩ γ=Λ.β∩ δ=Λ.⊃.R⊍S∈ (α∪ γ) sm̅(β∪ δ)
PM-VERBATIM-END PM1:✱73·701 -/
/- PM-VERBATIM-BEGIN PM1:✱73·71
✱73·71. ⊢:α sm β.γ sm δ.α∩ γ=Λ.β∩ δ=Λ.⊃.(α∪ γ) sm (β∪ δ) [*73·701·04]
PM-VERBATIM-END PM1:✱73·71 -/
/- PM-VERBATIM-BEGIN PM1:✱73·72
✱73·72. ⊢:α∪ ιʻx sm β∪ ιʻy.x∼∈ α.y∼∈ β.⊃.α sm β
PM-VERBATIM-END PM1:✱73·72 -/
/- PM-VERBATIM-BEGIN PM1:✱73·8
✱73·8. ⊢:(ᗡʻR⊂ β.β⊂ DʻR.κ = α̂(α⊂ DʻR.β-ᗡʻR ⊂ α.Řʻʻα⊂ α).⊃. DʻR∈ κ.pʻκ ⊂ DʻR
PM-VERBATIM-END PM1:✱73·8 -/
/- PM-VERBATIM-BEGIN PM1:✱73·801
✱73·801. ⊢: Hp *73·8. ⊃. β - ᗡʻR pʻκ
PM-VERBATIM-END PM1:✱73·801 -/
/- PM-VERBATIM-BEGIN PM1:✱73·802
✱73·802. ⊢: Hp*73·8.⊃.Řʻʻpʻκ ⊂ pʻκ
PM-VERBATIM-END PM1:✱73·802 -/
/- PM-VERBATIM-BEGIN PM1:✱73·81
✱73·81. ⊢: Hp*73·8.⊃.pʻκ∈ κ
PM-VERBATIM-END PM1:✱73·81 -/
/- PM-VERBATIM-BEGIN PM1:✱73·811
✱73·811. ⊢: Hp*73·8. ⊃. Řʻʻpʻκ ⊂ pʻκ - (β -ᗡʻR)
PM-VERBATIM-END PM1:✱73·811 -/
/- PM-VERBATIM-BEGIN PM1:✱73·812
✱73·812. ⊢:Hp*73·8.x∼∈ (β-ᗡʻR)∪ Řʻʻpʻκ.⊃.Řʻʻ(pʻκ-ιʻx)⊂ pʻκ-ιʻx
PM-VERBATIM-END PM1:✱73·812 -/
/- PM-VERBATIM-BEGIN PM1:✱73·82
✱73·82. ⊢:Hp*73·812.⊃.pʻκ-ιʻx=pʻκ.x∼∈ pʻκ
PM-VERBATIM-END PM1:✱73·82 -/
/- PM-VERBATIM-BEGIN PM1:✱73·821
✱73·821. ⊢:Hp*73·8.x∈ pʻκ-(β-ᗡʻR).⊃.x∈ Řʻʻpʻκ
PM-VERBATIM-END PM1:✱73·821 -/
/- PM-VERBATIM-BEGIN PM1:✱73·83
✱73·83. ⊢:Hp*73·8.⊃.pʻκ-(β-ᗡʻR)=Řʻʻpʻκ.pʻκ=(β-ᗡʻR)∪ Řʻʻpʻκ
PM-VERBATIM-END PM1:✱73·83 -/
/- PM-VERBATIM-BEGIN PM1:✱73·84
✱73·84. ⊢:Hp*73·8.⊃.β=pʻκ∪ (ᗡʻR-Řʻʻpʻκ)
PM-VERBATIM-END PM1:✱73·84 -/
/- PM-VERBATIM-BEGIN PM1:✱73·841
✱73·841. ⊢:Hp*73·8.R∈ 1 → 1.⊃.β sm ᗡʻR.β sm DʻR
PM-VERBATIM-END PM1:✱73·841 -/
/- PM-VERBATIM-BEGIN PM1:✱73·85
✱73·85. ⊢:R∈ 1 → 1.ᗡʻR⊂ β.β⊂ DʻR.⊃.β sm ᗡʻR.β sm DʻR [*73·841]
PM-VERBATIM-END PM1:✱73·85 -/
/- PM-VERBATIM-BEGIN PM1:✱73·86
✱73·86. ⊢:ᗡʻR⊂ DʻS.ᗡʻS ⊂ DʻR.⊃. Dʻ(R| S)=DʻR.ᗡʻ(R| S)⊂ ᗡʻS.ᗡʻS⊂ Dʻ(R| S)
PM-VERBATIM-END PM1:✱73·86 -/
/- PM-VERBATIM-BEGIN PM1:✱73·87
✱73·87. ⊢:R, S∈ 1 → 1.ᗡʻR⊂ DʻS.ᗡʻS⊂ DʻR.⊃.DʻR sm DʻS
PM-VERBATIM-END PM1:✱73·87 -/
/- PM-VERBATIM-BEGIN PM1:✱73·88
✱73·88. ⊢:α sm γ.β sm δ.γ⊂ β.δ⊂ α.⊃.α sm β
PM-VERBATIM-END PM1:✱73·88 -/
