/-! # PM I ✱63 — canonical transcription (PG78050, pp. 419–428) -/

/- PM-VERBATIM-BEGIN PM1:✱63·02
✱63·02. t₀ʻα = α ∪ -α Df
✱63·02. \(t_{0}ʻ\alpha = \alpha \cup -\alpha \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·02 -/
/- PM-VERBATIM-BEGIN PM1:✱63·01
✱63·01. tʻx = ιʻx ∪ - ιʻx Df
✱63·01. \(tʻx = \iotaʻx \cup - \iotaʻx \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·01 -/
/- PM-VERBATIM-BEGIN PM1:✱63·011
✱63·011. t¹ʻx = tʻx Df
✱63·011. \(t^{1}ʻx = tʻx \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·011 -/
/- PM-VERBATIM-BEGIN PM1:✱63·03
✱63·03. t₁ʻκ = t₀ʻsʻκ Df
✱63·03. \(t_{1}ʻ\kappa = t_{0}ʻsʻ\kappa \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·03 -/
/- PM-VERBATIM-BEGIN PM1:✱63·04
✱63·04. t²ʻx = tʻtʻx Df
✱63·04. \(t^{2}ʻx = tʻtʻx \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·04 -/
/- PM-VERBATIM-BEGIN PM1:✱63·041
✱63·041. t³ʻx = tʻt²ʻx Df
✱63·041. \(t^{3}ʻx = tʻt^{2}ʻx \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·041 -/
/- PM-VERBATIM-BEGIN PM1:✱63·05
✱63·05. t₂ʻκ = t₁ʻt₁ʻκ Df
✱63·05. \(t_{2}ʻ\kappa = t_{1}ʻt_{1}ʻ\kappa \quad \text{Df}\)
PM-VERBATIM-END PM1:✱63·05 -/
/- PM-VERBATIM-BEGIN PM1:✱63·051
✱63·051. t₃ʻκ = t₁ʻt₂ʻκ Df
✱63·051. \(t_{3}ʻ\kappa = t_{1}ʻt_{2}ʻ\kappa \quad\text{Df}\)
PM-VERBATIM-END PM1:✱63·051 -/
/- PM-VERBATIM-BEGIN PM1:✱63·103
✱63·103. ⊢ . x ∈ tʻx [*63·101 . *51·16]
✱63·103. \(\vdash . x \in  tʻx \quad[\text{*63·101 . *51·16}]\)
PM-VERBATIM-END PM1:✱63·103 -/
/- PM-VERBATIM-BEGIN PM1:✱63·105
✱63·105. ⊢ . α ⊂ t₀ʻα [*22·58]
✱63·105. \(\vdash . \alpha \subset t_{0}ʻ\alpha \quad[\text{*22·58}]\)
PM-VERBATIM-END PM1:✱63·105 -/
/- PM-VERBATIM-BEGIN PM1:✱63·11
✱63·11. ⊢ : x ∈ t₀ʻα . ⊃ . tʻx = α ∪ - α = t₀ʻα
Dem.
⊢ . *22·34 . (*63·02) . ⊃ ⊢ :. Hp . ⊃ : x ∈ α . ∨ . x∼∈ α :
[*20·8] ⊃ : ŷ(y ∈ α . ∨ . y∼∈ α) = ŷ(y = x . ∨ . y ≠ x) :
[*22·3·31.*51·15] ⊃ : α ∪ - α = ιʻx ∪ - ιʻx (1)
⊢ . (1) . (*63·01·02) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱63·11 -/
/- PM-VERBATIM-BEGIN PM1:✱63·13
✱63·13. ⊢ : φ x . φ y . ⊃ . y ∈ tʻx [*63·12 . Imp . Add]
✱63·13. \(\vdash : \phi x . \phi y . \supset . y \in  tʻx \quad[\text{*63·12 . Imp . Add}]\)
PM-VERBATIM-END PM1:✱63·13 -/
/- PM-VERBATIM-BEGIN PM1:✱63·15
✱63·15. ⊢ . t₀ʻtʻx = tʻx [*63·14·102]
✱63·15. \(\vdash . t_{0}ʻtʻx = tʻx \quad[\text{*63·14·102}]\)
PM-VERBATIM-END PM1:✱63·15 -/
/- PM-VERBATIM-BEGIN PM1:✱63·19
✱63·19. ⊢.tʻt₀ʻα=tʻα
Dem.
⊢.*63·105.*22·42. ⊃⊢.α⊂ t₀ʻα.t₀ʻα⊂ t₀ʻα.
[*63·13] ⊃⊢.α∈ tʻt₀ʻα.
[*63·16] ⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·19 -/
/- PM-VERBATIM-BEGIN PM1:✱63·16
✱63·16. ⊢:x∈ tʻy.≡.y∈ tʻx.≡.∃ !tʻx∩ tʻy.≡.tʻx=tʻy
Dem.
⊢.*63·101.*51·23. ⊃⊢:x∈ tʻy.≡.y∈ tʻx (1)
⊢.*63·13. ⊃⊢:(∃ z).z∈ tʻx.z∈ tʻy.⊃.y∈ tʻx (2)
⊢.*63·103. ⊃⊢:y∈ tʻx.⊃.y∈ tʻx.y∈ tʻy.
[*10·24] ⊃.∃ !tʻx∩ tʻy (3)
⊢.(2).(3). ⊃⊢:y∈ tʻx.≡.∃ !tʻx∩ tʻy (4)
⊢.*63·103. ⊃⊢:tʻx=tʻy.⊃.y∈ tʻx (5)
⊢.*63·13. ⊃⊢:y∈ tʻx.z∈ tʻx.⊃.z∈ tʻy (6)
⊢.*63·13. ⊃⊢:x∈ tʻy.z∈ tʻy.⊃.z∈ tʻx:
[(1)] ⊃⊢:y∈ tʻx.z∈ tʻy.⊃.z∈ tʻx (7)
⊢.(6).(7). ⊃⊢:. y∈ tʻx.⊃:z∈ tʻx.≡.z∈ tʻy (8)
⊢.(5).(8). ⊃⊢:. y∈ tʻx.≡.tʻx=tʻy (9)
⊢.(1).(4).(9).⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·16 -/
/- PM-VERBATIM-BEGIN PM1:✱63·32
✱63·32. ⊢.t₁ʻκ=sʻt₀ʻκ [*63·31.(*63·02·03)]
✱63·32. \(\vdash.t_{1}ʻ\kappa=sʻt_{0}ʻ\kappa \quad[\text{*63·31.(*63·02·03)}]\)
PM-VERBATIM-END PM1:✱63·32 -/
/- PM-VERBATIM-BEGIN PM1:✱63·371
✱63·371. ⊢:β⊂ t₀ʻα.≡.β∈ tʻα
Dem.
⊢.*63·181.⊃⊢:β⊂ t₀ʻα. ≡.t₀ʻα=t₀ʻβ.
[*63·37] ≡.tʻα=tʻβ.
[*63·16] ≡.β∈ tʻα:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·371 -/
/- PM-VERBATIM-BEGIN PM1:✱63·383
✱63·383. ⊢.tʻt₁ʻκ=t₀ʻκ
Dem.
⊢.*63·38·18.*10·11·23·35.⊃⊢:α∈ t₀ʻκ.⊃.tʻt₁ʻκ =tʻt₀ʻα
[*63·19] =tʻα
[*63·11] =t₀ʻκ (1)
⊢.(1).*10·11·23.*63·18.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·383 -/
/- PM-VERBATIM-BEGIN PM1:✱63·5
✱63·5. ⊢:x∈ t₀ʻα.≡.α∈ t²ʻx.≡.α⊂ tʻx.≡.tʻx=t₀ʻα
Dem.
⊢.*63·15.⊃⊢:α⊂ tʻx. ≡.α⊂ t₀ʻtʻx.
[*63·371] ≡.α∈ t²ʻx (1)
⊢.(1).*63·22.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·5 -/
/- PM-VERBATIM-BEGIN PM1:✱63·51
✱63·51. ⊢:α∈ t₀ʻκ.≡.α⊂ t₁ʻκ.≡.κ⊂ tʻα.≡.tʻα=t₀ʻκ
Dem.
⊢.*4·2.(*63·03).⊃⊢:α⊂ t₁ʻκ. ≡.α⊂ t₀ʻsʻκ.
[*63·371·19] ≡.α∈ tʻt₀ʻsʻκ.
[*4·2.(*63·03)] ≡.α∈ tʻt₁ʻκ.
[*63·383] ≡.α∈ t₀ʻκ (1)
⊢.(1).*63·5·22.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·51 -/
/- PM-VERBATIM-BEGIN PM1:✱63·52
✱63·52. ⊢:α∈ t₁ʻλ.≡.α⊂ t₂ʻλ.≡.λ⊂ t²ʻα.≡.tʻα=t₁ʻλ.≡.t²ʻα=t₀ʻλ
Dem.
⊢.*63·51 sʻλ/κ.(*63·03).⊃
⊢:α∈ t₁ʻλ. ≡.α⊂ t₁ʻsʻλ.
[*63·321] ≡.α⊂ t₁ʻt₀ʻsʻλ.
[(*63·03·05)] ≡.α⊂ t₂ʻλ (1)
⊢.*63·321.⊃
⊢:α∈ t₁ʻλ. ≡.α∈ t₀ʻt₁ʻλ.
[*63·22] ≡.tʻα=t₀ʻt₁ʻλ
[*63·321] =t₁ʻλ. (2)
[*63·391·41·42] ≡.t²ʻα=t₀ʻλ. (3)
[*63·15·181] ≡.λ⊂ t₀ʻt²ʻα.
[*63·15] ≡.λ⊂ t²ʻα (4)
⊢.(1).(2).(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·52 -/
/- PM-VERBATIM-BEGIN PM1:✱63·53
✱63·53. ⊢:x∈ t₀ʻα.≡.t²ʻx=tʻα.≡.tʻx=t₀ʻα
Dem.
⊢.*30·37.⊃⊢:t²ʻx=tʻα. ⊃.t₁ʻt²ʻx=t₁ʻtʻα.
[*63·43·34] ⊃.tʻx=t₀ʻα (1)
⊢.*63·19. ⊃⊢:tʻx=t₀ʻα.⊃.t²ʻx=tʻα (2)
⊢.(1).(2).*63·5.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·53 -/
/- PM-VERBATIM-BEGIN PM1:✱63·64
✱63·64. ⊢.tʻβ=t₀ʻιʻʻβ
Dem.
⊢.*51·16.*37·62.⊃
⊢:x∈ β. ⊃.x∈ ιʻx.ιʻx∈ ιʻʻβ.
[*63·105·38] ⊃.x∈ t₀ʻιʻx.t₀ʻιʻx=t₁ʻιʻʻβ.
[*13·13] ⊃.x∈ t₁ʻιʻʻβ (1)
⊢.(1).*63·51.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·64 -/
/- PM-VERBATIM-BEGIN PM1:✱63·66
✱63·66. ⊢.Clʻtʻx=t²ʻx [*63·5.*60·2]
✱63·66. \(\vdash.\text{Cl}ʻtʻx=t^{2}ʻx \quad[\text{*63·5.*60·2}]\)
PM-VERBATIM-END PM1:✱63·66 -/
/- PM-VERBATIM-BEGIN PM1:✱63·1
✱63·1. ⊢ . (x) . x ∈ t₀ʻα [*22·88]
✱63·1. \(\vdash . (x) . x \in  t_{0}ʻ\alpha \quad[\text{*22·88}]\)
PM-VERBATIM-END PM1:✱63·1 -/
/- PM-VERBATIM-BEGIN PM1:✱63·101
✱63·101. ⊢ . tʻx = t₀ʻιʻx = ιʻx ∪ - ιʻx [*20·2 . (*63·01·02)]
✱63·101. \(\vdash . tʻx = t_{0}ʻ\iotaʻx = \iotaʻx \cup - \iotaʻx \quad[\text{*20·2 . (*63·01·02)}]\)
PM-VERBATIM-END PM1:✱63·101 -/
/- PM-VERBATIM-BEGIN PM1:✱63·102
✱63·102. ⊢ . (y) . y ∈ tʻx [*63·1·101]
✱63·102. \(\vdash . (y) . y \in  tʻx \quad[\text{*63·1·101}]\)
PM-VERBATIM-END PM1:✱63·102 -/
/- PM-VERBATIM-BEGIN PM1:✱63·104
✱63·104. ⊢ : φ x . ∼φ y . ⊃ . y ∈ tʻx [*63·101 . *13·14]
✱63·104. \(\vdash : \phi x . {\sim}\phi y . \supset . y \in  tʻx \quad[\text{*63·101 . *13·14}]\)
PM-VERBATIM-END PM1:✱63·104 -/
/- PM-VERBATIM-BEGIN PM1:✱63·106
✱63·106. ⊢ . t₀ʻα = t₀ʻ - α [*22·8]
✱63·106. \(\vdash . t_{0}ʻ\alpha = t_{0}ʻ - \alpha \quad[\text{*22·8}]\)
PM-VERBATIM-END PM1:✱63·106 -/
/- PM-VERBATIM-BEGIN PM1:✱63·107
✱63·107. ⊢ :. (x) . φ x : f(φ y) : ⊃ . φ y
Dem.
⊢ . *2·11 . *10·11 . ⊃ ⊢ . (y) . f(φ y) ∨ ∼f(φ y) (1)
⊢ . (1) . *10·13·221 . ⊃ ⊢ :. (x) . φ x . ⊃ : φ y . f(φ y) ∨ ∼f(φ y) :
[*5·1] ⊃ : φ y . ≡ . f(φ y) ∨ ∼f(φ y) :
[*2·2] ⊃ : f(φ y) . ⊃ . φ y :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱63·107 -/
/- PM-VERBATIM-BEGIN PM1:✱63·108
✱63·108. ⊢ : f(y ∈ tʻx) . ⊃ . y ∈ tʻx [*63·107·102]
✱63·108. \(\vdash : f(y \in  tʻx) . \supset . y \in  tʻx \quad[\text{*63·107·102}]\)
PM-VERBATIM-END PM1:✱63·108 -/
/- PM-VERBATIM-BEGIN PM1:✱63·109
✱63·109. ⊢ : f(y ∈ t₀ʻα) . ⊃ . y ∈ t₀ʻα [*63·107·1]
✱63·109. \(\vdash : f(y \in  t_{0}ʻ\alpha) . \supset . y \in  t_{0}ʻ\alpha \quad[\text{*63·107·1}]\)
PM-VERBATIM-END PM1:✱63·109 -/
/- PM-VERBATIM-BEGIN PM1:✱63·12
✱63·12. ⊢ :. φ x ∨ ∼φ x . ⊃ : φ y ∨ ∼φ y . ≡y . y ∈ tʻx
Dem.
⊢ . *63·11 . *20·8 . ⊃ ⊢ :. Hp . ⊃ : tʻx = ẑ(φ z) ∪ - ẑ(φ z) :
[*20·31 . *22·391·392] ⊃ : y ∈ tʻx . ≡y . φ y ∨ ∼φ y :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱63·12 -/
/- PM-VERBATIM-BEGIN PM1:✱63·14
✱63·14. ⊢ : (x) . x ∈ α . ⊃ . t₀ʻα = α [*24·14·17·24 . (*63·02)]
✱63·14. \(\vdash : (x) . x \in  \alpha . \supset . t_{0}ʻ\alpha = \alpha \quad[\text{*24·14·17·24 . (*63·02)}]\)
PM-VERBATIM-END PM1:✱63·14 -/
/- PM-VERBATIM-BEGIN PM1:✱63·151
✱63·151. ⊢ . t₀ʻt₀ʻα = t₀ʻα [*63·14·1]
✱63·151. \(\vdash . t_{0}ʻt_{0}ʻ\alpha = t_{0}ʻ\alpha \quad[\text{*63·14·1}]\)
PM-VERBATIM-END PM1:✱63·151 -/
/- PM-VERBATIM-BEGIN PM1:✱63·152
✱63·152. ⊢ . x ∈ t₀ʻtʻx [*63·103·15]
✱63·152. \(\vdash . x \in  t_{0}ʻtʻx    \quad[\text{*63·103·15}]\)
PM-VERBATIM-END PM1:✱63·152 -/
/- PM-VERBATIM-BEGIN PM1:✱63·17
✱63·17. ⊢:y∈ tʻx.z∈ tʻy.⊃.z∈ tʻx [*63·16]
✱63·17. \(\vdash:y\in tʻx.z\in tʻy.\supset.z\in tʻx \quad[\text{*63·16}]\)
PM-VERBATIM-END PM1:✱63·17 -/
/- PM-VERBATIM-BEGIN PM1:✱63·18
✱63·18. ⊢.∃ !t₀ʻα [*10·25.*63·1]
✱63·18. \(\vdash.\exists !t_{0}ʻ\alpha \quad[\text{*10·25.*63·1}]\)
PM-VERBATIM-END PM1:✱63·18 -/
/- PM-VERBATIM-BEGIN PM1:✱63·181
✱63·181. ⊢:α⊂ t₀ʻβ.≡.β⊂ t₀ʻα.≡.∃ !t₀ʻα∩ t₀ʻβ.≡.t₀ʻα=t₀ʻβ
Dem.
⊢.*63·105. ⊃⊢:t₀ʻα=t₀ʻβ.⊃.α⊂ t₀ʻβ (1)
⊢.24·6. ⊃⊢:. α⊂ t₀ʻβ.⊃:α=t₀ʻβ.∨.∃ !t₀ʻβ-α (2)
⊢.*63·151. ⊃⊢:α=t₀ʻβ.⊃.t₀ʻα=t₀ʻβ (3)
⊢.*63·11. ⊃⊢:x∈ t₀ʻβ.x∈ -α.⊃.tʻx=t₀ʻβ.tʻx=t₀ʻ-α.
[*63·106] ⊃.t₀ʻα=t₀ʻβ (4)
⊢.(2).(3).(4). ⊃⊢:α⊂ t₀ʻβ.⊃.t₀ʻα=t₀ʻβ (5)
⊢.(1).(5). ⊃⊢:α⊂ t₀ʻβ.≡.t₀ʻα=t₀ʻβ (6)
⊢.(6) β, α/α, β. ⊃⊢:β⊂ t₀ʻα.≡.t₀ʻα=t₀ʻβ (7)
⊢.*63·11. ⊃⊢:x∈ t₀ʻα∩ t₀ʻβ.⊃.tʻx=t₀ʻα.tʻx=t₀ʻβ.
[*13·171] ⊃.t₀ʻα=t₀ʻβ (8)
⊢.*63·18. ⊃⊢:t₀ʻα=t₀ʻβ.⊃.∃ !t₀ʻα∩ t₀ʻβ (9)
⊢.(8).(9). ⊃⊢:∃ !t₀ʻα∩ t₀ʻβ.≡.t₀ʻα=t₀ʻβ (10)
⊢.(6).(7).(10). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·181 -/
/- PM-VERBATIM-BEGIN PM1:✱63·182
✱63·182. ⊢:α⊂ t₀ʻβ.β⊂ t₀ʻγ.⊃.α⊂ t₀ʻγ [*63·181]
✱63·182. \(\vdash:\alpha\subset t_{0}ʻ\beta.\beta\subset t_{0}ʻ\gamma.\supset.\alpha\subset t_{0}ʻ\gamma \quad[\text{*63·181}]\)
PM-VERBATIM-END PM1:✱63·182 -/
/- PM-VERBATIM-BEGIN PM1:✱63·191
✱63·191. ⊢.t₀ʻα∈ tʻα [*63·103·19]
✱63·191. \(\vdash.t_{0}ʻ\alpha\in tʻ\alpha \quad[\text{*63·103·19}]\)
PM-VERBATIM-END PM1:✱63·191 -/
/- PM-VERBATIM-BEGIN PM1:✱63·2
✱63·2. ⊢:x∈ t₀ʻα.α∈ t₀ʻκ.⊃.t²ʻx=tʻα=t₀ʻκ
Dem.
⊢.*63·11. ⊃⊢:Hp.⊃.tʻx=t₀ʻα.tʻα=t₀ʻκ (1)
⊢.(1).*63·19.(*63·04). ⊃⊢:Hp.⊃.t²ʻx=tʻα=t₀ʻκ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·2 -/
/- PM-VERBATIM-BEGIN PM1:✱63·21
✱63·21. ⊢:α⊂ tʻx.≡.t₀ʻα=tʻx
Dem.
⊢.*63·181·15.⊃⊢:α⊂ tʻx.≡.t₀ʻα =t₀ʻtʻx
[*63·15] =tʻx:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·21 -/
/- PM-VERBATIM-BEGIN PM1:✱63·22
✱63·22. ⊢:α⊂ tʻx.≡.x∈ t₀ʻα.≡.tʻx=t₀ʻα
Dem.
⊢.*63·103. ⊃⊢:tʻx=t₀ʻα.⊃.x∈ t₀ʻα (1)
⊢.(1).*63·11. ⊃⊢:x∈ t₀ʻα.≡.tʻx=t₀ʻα (2)
⊢.(2).*63·21. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·22 -/
/- PM-VERBATIM-BEGIN PM1:✱63·23
✱63·23. ⊢:α⊂ tʻx.κ⊂ tʻα.⊃.t²ʻx=tʻα=t₀ʻκ [*63·2·22]
✱63·23. \(\vdash:\alpha\subset tʻx.\kappa\subset tʻ\alpha.\supset.t^{2}ʻx=tʻ\alpha=t_{0}ʻ\kappa \quad[\text{*63·2·22}]\)
PM-VERBATIM-END PM1:✱63·23 -/
/- PM-VERBATIM-BEGIN PM1:✱63·3
✱63·3. ⊢:(α).α∈ κ.⊃.(x).x∈ sʻκ
Dem.
⊢.*10·1.⊃⊢:Hp. ⊃.V∈ κ.
[*40·221] ⊃.sʻκ=V.
[*24·14] ⊃.(x).x∈ sʻκ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·3 -/
/- PM-VERBATIM-BEGIN PM1:✱63·31
✱63·31. ⊢.sʻ(κ∪ -κ)=sʻκ∪ -sʻκ
Dem.
⊢.*40·171. ⊃⊢:. x∈ sʻ(κ∪ -κ).≡:x∈ sʻκ.∨.x∈ sʻ-κ (1)
⊢.(1).*22·88.*63·3. ⊃⊢:x∈ sʻκ.∨.x∈ sʻ-κ (2)
⊢.*22·88. ⊃⊢:x∈ sʻκ.∨.x∈ -sʻκ (3)
⊢.(2).(3).*10·221·13. ⊃
⊢:. x∈ sʻκ.∨.x∈ sʻ-κ:x∈ sʻκ.∨.x∈ -sʻκ:.
[(1).*5·1] ⊃⊢:. x∈ sʻ(κ∪ -κ).≡:x∈ sʻκ.∨.x∈ -sʻκ:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·31 -/
/- PM-VERBATIM-BEGIN PM1:✱63·321
✱63·321. ⊢.t₁ʻκ=t₁ʻt₀ʻκ=t₀ʻt₁ʻκ
Dem.
⊢.*20·2.(*63·03).⊃⊢.t₁ʻt₀ʻκ =t₀ʻsʻt₀ʻκ
[*63·32] =t₀ʻt₁ʻκ (1)
[*20·2.(*63·03)] =t₀ʻt₀ʻsʻκ
[*63·151] =t₀ʻsʻκ
[*20·2.(*63·03)] =t₁ʻκ (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·321 -/
/- PM-VERBATIM-BEGIN PM1:✱63·33
✱63·33. ⊢:t₀ʻκ=t₀ʻλ.⊃.t₁ʻκ=t₁ʻλ [*30·37.*63·32]
✱63·33. \(\vdash:t_{0}ʻ\kappa=t_{0}ʻ\lambda.\supset.t_{1}ʻ\kappa=t_{1}ʻ\lambda \quad[\text{*30·37.*63·32}]\)
PM-VERBATIM-END PM1:✱63·33 -/
/- PM-VERBATIM-BEGIN PM1:✱63·34
✱63·34. ⊢.t₁ʻtʻα=t₀ʻα=sʻtʻα
Dem.
⊢.*63·32.⊃⊢.t₁ʻtʻα =sʻt₀ʻtʻα
[*63·15] =sʻtʻα (1)
[*63·101] =sʻ(ιʻα∪ -ιʻα)
[*63·31] =sʻιʻα∪ -sʻιʻα
[*53·02] =α∪ -α
[(*63·02)] =t₀ʻα (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·34 -/
/- PM-VERBATIM-BEGIN PM1:✱63·35
✱63·35. ⊢:tʻα=tʻβ.⊃.t₀ʻα=t₀ʻβ [*30·37.*63·34]
✱63·35. \(\vdash:tʻ\alpha=tʻ\beta.\supset.t_{0}ʻ\alpha=t_{0}ʻ\beta \quad[\text{*30·37.*63·34}]\)
PM-VERBATIM-END PM1:✱63·35 -/
/- PM-VERBATIM-BEGIN PM1:✱63·36
✱63·36. ⊢:tʻκ=tʻλ.⊃.t₁ʻκ=t₁ʻλ [*63·35·33]
✱63·36. \(\vdash:tʻ\kappa=tʻ\lambda.\supset.t_{1}ʻ\kappa=t_{1}ʻ\lambda \quad[\text{*63·35·33}]\)
PM-VERBATIM-END PM1:✱63·36 -/
/- PM-VERBATIM-BEGIN PM1:✱63·361
✱63·361. ⊢:t₀ʻα=t₀ʻβ.⊃.tʻα=tʻβ [*30·37.*63·19]
✱63·361. \(\vdash:t_{0}ʻ\alpha=t_{0}ʻ\beta.\supset.tʻ\alpha=tʻ\beta \quad[\text{*30·37.*63·19}]\)
PM-VERBATIM-END PM1:✱63·361 -/
/- PM-VERBATIM-BEGIN PM1:✱63·37
✱63·37. ⊢:t₀ʻα=t₀ʻβ.≡.tʻα=tʻβ [*63·35·361]
✱63·37. \(\vdash:t_{0}ʻ\alpha=t_{0}ʻ\beta.\equiv.tʻ\alpha=tʻ\beta \quad[\text{*63·35·361}]\)
PM-VERBATIM-END PM1:✱63·37 -/
/- PM-VERBATIM-BEGIN PM1:✱63·38
✱63·38. ⊢:α∈ t₀ʻκ.x∈ t₀ʻα.⊃.tʻx=t₀ʻα=t₁ʻκ
Dem.
⊢.*63·11. ⊃⊢:Hp.⊃.tʻx =t₀ʻα.tʻα=t₀ʻκ (1)
⊢.(1).*63·34.⊃⊢:Hp.⊃.t₀ʻα =t₁ʻt₀ʻκ
[*63·151·33] =t₁ʻκ (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·38 -/
/- PM-VERBATIM-BEGIN PM1:✱63·381
✱63·381. ⊢:x∈ t₁ʻκ.⊃.tʻx=t₁ʻκ
Dem.
⊢.*63·38·105. ⊃⊢:α∈ t₀ʻκ.x∈ α.⊃.tʻx=t₁ʻκ:
[*10·11·23.*40·11] ⊃⊢:x∈ sʻt₀ʻκ.⊃.tʻx=t₁ʻκ (1)
⊢.(1).*63·32. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·381 -/
/- PM-VERBATIM-BEGIN PM1:✱63·382
✱63·382. ⊢.∃ !t₁ʻκ [*63·18.(*63·03)]
✱63·382. \(\vdash.\exists !t_{1}ʻ\kappa \quad[\text{*63·18.(*63·03)}]\)
PM-VERBATIM-END PM1:✱63·382 -/
/- PM-VERBATIM-BEGIN PM1:✱63·384
✱63·384. ⊢:t₁ʻκ=t₁ʻλ.⊃.t₀ʻκ=t₀ʻλ.tʻκ=tʻλ [*63·383·37]
✱63·384. \(\vdash:t_{1}ʻ\kappa=t_{1}ʻ\lambda.\supset.t_{0}ʻ\kappa=t_{0}ʻ\lambda.tʻ\kappa=tʻ\lambda \quad[\text{*63·383·37}]\)
PM-VERBATIM-END PM1:✱63·384 -/
/- PM-VERBATIM-BEGIN PM1:✱63·39
✱63·39. ⊢:t₁ʻκ=t₁ʻλ.≡.t₀ʻκ=t₀ʻλ.≡.tʻκ=tʻλ [*63·33·384·37]
✱63·39. \(\vdash:t_{1}ʻ\kappa=t_{1}ʻ\lambda.\equiv.t_{0}ʻ\kappa=t_{0}ʻ\lambda.\equiv.tʻ\kappa=tʻ\lambda  \quad[\text{*63·33·384·37}]\)
PM-VERBATIM-END PM1:✱63·39 -/
/- PM-VERBATIM-BEGIN PM1:✱63·391
✱63·391. ⊢:tʻx=tʻy.≡.t²ʻx=t²ʻy
Dem.
⊢.*63·39.⊃⊢:t²ʻx=t²ʻy. ≡.t₀ʻtʻx=t₀ʻtʻy.
[*63·15] ≡.tʻx=tʻy:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·391 -/
/- PM-VERBATIM-BEGIN PM1:✱63·392
✱63·392. ⊢:t₂ʻκ=t₂ʻλ.≡.t₁ʻκ=t₁ʻλ.≡.t₀ʻκ=t₀ʻλ
Dem.
⊢.*63·39.⊃⊢:t₂ʻκ=t₂ʻλ. ≡.t₀ʻt₁ʻκ=t₀ʻt₁ʻλ.
[*63·321] ≡.t₁ʻκ=t₁ʻλ (1)
⊢.(1).*63·39.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·392 -/
/- PM-VERBATIM-BEGIN PM1:✱63·4
✱63·4. ⊢:α∈ t₀ʻκ.κ∈ t₀ʻλ.⊃.t₀ʻα=t₁ʻκ=t₂ʻλ
Dem.
⊢.*63·38·18.⊃⊢:Hp. ⊃.t₀ʻα=t₁ʻκ.t₀ʻκ=t₁ʻλ.
[*30·37.(*63·05)] ⊃.t₀ʻα=t₁ʻκ.t₁ʻt₀ʻκ=t₂ʻλ.
[*63·321] ⊃.t₀ʻα=t₁ʻκ.t₁ʻκ=t₂ʻλ:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·4 -/
/- PM-VERBATIM-BEGIN PM1:✱63·41
✱63·41. ⊢.tʻt₂ʻλ=t₁ʻλ
Dem.
⊢.*63·4·18.*10·11·23·35.⊃⊢:κ∈ t₀ʻλ.⊃.tʻt₂ʻλ =tʻt₁ʻκ
[*63·383] =t₀ʻκ
[*63·38·18.*10·11·23·35] =t₁ʻλ (1)
⊢.(1).*63·18.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·41 -/
/- PM-VERBATIM-BEGIN PM1:✱63·42
✱63·42. ⊢.t²ʻt₂ʻλ=t₀ʻλ [*30·37.*63·41·383]
✱63·42. \(\vdash.t^{2}ʻt_{2}ʻ\lambda=t_{0}ʻ\lambda \quad[\text{*30·37.*63·41·383}]\)
PM-VERBATIM-END PM1:✱63·42 -/
/- PM-VERBATIM-BEGIN PM1:✱63·43
✱63·43. ⊢.t₁ʻt²ʻx=tʻx [*63·34·15]
✱63·43. \(\vdash.t_{1}ʻt^{2}ʻx=tʻx \quad[\text{*63·34·15}]\)
PM-VERBATIM-END PM1:✱63·43 -/
/- PM-VERBATIM-BEGIN PM1:✱63·44
✱63·44. ⊢.t₂ʻt²ʻα=t₀ʻα [*63·43·34]
✱63·44. \(\vdash.t_{2}ʻt^{2}ʻ\alpha=t_{0}ʻ\alpha \quad[\text{*63·43·34}]\)
PM-VERBATIM-END PM1:✱63·44 -/
/- PM-VERBATIM-BEGIN PM1:✱63·54
✱63·54. ⊢:α∈ t₀ʻκ.≡.t₀ʻα=t₁ʻκ.≡.tʻα=t₀ʻκ.≡.t²ʻα=tʻκ
Dem.
⊢.*30·37.⊃⊢:tʻα=t₀ʻκ. ⊃.t₁ʻtʻα=t₁ʻt₀ʻκ.
[*63·34·321] ⊃.t₀ʻα=t₁ʻκ (1)
⊢.*30·37. ⊃⊢:t₀ʻα=t₁ʻκ.⊃.tʻt₀ʻα=tʻt₁ʻκ.
[*63·19·383] ⊃.tʻα=t₀ʻκ (2)
⊢.(1).(2).*63·51·53.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·54 -/
/- PM-VERBATIM-BEGIN PM1:✱63·56
✱63·56. ⊢:x∈ t₁ʻκ.≡.tʻx=t₁ʻκ.≡.t²ʻx=t₀ʻκ
Dem.
⊢.*63·321. ⊃⊢:x∈ t₁ʻκ. ≡.x∈ t₀ʻt₁ʻκ.
[*63·53] ≡.t²ʻx=tʻt₁ʻκ (1)
[*63·383] =t₀ʻκ (2)
⊢.(1).*63·53.⊃⊢:x∈ t₁ʻκ. ≡.tʻx=t₀ʻt₁ʻκ
[*63·321] =t₁ʻκ (3)
⊢.(2).(3).⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·56 -/
/- PM-VERBATIM-BEGIN PM1:✱63·61
✱63·61. ⊢.t²ʻx=tʻιʻx [*63·19·101]
✱63·61. \(\vdash.t^{2}ʻx=tʻ\iotaʻx \quad[\text{*63·19·101}]\)
PM-VERBATIM-END PM1:✱63·61 -/
/- PM-VERBATIM-BEGIN PM1:✱63·62
✱63·62. ⊢:x∈ t₀ʻα.⊃.ιʻx∈ tʻα.tʻιʻx=tʻα
Dem.
⊢.*63·53.⊃⊢:Hp. ⊃.t²ʻx=tʻα.
[*63·61] ⊃.tʻιʻx=tʻα.
[*63·16] ⊃.ιʻx∈ tʻα:⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·62 -/
/- PM-VERBATIM-BEGIN PM1:✱63·621
✱63·621. ⊢:x∈ α.⊃.ιʻx∈ tʻα.tʻιʻx=tʻα [*63·62.*63·105]
✱63·621. \(\vdash:x\in \alpha.\supset.\iotaʻx\in tʻ\alpha.tʻ\iotaʻx=tʻ\alpha \quad[\text{*63·62.*63·105}]\)
PM-VERBATIM-END PM1:✱63·621 -/
/- PM-VERBATIM-BEGIN PM1:✱63·63
✱63·63. ⊢:x∈ t₀ʻα.⊃.ιʻιʻx∈ t²ʻα.tʻιʻιʻx=t²ʻα
Dem.
⊢.*63·101. ⊃⊢.tʻιʻx=t₀ʻιʻιʻx.
[*63·62] ⊃⊢:Hp. ⊃.tʻα=t₀ʻιʻιʻx.
[*63·19] ⊃.t²ʻα=tʻιʻιʻx (1)
⊢.(1).*63·103.⊃⊢.Prop
PM-VERBATIM-END PM1:✱63·63 -/
/- PM-VERBATIM-BEGIN PM1:✱63·65
✱63·65. ⊢.Clʻt₀ʻα=tʻα [*63·371.*60·2]
✱63·65. \(\vdash.\text{Cl}ʻt_{0}ʻ\alpha=tʻ\alpha \quad[\text{*63·371.*60·2}]\)
PM-VERBATIM-END PM1:✱63·65 -/
/- PM-VERBATIM-BEGIN PM1:✱63·661
✱63·661. ⊢.tʻClʻα=t²ʻα [*60·34.*63·105·53]
✱63·661. \(\vdash.tʻ\text{Cl}ʻ\alpha=t^{2}ʻ\alpha \quad[\text{*60·34.*63·105·53}]\)
PM-VERBATIM-END PM1:✱63·661 -/
/- PM-VERBATIM-BEGIN PM1:✱63·67
✱63·67. ⊢.Clʻt₁ʻκ=t₀ʻκ [*63·51.*60·2]
✱63·67. \(\vdash.\text{Cl}ʻt_{1}ʻ\kappa=t_{0}ʻ\kappa \quad[\text{*63·51.*60·2}]\)
PM-VERBATIM-END PM1:✱63·67 -/
/- PM-VERBATIM-BEGIN PM1:✱63·68
✱63·68. ⊢.Clʻt₂ʻκ=t₁ʻκ [*63·52.*60·2]
✱63·68. \(\vdash.\text{Cl}ʻt_{2}ʻ\kappa=t_{1}ʻ\kappa \quad[\text{*63·52.*60·2}]\)
PM-VERBATIM-END PM1:✱63·68 -/

/- PM-VERBATIM-BEGIN PM1:✱63·55
✱63·55. ⊢:κ∈ t₀ʻλ.≡.t₁ʻκ=t₂ʻλ.≡.t₀ʻκ=t₁ʻλ.≡.tʻκ=t₀ʻλ.≡.t²ʻκ=tʻλ [Proof as in *63·54]
PM-VERBATIM-END PM1:✱63·55 -/
/- PM-VERBATIM-BEGIN PM1:✱63·57
✱63·57. ⊢:α∈ t₁ʻλ.≡.t₀ʻα=t₂ʻλ.≡.tʻα=t₁ʻλ.≡.t²ʻα=t₀ʻλ [Proof as in *63·56]
PM-VERBATIM-END PM1:✱63·57 -/
