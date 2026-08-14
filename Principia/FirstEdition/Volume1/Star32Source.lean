/-! PM I ✱32, canonical PG78050 transcription. -/

namespace PM.FirstEdition.Volume1.Star32Source

universe u v

/-- Class and relation extensions used by the four eliminable definitions
printed at ✱32·01–·04. -/
abbrev ClassExtension (α : Sort u) := α → Prop
abbrev RelationExtension (α : Sort u) (β : Sort v) := α → β → Prop

/-- ✱32·01: the right-sectional function of a relation. -/
def star_32_01 (R : RelationExtension α β) : β → ClassExtension α :=
  fun y x => R x y

/-- ✱32·02: the left-sectional function of a relation. -/
def star_32_02 (R : RelationExtension α β) : α → ClassExtension β :=
  fun x y => R x y

/-- ✱32·03: `sg` is the relation holding exactly when `A` is the
right-sectional function of `R`. -/
def star_32_03 (A : β → ClassExtension α) (R : RelationExtension α β) : Prop :=
  A = star_32_01 R

/-- ✱32·04: `gs` is the relation holding exactly when `A` is the
left-sectional function of `R`. -/
def star_32_04 (A : α → ClassExtension β) (R : RelationExtension α β) : Prop :=
  A = star_32_02 R

end PM.FirstEdition.Volume1.Star32Source
/- PM-VERBATIM-BEGIN PM1:✱32·01
R⃗ = α̂ŷ{α = x̂(x R y)} Df
✱32·01. \(\overrightarrow{R} = \hat{\alpha}\hat{y}\{\alpha = \hat{x}(x R y)\} \quad \text{Df}\)
PM-VERBATIM-END PM1:✱32·01 -/
/- PM-VERBATIM-BEGIN PM1:✱32·02
R⃖ = β̂x̂{β = ŷ(xRy)} Df
✱32·02. \(\overleftarrow{R} = \hat{\beta}\hat{x}\{\beta = \hat{y}(xRy)\} \quad \text{Df}\)
PM-VERBATIM-END PM1:✱32·02 -/
/- PM-VERBATIM-BEGIN PM1:✱32·03
sg=ÂR̂(A=R⃗) Df
✱32·03. \(\text{sg}=\hat{A}\hat{R}(A=\overrightarrow{R}) \quad\text{Df}\)
PM-VERBATIM-END PM1:✱32·03 -/
/- PM-VERBATIM-BEGIN PM1:✱32·04
gs=ÂR̂(A=R⃖) Df
✱32·04. \(\text{gs}=\hat{A}\hat{R}(A=\overleftarrow{R}) \quad\text{Df}\)
PM-VERBATIM-END PM1:✱32·04 -/
/- PM-VERBATIM-BEGIN PM1:✱32·13
✱32·13. ⊢.R⃗ʻy=x̂(xRy) [*32·11.*20·59]
PM-VERBATIM-END PM1:✱32·13 -/
/- PM-VERBATIM-BEGIN PM1:✱32·131
✱32·131. ⊢.R⃖ʻx=ŷ(xRy) [*32·111.*20·59]
PM-VERBATIM-END PM1:✱32·131 -/
/- PM-VERBATIM-BEGIN PM1:✱32·16
✱32·16. ⊢:R⃗=S⃗.≡.R⃖=S⃖.≡.R=S [*32·14·15]
PM-VERBATIM-END PM1:✱32·16 -/
/- PM-VERBATIM-BEGIN PM1:✱32·1
✱32·1. ⊢:αR⃗y.≡.α=x̂(xRy) [*21·3.(*32·01)]
PM-VERBATIM-END PM1:✱32·1 -/
/- PM-VERBATIM-BEGIN PM1:✱32·101
✱32·101. ⊢:βR⃖x.≡.β=ŷ(xRy) [*21·3.(*32·02)]
PM-VERBATIM-END PM1:✱32·101 -/
/- PM-VERBATIM-BEGIN PM1:✱32·11
✱32·11. ⊢.x̂(xRy)=R⃗ʻy [*32·1.*30·3]
PM-VERBATIM-END PM1:✱32·11 -/
/- PM-VERBATIM-BEGIN PM1:✱32·111
✱32·111. ⊢.ŷ(xRy)=R⃖ʻx [*32·101.*30·3]
PM-VERBATIM-END PM1:✱32·111 -/
/- PM-VERBATIM-BEGIN PM1:✱32·12
✱32·12. ⊢.E!R⃗ʻy [*32·11.*14·21]
PM-VERBATIM-END PM1:✱32·12 -/
/- PM-VERBATIM-BEGIN PM1:✱32·121
✱32·121. ⊢.E!R⃖ʻx [*32·111.*14·21]
PM-VERBATIM-END PM1:✱32·121 -/
/- PM-VERBATIM-BEGIN PM1:✱32·132
✱32·132. ⊢:αR⃗y.≡.α=R⃗ʻy.≡.α=x̂(xRy) [*32·1·13.*20·57]
PM-VERBATIM-END PM1:✱32·132 -/
/- PM-VERBATIM-BEGIN PM1:✱32·133
✱32·133. ⊢:βR⃖x.≡.β=R⃖ʻx.≡.β=ŷ(xRy) [*32·101·131.*20·57]
PM-VERBATIM-END PM1:✱32·133 -/
/- PM-VERBATIM-BEGIN PM1:✱32·14
✱32·14. ⊢:R⃗=S⃗.≡.R=S
PM-VERBATIM-END PM1:✱32·14 -/
/- PM-VERBATIM-BEGIN PM1:✱32·15
✱32·15. ⊢:R⃖=S⃖.≡.R=S [Similar proof]
PM-VERBATIM-END PM1:✱32·15 -/
/- PM-VERBATIM-BEGIN PM1:✱32·18
✱32·18. ⊢:x∈ R⃗ʻy.≡.xRy [*32·13.*20·33]
PM-VERBATIM-END PM1:✱32·18 -/
/- PM-VERBATIM-BEGIN PM1:✱32·181
✱32·181. ⊢:y∈ R⃖ʻx.≡.xRy [*32·131.*20·33]
PM-VERBATIM-END PM1:✱32·181 -/
/- PM-VERBATIM-BEGIN PM1:✱32·182
✱32·182. ⊢:x∈ R⃗ʻy.≡.y∈ R⃖ʻx [*32·18·181]
PM-VERBATIM-END PM1:✱32·182 -/
/- PM-VERBATIM-BEGIN PM1:✱32·19
✱32·19. ⊢:R⪽S.⊃.R⃗ʻy⊂S⃗ʻy.R⃖ʻx⊂S⃖ʻx
PM-VERBATIM-END PM1:✱32·19 -/
/- PM-VERBATIM-BEGIN PM1:✱32·2
✱32·2. ⊢:A sg R.≡.A=R⃗ [*21·3.(*32·03)]
PM-VERBATIM-END PM1:✱32·2 -/
/- PM-VERBATIM-BEGIN PM1:✱32·201
✱32·201. ⊢:A gs R.≡.A=R⃖ [*21·3.(*32·04)]
PM-VERBATIM-END PM1:✱32·201 -/
/- PM-VERBATIM-BEGIN PM1:✱32·21
✱32·21. ⊢.R⃗=sgʻR [*32·2.*30·3]
PM-VERBATIM-END PM1:✱32·21 -/
/- PM-VERBATIM-BEGIN PM1:✱32·211
✱32·211. ⊢.R⃖=gsʻR [*32·201.*30·3]
PM-VERBATIM-END PM1:✱32·211 -/
/- PM-VERBATIM-BEGIN PM1:✱32·22
✱32·22. ⊢.E!sgʻR [*32·21.*14·21]
PM-VERBATIM-END PM1:✱32·22 -/
/- PM-VERBATIM-BEGIN PM1:✱32·221
✱32·221. ⊢.E!gsʻR [*32·211.*14·21]
PM-VERBATIM-END PM1:✱32·221 -/
/- PM-VERBATIM-BEGIN PM1:✱32·23
✱32·23. ⊢.sgʻR=R⃗ [*32·21.*21·2·57]
PM-VERBATIM-END PM1:✱32·23 -/
/- PM-VERBATIM-BEGIN PM1:✱32·231
✱32·231. ⊢.gsʻR=R⃖ [*32·211.*21·2·57]
PM-VERBATIM-END PM1:✱32·231 -/
/- PM-VERBATIM-BEGIN PM1:✱32·24
✱32·24. ⊢.sgʻŘ=gsʻR
PM-VERBATIM-END PM1:✱32·24 -/
/- PM-VERBATIM-BEGIN PM1:✱32·241
✱32·241. ⊢.gsʻŘ=sgʻR [Similar proof]
PM-VERBATIM-END PM1:✱32·241 -/
/- PM-VERBATIM-BEGIN PM1:✱32·25
✱32·25. ⊢:A sg R.≡.A=sgʻR [*30·4.*32·22]
PM-VERBATIM-END PM1:✱32·25 -/
/- PM-VERBATIM-BEGIN PM1:✱32·251
✱32·251. ⊢:A gs R.≡.A=gsʻR [*30·4.*32·221]
PM-VERBATIM-END PM1:✱32·251 -/
/- PM-VERBATIM-BEGIN PM1:✱32·3
✱32·3. ⊢.sgʻ(R∩̇S)ʻy=R⃗ʻy∩ S⃗ʻy
PM-VERBATIM-END PM1:✱32·3 -/
/- PM-VERBATIM-BEGIN PM1:✱32·31
✱32·31. ⊢.{gsʻ(R∩̇S)}ʻx=R⃖ʻx∩ R⃖ʻx
PM-VERBATIM-END PM1:✱32·31 -/
/- PM-VERBATIM-BEGIN PM1:✱32·32
✱32·32. ⊢.{sgʻ(R⊍S)}ʻy=R⃗ʻy∪ S⃗ʻy
PM-VERBATIM-END PM1:✱32·32 -/
/- PM-VERBATIM-BEGIN PM1:✱32·33
✱32·33. ⊢.{gsʻ(R⊍S)}ʻx=R⃖ʻx∪ R⃖ʻx
PM-VERBATIM-END PM1:✱32·33 -/
/- PM-VERBATIM-BEGIN PM1:✱32·34
✱32·34. ⊢.{sgʻ(-̇R)}ʻy=-R⃗ʻy
PM-VERBATIM-END PM1:✱32·34 -/
/- PM-VERBATIM-BEGIN PM1:✱32·35
✱32·35. ⊢.{gsʻ(-̇R)}ʻx=-R⃖ʻx
PM-VERBATIM-END PM1:✱32·35 -/
/- PM-VERBATIM-BEGIN PM1:✱32·4
✱32·4. ⊢:. E!Rʻz.≡:∃ !R⃗ʻz:x,y∈ R⃗ʻz.⊃ₓ,y.x=y [*30·21.*32·18]
PM-VERBATIM-END PM1:✱32·4 -/
/- PM-VERBATIM-BEGIN PM1:✱32·41
✱32·41. ⊢:. E!Sʻy.⊃:R⃗ʻy=S⃗ʻy.≡.Rʻy=Sʻy
PM-VERBATIM-END PM1:✱32·41 -/
/- PM-VERBATIM-BEGIN PM1:✱32·42
✱32·42. ⊢:. R⃗ʻy=S⃗ʻy.⊃:E!Rʻy.≡.E!Sʻy [*30·34.*32·18]
PM-VERBATIM-END PM1:✱32·42 -/
