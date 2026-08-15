/-! # ✱71 — One-many, many-one, and one-one relations (Gutenberg 78050). -/
/- PM-VERBATIM-BEGIN PM1:✱71·01
✱71·01. ⊢.1 → Cls=Ř(R⃗ʻʻᗡʻR⊂ 1) [*70·4]
PM-VERBATIM-END PM1:✱71·01 -/
/- PM-VERBATIM-BEGIN PM1:✱71·02
✱71·02. ⊢.Cls → 1=Ř(R⃖ʻʻDʻR⊂ 1) [*70·41]
PM-VERBATIM-END PM1:✱71·02 -/
/- PM-VERBATIM-BEGIN PM1:✱71·03
✱71·03. ⊢.1 → 1=Ř(R⃗ʻʻᗡʻR⊂ 1.R⃖ʻʻDʻR⊂ 1) [*20·2.(*70·01)]
PM-VERBATIM-END PM1:✱71·03 -/
/- PM-VERBATIM-BEGIN PM1:✱71·04
✱71·04. ⊢.1 → 1=(1 → Cls)∩ (Cls → 1) [*70·42]
PM-VERBATIM-END PM1:✱71·04 -/
/- PM-VERBATIM-BEGIN PM1:✱71·1
✱71·1. ⊢:R∈ 1 → Cls.≡.R⃗ʻʻᗡʻR⊂ 1 [*20·33.*71·01]
PM-VERBATIM-END PM1:✱71·1 -/
/- PM-VERBATIM-BEGIN PM1:✱71·101
✱71·101. ⊢:R∈ Cls → 1.≡.R⃖ʻʻDʻR⊂ 1 [*20·33.*71·02]
PM-VERBATIM-END PM1:✱71·101 -/
/- PM-VERBATIM-BEGIN PM1:✱71·102
✱71·102. ⊢:R∈ 1 → 1.≡.R⃗ʻʻᗡʻR⊂ 1.R⃖ʻʻDʻR⊂ 1 [*20·33.*71·03]
PM-VERBATIM-END PM1:✱71·102 -/
/- PM-VERBATIM-BEGIN PM1:✱71·103
✱71·103. ⊢:R∈ 1 → 1.≡.R∈ 1 → Cls.R∈ Cls → 1 [*22·33.*71·04]
PM-VERBATIM-END PM1:✱71·103 -/
/- PM-VERBATIM-BEGIN PM1:✱71·11
✱71·11. ⊢:R∈ 1 → Cls.≡.R⃗ʻʻV⊂ 1∪ ιʻΛ [*70·44]
PM-VERBATIM-END PM1:✱71·11 -/
/- PM-VERBATIM-BEGIN PM1:✱71·111
✱71·111. ⊢:R∈ Cls → 1.≡.R⃖ʻʻV⊂ 1∪ ιʻΛ [*70·441]
PM-VERBATIM-END PM1:✱71·111 -/
/- PM-VERBATIM-BEGIN PM1:✱71·112
✱71·112. ⊢:R∈ 1 → 1.≡.R⃗ʻʻV⊂ 1∪ ιʻΛ.R⃖ʻʻV⊂ 1∪ ιʻΛ [*70·12]
PM-VERBATIM-END PM1:✱71·112 -/
/- PM-VERBATIM-BEGIN PM1:✱71·12
✱71·12. ⊢:R∈ 1 → Cls.≡.(y).R⃗ʻy∈ 1∪ ιʻΛ [*70·45]
PM-VERBATIM-END PM1:✱71·12 -/
/- PM-VERBATIM-BEGIN PM1:✱71·121
✱71·121. ⊢:R∈ Cls → 1.≡.(x).R⃖ʻx∈ 1∪ ιʻΛ [*70·451]
PM-VERBATIM-END PM1:✱71·121 -/
/- PM-VERBATIM-BEGIN PM1:✱71·122
✱71·122. ⊢:. R∈ 1 → 1.≡:(y).R⃗ʻy∈ 1∪ ιʻΛ:(x).R⃖ʻx∈ 1∪ ιʻΛ [*70·13]
PM-VERBATIM-END PM1:✱71·122 -/
/- PM-VERBATIM-BEGIN PM1:✱71·13
✱71·13. ⊢:. R∈ 1 → Cls.≡:(y):R⃗ʻy∈ 1.∨.R⃗ʻy=Λ [*70·46]
PM-VERBATIM-END PM1:✱71·13 -/
/- PM-VERBATIM-BEGIN PM1:✱71·131
✱71·131. ⊢:. R∈ Cls → 1.≡:(x):R⃖ʻx∈ 1.∨.R⃖ʻx=Λ [*70·461]
PM-VERBATIM-END PM1:✱71·131 -/
/- PM-VERBATIM-BEGIN PM1:✱71·132
✱71·132. ⊢:: R∈ 1 → 1.≡:. (y):R⃗ʻy∈ 1.∨.R⃗ʻy=Λ:. (x):R⃖ʻx∈ 1.∨.R⃖ʻx=Λ [*70·14]
PM-VERBATIM-END PM1:✱71·132 -/
/- PM-VERBATIM-BEGIN PM1:✱71·14
✱71·14. ⊢:. R∈ 1 → Cls.≡:∃ !R⃗ʻy.⊃y.R⃗ʻy∈ 1 [*70·47]
PM-VERBATIM-END PM1:✱71·14 -/
/- PM-VERBATIM-BEGIN PM1:✱71·141
✱71·141. ⊢:. R∈ Cls → 1.≡:∃ !R⃖ʻx.⊃ₓ.R⃖ʻx∈ 1 [*70·471]
PM-VERBATIM-END PM1:✱71·141 -/
/- PM-VERBATIM-BEGIN PM1:✱71·142
✱71·142. ⊢:. R∈ 1 → 1.≡:∃ !R⃗ʻy.⊃y.R⃗ʻy∈ 1:∃ !R⃖ʻx.⊃ₓ.R⃖ʻx∈ 1 [*70·15]
PM-VERBATIM-END PM1:✱71·142 -/
/- PM-VERBATIM-BEGIN PM1:✱71·15
✱71·15. ⊢:R∈ 1 → Cls.≡.DʻR⃗⊂ 1∪ ιʻΛ [*70·48]
PM-VERBATIM-END PM1:✱71·15 -/
/- PM-VERBATIM-BEGIN PM1:✱71·151
✱71·151. ⊢:R∈ Cls → 1.≡.DʻR⃖⊂ 1∪ ιʻΛ [*70·481]
PM-VERBATIM-END PM1:✱71·151 -/
/- PM-VERBATIM-BEGIN PM1:✱71·152
✱71·152. ⊢:R∈ 1 → 1.≡.DʻR⃗⊂ 1∪ ιʻΛ.DʻR⃖⊂ 1∪ ιʻΛ [*70·16]
PM-VERBATIM-END PM1:✱71·152 -/
/- PM-VERBATIM-BEGIN PM1:✱71·16
✱71·16. ⊢:R∈ 1 → Cls.≡.E‼RʻʻᗡʻR
PM-VERBATIM-END PM1:✱71·16 -/
/- PM-VERBATIM-BEGIN PM1:✱71·161
✱71·161. ⊢:R∈ Cls → 1.≡.E‼ŘʻʻDʻR
PM-VERBATIM-END PM1:✱71·161 -/
/- PM-VERBATIM-BEGIN PM1:✱71·162
✱71·162. ⊢:R∈ 1 → 1.≡.E‼RʻʻᗡʻR.E‼ŘʻʻDʻR
PM-VERBATIM-END PM1:✱71·162 -/
/- PM-VERBATIM-BEGIN PM1:✱71·163
✱71·163. ⊢:. R∈ 1 → Cls.≡:y∈ ᗡʻR.≡y.E!Rʻy
PM-VERBATIM-END PM1:✱71·163 -/
/- PM-VERBATIM-BEGIN PM1:✱71·164
✱71·164. ⊢:. R∈ Cls → 1.≡:x∈ DʻR.≡ₓ.E!Řʻx
PM-VERBATIM-END PM1:✱71·164 -/
/- PM-VERBATIM-BEGIN PM1:✱71·165
✱71·165. ⊢:. R∈ 1 → 1.≡:y∈ ᗡʻR.≡y.E!Rʻy:x∈ DʻR.≡ₓ.E!Řʻx
PM-VERBATIM-END PM1:✱71·165 -/
/- PM-VERBATIM-BEGIN PM1:✱71·166
✱71·166. ⊢:(y).E!Rʻy.⊃.R∈ 1 → Cls
PM-VERBATIM-END PM1:✱71·166 -/
/- PM-VERBATIM-BEGIN PM1:✱71·167
✱71·167. ⊢:(x).E!Řʻx.⊃.R∈ Cls → 1
PM-VERBATIM-END PM1:✱71·167 -/
/- PM-VERBATIM-BEGIN PM1:✱71·168
✱71·168. ⊢ :. (y) . E ! Rʻy : (x) . E ! Řʻx : ⊃ . R ∈ 1 → 1
PM-VERBATIM-END PM1:✱71·168 -/
/- PM-VERBATIM-BEGIN PM1:✱71·17
✱71·17. ⊢ :. R ∈ 1 → Cls . ≡ : xRz . yRz . ⊃ₓ, y, z . x = y
PM-VERBATIM-END PM1:✱71·17 -/
/- PM-VERBATIM-BEGIN PM1:✱71·171
✱71·171. ⊢ :. R ∈ Cls → 1 . ≡ : xRy . xRz . ⊃ₓ, y, z . y = z
PM-VERBATIM-END PM1:✱71·171 -/
/- PM-VERBATIM-BEGIN PM1:✱71·172
✱71·172. ⊢ :. R ∈ 1 → 1 . ≡ : xRz . yRz . ⊃ₓ, y, z . x = y : xRy . xRz . ⊃ₓ, y, z . y = z
PM-VERBATIM-END PM1:✱71·172 -/
/- PM-VERBATIM-BEGIN PM1:✱71·18
✱71·18. ⊢ :. R ∈ 1 → Cls . ≡ : ∃ ! R⃖ʻx ∩ R⃖ʻy . ⊃ₓ, y . x = y
PM-VERBATIM-END PM1:✱71·18 -/
/- PM-VERBATIM-BEGIN PM1:✱71·181
✱71·181. ⊢ :. R ∈ Cls → 1 . ≡ : ∃ ! R⃗ʻy ∩ R⃗ʻz . ⊃y, z . y = z
PM-VERBATIM-END PM1:✱71·181 -/
/- PM-VERBATIM-BEGIN PM1:✱71·182
✱71·182. ⊢ :: R ∈ 1 → 1 . ≡ :. ∃ ! R⃖ʻx ∩ R⃖ʻy . ∨ . ∃ ! R⃗ʻx ∩ R⃗ʻy : ⊃ₓ, y . x = y
PM-VERBATIM-END PM1:✱71·182 -/
/- PM-VERBATIM-BEGIN PM1:✱71·19
✱71·19. ⊢ : R ∈ 1 → Cls . ≡ . R| Ř = I↾ DʻR
PM-VERBATIM-END PM1:✱71·19 -/
/- PM-VERBATIM-BEGIN PM1:✱71·191
✱71·191. ⊢ : R ∈ Cls → 1 . ≡ . Ř| R = I↾ ᗡʻR
PM-VERBATIM-END PM1:✱71·191 -/
/- PM-VERBATIM-BEGIN PM1:✱71·192
✱71·192. ⊢ : R ∈ 1 → 1 . ≡ . R| Ř = I↾ DʻR . Ř| R = I↾ ᗡʻR
PM-VERBATIM-END PM1:✱71·192 -/
/- PM-VERBATIM-BEGIN PM1:✱71·2
✱71·2. ⊢.Cls → 1=Cnvʻʻ(1 → Cls). 1 → Cls=Cnvʻʻ(Cls → 1).1 → 1=Cnvʻʻ(1 → 1) [*70·22]
PM-VERBATIM-END PM1:✱71·2 -/
/- PM-VERBATIM-BEGIN PM1:✱71·21
✱71·21. ⊢:R∈ 1 → Cls.≡.Ř∈ Cls → 1
PM-VERBATIM-END PM1:✱71·21 -/
/- PM-VERBATIM-BEGIN PM1:✱71·211
✱71·211. ⊢:R∈ Cls → 1.≡.Ř∈ 1 → Cls
PM-VERBATIM-END PM1:✱71·211 -/
/- PM-VERBATIM-BEGIN PM1:✱71·212
✱71·212. ⊢:R∈ 1 → 1.≡.Ř∈ 1 → 1
PM-VERBATIM-END PM1:✱71·212 -/
/- PM-VERBATIM-BEGIN PM1:✱71·22
✱71·22. ⊢:R∈ 1 → Cls.S⪽R.⊃.S∈ 1 → Cls
PM-VERBATIM-END PM1:✱71·22 -/
/- PM-VERBATIM-BEGIN PM1:✱71·221
✱71·221. ⊢:R∈ Cls → 1.S⪽R.⊃.S∈ Cls → 1
PM-VERBATIM-END PM1:✱71·221 -/
/- PM-VERBATIM-BEGIN PM1:✱71·222
✱71·222. ⊢:R∈ 1 → 1.S⪽R.⊃.S∈ 1 → 1
PM-VERBATIM-END PM1:✱71·222 -/
/- PM-VERBATIM-BEGIN PM1:✱71·223
✱71·223. ⊢:R∈ 1 → Cls.⊃.RlʻR⊂ 1 → Cls [*71·22.*61·2]
PM-VERBATIM-END PM1:✱71·223 -/
/- PM-VERBATIM-BEGIN PM1:✱71·224
✱71·224. ⊢:R∈ Cls → 1.⊃.RlʻR⊂ Cls → 1
PM-VERBATIM-END PM1:✱71·224 -/
/- PM-VERBATIM-BEGIN PM1:✱71·225
✱71·225. ⊢:R∈ 1 → 1.⊃.RlʻR⊂ 1 → 1
PM-VERBATIM-END PM1:✱71·225 -/
/- PM-VERBATIM-BEGIN PM1:✱71·23
✱71·23. ⊢:R∈ 1 → Cls.⊃.R∩̇S∈ 1 → Cls [*71·22.*23·43]
PM-VERBATIM-END PM1:✱71·23 -/
/- PM-VERBATIM-BEGIN PM1:✱71·231
✱71·231. ⊢:R∈ Cls → 1.⊃.R∩̇S∈ Cls → 1
PM-VERBATIM-END PM1:✱71·231 -/
/- PM-VERBATIM-BEGIN PM1:✱71·232
✱71·232. ⊢:R∈ 1 → 1.⊃.R∩̇S∈ 1 → 1
PM-VERBATIM-END PM1:✱71·232 -/
/- PM-VERBATIM-BEGIN PM1:✱71·233
✱71·233. ⊢:R, S∈ 1 → Cls.⊃.R∩̇Š∈ 1 → 1
PM-VERBATIM-END PM1:✱71·233 -/
/- PM-VERBATIM-BEGIN PM1:✱71·234
✱71·234. ⊢:R, S∈ Cls → 1.⊃.R∩̇Š∈ 1 → 1
PM-VERBATIM-END PM1:✱71·234 -/
/- PM-VERBATIM-BEGIN PM1:✱71·235
✱71·235. ⊢:R∈ 1 → Cls.S∈ Cls → 1.⊃.R∩̇S∈ 1 → 1
PM-VERBATIM-END PM1:✱71·235 -/
/- PM-VERBATIM-BEGIN PM1:✱71·24
✱71·24. ⊢:R, S∈ 1 → Cls.ᗡʻR∩ ᗡʻS=Λ.⊃.R⊍S∈ 1 → Cls [*70·54]
PM-VERBATIM-END PM1:✱71·24 -/
/- PM-VERBATIM-BEGIN PM1:✱71·241
✱71·241. ⊢:R, S∈ Cls → 1.DʻR∩ DʻS=Λ.⊃.R⊍S∈ Cls → 1 [*70·55]
PM-VERBATIM-END PM1:✱71·241 -/
/- PM-VERBATIM-BEGIN PM1:✱71·242
✱71·242. ⊢:R, S∈ 1 → 1.DʻR∩ DʻS=Λ.ᗡʻR∩ ᗡʻS=Λ.⊃.R⊍S∈ 1 → 1 [*70·56]
PM-VERBATIM-END PM1:✱71·242 -/
/- PM-VERBATIM-BEGIN PM1:✱71·243
✱71·243. ⊢:R, S∈ 1 → 1.CʻR∩ CʻS=Λ.⊃.R⊍S∈ 1 → 1 [*70·57]
PM-VERBATIM-END PM1:✱71·243 -/
/- PM-VERBATIM-BEGIN PM1:✱71·244
✱71·244. ⊢:R, S∈ 1 → Cls.R↾ ᗡʻS⪽S.⊃.R⊍S∈ 1 → Cls
PM-VERBATIM-END PM1:✱71·244 -/
/- PM-VERBATIM-BEGIN PM1:✱71·245
✱71·245. ⊢:R,S∈ Cls → 1.(DʻS)↿ R⪽S.⊃.R⊍S∈ Cls → 1
PM-VERBATIM-END PM1:✱71·245 -/
/- PM-VERBATIM-BEGIN PM1:✱71·25
✱71·25. ⊢:R,S∈ 1 → Cls.⊃.R| S∈ 1 → Cls
PM-VERBATIM-END PM1:✱71·25 -/
/- PM-VERBATIM-BEGIN PM1:✱71·251
✱71·251. ⊢:R, S∈ Cls → 1.⊃.R| S∈ Cls → 1
PM-VERBATIM-END PM1:✱71·251 -/
/- PM-VERBATIM-BEGIN PM1:✱71·252
✱71·252. ⊢:R, S∈ 1 → 1.⊃.R| S∈ 1 → 1
PM-VERBATIM-END PM1:✱71·252 -/
/- PM-VERBATIM-BEGIN PM1:✱71·26
✱71·26. ⊢:R∈ 1 → Cls.⊃.R↾ γ∈ 1 → Cls [*70·62]
PM-VERBATIM-END PM1:✱71·26 -/
/- PM-VERBATIM-BEGIN PM1:✱71·261
✱71·261. ⊢:R∈ Cls → 1.⊃.β↿ R∈ Cls → 1 [*70·63]
PM-VERBATIM-END PM1:✱71·261 -/
/- PM-VERBATIM-BEGIN PM1:✱71·27
✱71·27. ⊢:R∈ 1 → Cls.⊃.β↿ R∈ 1 → Cls [*35·44.*71·22]
PM-VERBATIM-END PM1:✱71·27 -/
/- PM-VERBATIM-BEGIN PM1:✱71·271
✱71·271. ⊢:R∈ Cls → 1.⊃.R↾ γ∈ Cls → 1
PM-VERBATIM-END PM1:✱71·271 -/
/- PM-VERBATIM-BEGIN PM1:✱71·281
✱71·281. ⊢:R∈ Cls → 1.⊃.β↿ R↾ γ∈ Cls → 1
PM-VERBATIM-END PM1:✱71·281 -/
/- PM-VERBATIM-BEGIN PM1:✱71·28
✱71·28. ⊢:R ∈ 1→ Cls.⊃.β↿R↾ γ ∈ 1→ Cls  [✱35·442.✱71·22]
PM-VERBATIM-END PM1:✱71·28 -/
/- PM-VERBATIM-BEGIN PM1:✱71·29
✱71·29. ⊢:R∈ 1 → 1.⊃.β↿ R, R↾ γ,β↿ R↾ γ∈ 1 → 1
PM-VERBATIM-END PM1:✱71·29 -/
/- PM-VERBATIM-BEGIN PM1:✱71·31
✱71·31. ⊢:R∈ 1 → Cls.y∈ ᗡʻR.⊃.(Rʻy)Ry [*30·32.*71·163]
PM-VERBATIM-END PM1:✱71·31 -/
/- PM-VERBATIM-BEGIN PM1:✱71·311
✱71·311. ⊢:R∈ Cls → 1.x∈ DʻR.⊃.xR(Řʻx)
PM-VERBATIM-END PM1:✱71·311 -/
/- PM-VERBATIM-BEGIN PM1:✱71·312
✱71·312. ⊢:R∈ 1 → 1.x∈ DʻR.y∈ ᗡʻR.⊃.xR(Řʻx).(Rʻy)Ry
PM-VERBATIM-END PM1:✱71·312 -/
/- PM-VERBATIM-BEGIN PM1:✱71·32
✱71·32. ⊢:: R∈ 1 → Cls.y∈ ᗡʻR.⊃:. ψ(Rʻy).≡:(∃ x).xRy.ψ x:≡:xRy.⊃ₓ.ψ x [*30·33.*71·163]
PM-VERBATIM-END PM1:✱71·32 -/
/- PM-VERBATIM-BEGIN PM1:✱71·321
✱71·321. ⊢:: R∈ Cls → 1.x∈ DʻR.⊃:. ψ(Řʻx).≡:(∃ y).xRy.ψ y:≡:xRy.⊃y.ψ y
PM-VERBATIM-END PM1:✱71·321 -/
/- PM-VERBATIM-BEGIN PM1:✱71·33
✱71·33. ⊢:: R∈ 1 → Cls.⊃:. ψ(Rʻy):≡:(∃ x).xRy.ψ x:≡:y∈ ᗡʻR:xRy.⊃ₓ.ψ x
PM-VERBATIM-END PM1:✱71·33 -/
/- PM-VERBATIM-BEGIN PM1:✱71·331
✱71·331. ⊢:: R∈ Cls → 1.⊃:. ψ(Řʻx).≡:(∃ y). xRy.ψ y:≡: x∈ DʻR:xRy.⊃y.ψ y
PM-VERBATIM-END PM1:✱71·331 -/
/- PM-VERBATIM-BEGIN PM1:✱71·332
✱71·332. ⊢:. R∈ 1 → Cls.⊃:Rʻy∈ α.≡.∃ !R⃗ʻy∩ α.≡.y∈ ᗡʻR.R⃗ʻy⊂ α [*71·33 x∈ α/ψ x ]
PM-VERBATIM-END PM1:✱71·332 -/
/- PM-VERBATIM-BEGIN PM1:✱71·333
✱71·333. ⊢:. R∈ Cls → 1.⊃:Řʻx∈ α.≡.∃ !R⃖ʻx∩ α.≡.x∈ DʻR.R⃖ʻx⊂ α
PM-VERBATIM-END PM1:✱71·333 -/
/- PM-VERBATIM-BEGIN PM1:✱71·34
✱71·34. ⊢:R∈ 1 → Cls.R=S.y∈ ᗡʻR.⊃.Rʻy=Sʻy [*30·36.*71·163]
PM-VERBATIM-END PM1:✱71·34 -/
/- PM-VERBATIM-BEGIN PM1:✱71·341
✱71·341. ⊢:R∈ Cls → 1.R=S.x∈ DʻR.⊃.Řʻx=Šʻx
PM-VERBATIM-END PM1:✱71·341 -/
/- PM-VERBATIM-BEGIN PM1:✱71·35
✱71·35. ⊢:: R∈ 1 → Cls.⊃:. y∈ ᗡʻR∪ ᗡʻS.⊃y.Rʻy=Sʻy:≡.R=S
PM-VERBATIM-END PM1:✱71·35 -/
/- PM-VERBATIM-BEGIN PM1:✱71·351
✱71·351. ⊢:: R∈ Cls → 1.⊃:. x∈ DʻR∪ DʻS.⊃ₓ.Řʻx=Šʻx:≡.R=S
PM-VERBATIM-END PM1:✱71·351 -/
/- PM-VERBATIM-BEGIN PM1:✱71·352
✱71·352. ⊢:: R∈ 1 → 1.⊃:. y∈ ᗡʻR∪ ᗡʻS. ⊃y.Rʻy=Sʻy:≡:R=S: ≡:x∈ DʻR∪ DʻS.⊃ₓ.Řʻx=Šʻx
PM-VERBATIM-END PM1:✱71·352 -/
/- PM-VERBATIM-BEGIN PM1:✱71·36
✱71·36. ⊢:. R∈ 1 → Cls.⊃:x=Rʻy.≡.xRy
PM-VERBATIM-END PM1:✱71·36 -/
/- PM-VERBATIM-BEGIN PM1:✱71·361
✱71·361. ⊢:. R∈ Cls → 1.⊃:y=Řʻx.≡.xRy
PM-VERBATIM-END PM1:✱71·361 -/
/- PM-VERBATIM-BEGIN PM1:✱71·362
✱71·362. ⊢:. R∈ 1 → 1.⊃:x=Rʻy.≡.xRy.≡.y=Řʻx
PM-VERBATIM-END PM1:✱71·362 -/
/- PM-VERBATIM-BEGIN PM1:✱71·37
✱71·37. ⊢:. R∈ 1 → Cls.⊃:y∈ Řʻʻα.≡.Rʻy∈ α
PM-VERBATIM-END PM1:✱71·37 -/
/- PM-VERBATIM-BEGIN PM1:✱71·371
✱71·371. ⊢:. R∈ Cls → 1.⊃:x∈ Rʻʻα.≡.Řʻx∈ α
PM-VERBATIM-END PM1:✱71·371 -/
/- PM-VERBATIM-BEGIN PM1:✱71·38
✱71·38. ⊢:R∈ 1 → Cls.⊃.Řʻʻ(α-β)=Řʻʻα-Řʻʻβ
PM-VERBATIM-END PM1:✱71·38 -/
/- PM-VERBATIM-BEGIN PM1:✱71·381
✱71·381. ⊢:R∈ Cls → 1.⊃.Rʻʻ(α-β)=Rʻʻα-Rʻʻβ
PM-VERBATIM-END PM1:✱71·381 -/
/- PM-VERBATIM-BEGIN PM1:✱71·4
✱71·4. ⊢:R∈ 1 → Cls.⊃.Rʻʻβ=x̂{(∃ y).y∈ β.x=Rʻy} [*37·1.*71·36]
PM-VERBATIM-END PM1:✱71·4 -/
/- PM-VERBATIM-BEGIN PM1:✱71·401
✱71·401. ⊢:R∈ Cls → 1.⊃.Řʻʻβ=ŷ{(∃ x).x∈ β.y=Řʻx}
PM-VERBATIM-END PM1:✱71·401 -/
/- PM-VERBATIM-BEGIN PM1:✱71·41
✱71·41. ⊢:R∈ 1 → Cls.⊃.DʻR=x̂(∃ y).x=Rʻy [*33·11.*71·36]
PM-VERBATIM-END PM1:✱71·41 -/
/- PM-VERBATIM-BEGIN PM1:✱71·411
✱71·411. ⊢:R∈ Cls → 1.⊃.ᗡʻR=ŷ{(∃ x).y=Řʻx}
PM-VERBATIM-END PM1:✱71·411 -/
/- PM-VERBATIM-BEGIN PM1:✱71·42
✱71·42. ⊢:: R∈ 1 → Cls.β⊂ ᗡʻR.⊃:. Rʻʻβ⊂ α.≡:y∈ β.⊃y.Rʻy∈ α [*37·61.*71·16]
PM-VERBATIM-END PM1:✱71·42 -/
/- PM-VERBATIM-BEGIN PM1:✱71·421
✱71·421. ⊢:: R∈ Cls → 1.α⊂ DʻR.⊃:. Řʻʻα⊂ β.≡:x∈ α.⊃ₓ.Řʻx∈ β
PM-VERBATIM-END PM1:✱71·421 -/
/- PM-VERBATIM-BEGIN PM1:✱71·43
✱71·43. ⊢:R∈ 1 → Cls.y∈ α∩ ᗡʻR.⊃.Rʻy∈ Rʻʻα [*37·62.*71·16]
PM-VERBATIM-END PM1:✱71·43 -/
/- PM-VERBATIM-BEGIN PM1:✱71·431
✱71·431. ⊢:R∈ Cls → 1.x∈ α∩ DʻR.⊃.Řʻx∈ Řʻʻα
PM-VERBATIM-END PM1:✱71·431 -/
/- PM-VERBATIM-BEGIN PM1:✱71·44
✱71·44. ⊢:: R∈ 1 → Cls.α⊂ ᗡʻR.⊃:. x∈ Rʻʻα.⊃ₓ.ψ x:≡:y∈ α.⊃y.ψ(Rʻy) [*37·63.*71·16]
PM-VERBATIM-END PM1:✱71·44 -/
/- PM-VERBATIM-BEGIN PM1:✱71·441
✱71·441. ⊢:: R∈ Cls → 1.α⊂ DʻR.⊃:. y∈ Řʻʻα.⊃y.ψ y:≡:x∈ α.⊃ₓ.ψ(Řʻx)
PM-VERBATIM-END PM1:✱71·441 -/
/- PM-VERBATIM-BEGIN PM1:✱71·45
✱71·45. ⊢:. R∈ 1 → Cls.⊃:(∃ x).x∈ Rʻʻα.ψ x.≡.(∃ y).y∈ α.ψ(Rʻy)
PM-VERBATIM-END PM1:✱71·45 -/
/- PM-VERBATIM-BEGIN PM1:✱71·451
✱71·451. ⊢:. R∈ Cls → 1.⊃:(∃ y).y∈ Řʻʻα.ψ y.≡.(∃ x).x∈ α.ψ(Řʻx)
PM-VERBATIM-END PM1:✱71·451 -/
/- PM-VERBATIM-BEGIN PM1:✱71·46
✱71·46. ⊢:R∈ 1 → Cls.α⊂ Rʻʻβ.⊃.α=Rʻʻ(Řʻʻα∩ β)
PM-VERBATIM-END PM1:✱71·46 -/
/- PM-VERBATIM-BEGIN PM1:✱71·461
✱71·461. ⊢:R∈ Cls → 1.β⊂ Řʻʻα.⊃.β=Řʻʻ(Rʻʻβ∩ α)
PM-VERBATIM-END PM1:✱71·461 -/
/- PM-VERBATIM-BEGIN PM1:✱71·47
✱71·47. ⊢:. R∈ 1 → Cls.⊃:α⊂ Rʻʻβ.≡.(∃ γ).γ⊂ β.α=Rʻʻγ
PM-VERBATIM-END PM1:✱71·47 -/
/- PM-VERBATIM-BEGIN PM1:✱71·471
✱71·471. ⊢:. R∈ Cls → 1.⊃:β⊂ Řʻʻα.≡.(∃ γ).γ⊂ α.β=Řʻʻγ
PM-VERBATIM-END PM1:✱71·471 -/
/- PM-VERBATIM-BEGIN PM1:✱71·48
✱71·48. ⊢:R∈ 1 → Cls.⊃.DʻR_∈=ClʻDʻR
PM-VERBATIM-END PM1:✱71·48 -/
/- PM-VERBATIM-BEGIN PM1:✱71·481
✱71·481. ⊢:R∈ Cls → 1.⊃.Dʻ(Ř)_∈=ClʻᗡʻR
PM-VERBATIM-END PM1:✱71·481 -/
/- PM-VERBATIM-BEGIN PM1:✱71·49
✱71·49. ⊢:R∈ 1 → Cls.α⊂ ᗡʻR.⊃.RʻʻʻClʻα=ClʻRʻʻα.RʻʻʻCl exʻα=Cl exʻRʻʻα
PM-VERBATIM-END PM1:✱71·49 -/
/- PM-VERBATIM-BEGIN PM1:✱71·491
✱71·491. ⊢:R∈ Cls → 1.α⊂ DʻR.⊃.ŘʻʻʻClʻα=ClʻŘʻʻα.ŘʻʻʻCl exʻα=Cl exʻŘʻʻα
PM-VERBATIM-END PM1:✱71·491 -/
/- PM-VERBATIM-BEGIN PM1:✱71·5
✱71·5. ⊢:. R∈ 1 → Cls.⊃:xRy.≡.x=ι̌ʻR⃗ʻy
PM-VERBATIM-END PM1:✱71·5 -/
/- PM-VERBATIM-BEGIN PM1:✱71·501
✱71·501. ⊢:. R∈ Cls → 1.⊃:xRy.≡.y=ι̌ʻR⃖ʻx
PM-VERBATIM-END PM1:✱71·501 -/
/- PM-VERBATIM-BEGIN PM1:✱71·51
✱71·51. ⊢:R∈ 1 → Cls.y∈ ᗡʻR.⊃.Rʻy=ι̌ʻR⃗ʻy
PM-VERBATIM-END PM1:✱71·51 -/
/- PM-VERBATIM-BEGIN PM1:✱71·511
✱71·511. ⊢:R∈ Cls → 1.x∈ DʻR.⊃.Řʻx=ι̌ʻR⃖ʻx
PM-VERBATIM-END PM1:✱71·511 -/
/- PM-VERBATIM-BEGIN PM1:✱71·52
✱71·52. ⊢:R∈ 1 → Cls.⊃.Rʻʻα=ι̌ʻʻR⃗ʻʻα
PM-VERBATIM-END PM1:✱71·52 -/
/- PM-VERBATIM-BEGIN PM1:✱71·521
✱71·521. ⊢:R∈ Cls → 1.⊃.Řʻʻα=ι̌ʻʻR⃖ʻʻα
PM-VERBATIM-END PM1:✱71·521 -/
/- PM-VERBATIM-BEGIN PM1:✱71·53
✱71·53. ⊢:R∈ 1 → Cls.Řʻx=Řʻy.⊃.x=y
PM-VERBATIM-END PM1:✱71·53 -/
/- PM-VERBATIM-BEGIN PM1:✱71·531
✱71·531. ⊢:R∈ Cls → 1.Rʻy=Rʻz.⊃.y=z
PM-VERBATIM-END PM1:✱71·531 -/
/- PM-VERBATIM-BEGIN PM1:✱71·532
✱71·532. ⊢:. R∈ 1 → 1.⊃:Rʻy=Rʻz.⊃.y=z:Řʻx=Řʻy.⊃.x=y
PM-VERBATIM-END PM1:✱71·532 -/
/- PM-VERBATIM-BEGIN PM1:✱71·54
✱71·54. ⊢:: R∈ 1 → Cls.⊃:. R∈ 1 → 1.≡:Rʻy=Rʻz.⊃y,z.y=z
PM-VERBATIM-END PM1:✱71·54 -/
/- PM-VERBATIM-BEGIN PM1:✱71·55
✱71·55. ⊢:: R∈ 1 → Cls.⊃:. R↾ β∈ 1 → 1.≡:y,z∈ β.Rʻy=Rʻz.⊃y,z.y=z
PM-VERBATIM-END PM1:✱71·55 -/
/- PM-VERBATIM-BEGIN PM1:✱71·56
✱71·56. ⊢:. R∈ 1 → 1.y∈ ᗡʻR.⊃:Rʻy=Rʻz.≡.y=z
PM-VERBATIM-END PM1:✱71·56 -/
/- PM-VERBATIM-BEGIN PM1:✱71·561
✱71·561. ⊢:. R∈ 1 → 1.x∈ DʻR.⊃:Řʻx=Řʻy.≡.x=y
PM-VERBATIM-END PM1:✱71·561 -/
/- PM-VERBATIM-BEGIN PM1:✱71·57
✱71·57. ⊢:. Rʻy=Rʻz.≡y,z.y=z:≡:R∈ 1 → 1:(y).E!Rʻy
PM-VERBATIM-END PM1:✱71·57 -/
/- PM-VERBATIM-BEGIN PM1:✱71·571
✱71·571. ⊢:. y∈ β.⊃y.E!Rʻy:≡.R↾ β∈ 1 → Cls.β⊂ ᗡʻR
PM-VERBATIM-END PM1:✱71·571 -/
/- PM-VERBATIM-BEGIN PM1:✱71·572
✱71·572. ⊢:. y∈ β∩ ᗡʻR.⊃y.E!Rʻy:≡.R↾ β∈ 1 → Cls [*71·571.*35·351.*22·43]
PM-VERBATIM-END PM1:✱71·572 -/
/- PM-VERBATIM-BEGIN PM1:✱71·58
✱71·58. ⊢:: y, z∈ β.⊃y,z:Rʻy=Rʻz.≡.y=z:. ⊃.R↾ β∈ 1 → 1.β⊂ ᗡʻR
PM-VERBATIM-END PM1:✱71·58 -/
/- PM-VERBATIM-BEGIN PM1:✱71·59
✱71·59. ⊢:: y,z∈ β.⊃y,z:Rʻy=Rʻz.≡.y=z:. ≡.R↾ β∈ 1 → 1.β⊂ ᗡʻR
PM-VERBATIM-END PM1:✱71·59 -/
/- PM-VERBATIM-BEGIN PM1:✱71·6
✱71·6. ⊢:R∈ 1 → Cls.⊃.R=ṡʻP̂{(∃ y).y∈ ᗡʻR.P=(Rʻy)↓ y}
PM-VERBATIM-END PM1:✱71·6 -/
/- PM-VERBATIM-BEGIN PM1:✱71·61
✱71·61. ⊢:T∈ 1 → Cls.⊃.QʻʻʻT⃗ʻʻ(ᗡʻT∩ α)=Q⃗ʻʻTʻʻα
PM-VERBATIM-END PM1:✱71·61 -/
/- PM-VERBATIM-BEGIN PM1:✱71·611
✱71·611. ⊢:T∈ Cls → 1.⊃.QʻʻʻT⃖ʻʻ(DʻT∩ α)=Q⃗ʻʻŤʻʻα
PM-VERBATIM-END PM1:✱71·611 -/
/- PM-VERBATIM-BEGIN PM1:✱71·612
✱71·612. ⊢:T∈ 1 → Cls.⊃.Q̌ʻʻʻT⃗ʻʻ(ᗡʻT∩ α)=Q⃖ʻʻTʻʻα
PM-VERBATIM-END PM1:✱71·612 -/
/- PM-VERBATIM-BEGIN PM1:✱71·613
✱71·613. ⊢:T∈ Cls → 1.⊃.Q̌ʻʻʻT⃖ʻʻ(DʻT∩ α)=Q⃖ʻʻŤʻʻα
PM-VERBATIM-END PM1:✱71·613 -/
/- PM-VERBATIM-BEGIN PM1:✱71·7
✱71·7. ⊢:. Q∈ 1 → Cls.⊃:xP| Qz.≡.xP(Qʻz)
PM-VERBATIM-END PM1:✱71·7 -/
/- PM-VERBATIM-BEGIN PM1:✱71·701
✱71·701. ⊢:. Q∈ Cls → 1.⊃:xQ| Pz.≡.(Q̌ʻx)Pz
PM-VERBATIM-END PM1:✱71·701 -/
