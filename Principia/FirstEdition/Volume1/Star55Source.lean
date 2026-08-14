/-! PM I, ✱55·01–✱55·201. Source: Project Gutenberg ebook 78050. -/
/- PM-VERBATIM-BEGIN PM1:✱55·01
✱55·01. x↓y = ιʻx ↑ ιʻy  Df
PM-VERBATIM-END PM1:✱55·01 -/
/- PM-VERBATIM-BEGIN PM1:✱55·02
✱55·02. Rʻx↓y = Rʻ(x↓y)  Df
PM-VERBATIM-END PM1:✱55·02 -/
/- PM-VERBATIM-BEGIN PM1:✱55·1
✱55·1. ⊢ . x↓y = ιʻx ↑ ιʻy
PM-VERBATIM-END PM1:✱55·1 -/
/- PM-VERBATIM-BEGIN PM1:✱55·11
✱55·11. ⊢ . x↓ʻy = ↓ιʻx = x↓y = ιʻx ↑ ιʻy
PM-VERBATIM-END PM1:✱55·11 -/
/- PM-VERBATIM-BEGIN PM1:✱55·12
✱55·12. ⊢ . E!x↓ʻy
PM-VERBATIM-END PM1:✱55·12 -/
/- PM-VERBATIM-BEGIN PM1:✱55·121
✱55·121. ⊢ . E!x↓yʻx
PM-VERBATIM-END PM1:✱55·121 -/
/- PM-VERBATIM-BEGIN PM1:✱55·123
✱55·123. ⊢ : R(↓y)x .≡. R = x↓y
PM-VERBATIM-END PM1:✱55·123 -/
/- PM-VERBATIM-BEGIN PM1:✱55·132
✱55·132. ⊢ . x(x↓y)y
PM-VERBATIM-END PM1:✱55·132 -/
/- PM-VERBATIM-BEGIN PM1:✱55·134
✱55·134. ⊢ . ∃̇!(x↓y)
PM-VERBATIM-END PM1:✱55·134 -/
/- PM-VERBATIM-BEGIN PM1:✱55·14
✱55·14. ⊢ . x↓y = Cnvʻy↓x
PM-VERBATIM-END PM1:✱55·14 -/
/- PM-VERBATIM-BEGIN PM1:✱55·15
✱55·15. ⊢ . Dʻx↓y = ιʻx . ᗡʻx↓y = ιʻy . Cʻx↓y = ιʻx ∪ ιʻy
PM-VERBATIM-END PM1:✱55·15 -/
/- PM-VERBATIM-BEGIN PM1:✱55·16
✱55·16. ⊢ : DʻR = ιʻx . ᗡʻR = ιʻy .≡. R = x↓y
Dem.
⊢.*33·13·131.*51·15.⊃
⊢::Dʻ R=ιʻ x.ᗡʻ R=ιʻ y. ≡:.(∃ w).zRw.≡z.z=x:(∃ z).zRw.≡w.w=y:.
[*14·122] ≡:.(∃ z,w).zRw:(∃ w).zRw.⊃z.z=x:
(∃ w,z).zRw:(∃ z).zRw.⊃w.w=y:.
[*11·23.*4·71] ≡:.(∃ z,w).zRw:(∃ w).zRw.⊃z.z=x:(∃ z).zRw.⊃w.w=y:.
[*10·23] ≡:.(∃ z,w).zRw:zRw.⊃z,w.z=x:zRw.⊃z,w.w=y:.
[*11·391] ≡:.(∃ z,w).zRw:zRw.⊃z,w.z=x.w=y:.
[*14·123] ≡:. zRw.≡z,w.z=x.w=y:.
[*55·13] ≡:. zRw.≡z,w.z(x↓ y)w:.
[*21·43] ≡:. R=x↓ y::⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·16 -/
/- PM-VERBATIM-BEGIN PM1:✱55·161
✱55·161. ⊢ . x↓y = ι̌ʻ R̂(DʻR = ιʻx . ᗡʻR = ιʻy)
Dem.
⊢.*55·16.*20·15.⊃
⊢.R̂(Dʻ R=ιʻ x.ᗡʻR=ιʻ y) =R̂(R=x↓ y)
[*51·11] =ιʻ (x↓ y) (1)
⊢.(1).*51·51.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·161 -/
/- PM-VERBATIM-BEGIN PM1:✱55·17
✱55·17. ⊢ . x↓y = ι̌ʻ(←Dʻιʻx ∩ ←ᗡʻιʻy)
PM-VERBATIM-END PM1:✱55·17 -/
/- PM-VERBATIM-BEGIN PM1:✱55·2
✱55·2. ⊢ : x↓y = x↓z .≡. y = z
Dem.
⊢.*30·37.*55·11·12.⊃⊢:y=z.⊃.x↓ y=x↓ z (1)
⊢.*30·37.*33·121.⊃
⊢:x↓ y=x↓ z.⊃.ᗡʻ x↓ y=ᗡʻ x↓ z.
[*55·15] ⊃.ιʻ y=ιʻ z.
[*51·23] ⊃.y=z (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·2 -/
/- PM-VERBATIM-BEGIN PM1:✱55·201
✱55·201. ⊢ : x↓z = y↓z .≡. x = y
PM-VERBATIM-END PM1:✱55·201 -/
/- PM-VERBATIM-BEGIN PM1:✱55·202
✱55·202. ⊢ : x↓y = z↓w .≡. x=z . y=w .≡. y↓x = w↓z
Dem.
⊢.*55·2·201.⊃
⊢:x=z.y=w. ⊃.x↓ y=z↓ y.z↓ y=z↓ w.
[*13·17] ⊃.x↓ y=z↓ w (1)
⊢.*30·37.*33·12·121.⊃
⊢:x↓ y=z↓ w. ⊃.Dʻx↓ y=Dʻz↓ w.ᗡʻx↓ y=ᗡʻz↓ w.
[*55·15] ⊃.ιʻ x=ιʻ z.ιʻ y=ιʻ w.
[*51·23] ⊃.x=z.y=w (2)
⊢.(1).(2).⊃
⊢:x↓ y=z↓ w.≡.x=z.y=w (3)
Similarly
⊢:y↓ x=w↓ z.≡.x=z.y=w (4)
⊢.(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·202 -/
/- PM-VERBATIM-BEGIN PM1:✱55·21
✱55·21. ⊢ . ᗡʻx↓ = V . ᗡʻ↓x = V
PM-VERBATIM-END PM1:✱55·21 -/
/- PM-VERBATIM-BEGIN PM1:✱55·22
✱55·22. ⊢ . Dʻx↓ = Ř{(∃y).R=x↓y}
PM-VERBATIM-END PM1:✱55·22 -/
/- PM-VERBATIM-BEGIN PM1:✱55·221
✱55·221. ⊢ . Dʻ↓x = Ř{(∃y).R=y↓x}
PM-VERBATIM-END PM1:✱55·221 -/
/- PM-VERBATIM-BEGIN PM1:✱55·222
✱55·222. ⊢ : R∈Dʻx↓ .≡. DʻR=ιʻx . ᗡʻR∈1
Dem.
⊢.*55·22·16.⊃⊢:. R∈Dʻ x↓. ≡:(∃ y).DʻR=ιʻ x.ᗡʻ R=ιʻ y:
[*10·35] ≡:Dʻ R=ιʻ x:(∃ y).ᗡʻ R=ιʻ y:
[*52·1] ≡:Dʻ R=ιʻ x.ᗡʻ R∈ 1:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·222 -/
/- PM-VERBATIM-BEGIN PM1:✱55·223
✱55·223. ⊢ : R∈Dʻ↓x .≡. ᗡʻR=ιʻx . DʻR∈1
[Proof as in ✱55·222]
PM-VERBATIM-END PM1:✱55·223 -/
/- PM-VERBATIM-BEGIN PM1:✱55·224
✱55·224. ⊢ . Dʻx↓ ∩ Dʻ↓y = ιʻ(x↓y)
Dem.
⊢.*55·222·223.⊃
⊢:R∈Dʻ x↓∩ Dʻ ↓ y. ≡.DʻR=ιʻ x.ᗡʻ R∈ 1.ᗡʻ R=ιʻ y.DʻR∈ 1.
[*52·22.*4·71] ≡.DʻR=ιʻx.ᗡʻR=ιʻ y.
[*55·16] ≡.R=x↓ y.
[*51·15] ≡.R∈ιʻ(x↓ y):⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·224 -/
/- PM-VERBATIM-BEGIN PM1:✱55·23
✱55·23. ⊢ . x↓ ʻʻα = R̂{(∃y).y∈α . R=x↓y}
PM-VERBATIM-END PM1:✱55·23 -/
/- PM-VERBATIM-BEGIN PM1:✱55·231
✱55·231. ⊢ . ↓x ʻʻα = R̂{(∃y).y∈α . R=y↓x}
PM-VERBATIM-END PM1:✱55·231 -/
/- PM-VERBATIM-BEGIN PM1:✱55·232
✱55·232. ⊢ : ∃! ↓x ʻʻα ∩ ↓y ʻʻβ .≡. x=y . ∃! α∩β
Dem.
⊢.*55·231.*11·55.⊃
⊢:.∃ !↓ xʻʻα∩ ↓ yʻʻ β. ≡:(∃ R):(∃ z,w).z∈α.R=z↓ x.w∈β.R=w↓ y:
[*13·195] ≡:(∃ z,w).z∈α.w∈β.z↓ x=w↓ y:
[*55·202] ≡:(∃ z,w).z∈α.w∈β.x=y.z=w:
[*13·195] ≡:(∃ z).z∈α∩β.x=y:
[*10·35] ≡:∃ !α∩ β.x=y:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·232 -/
/- PM-VERBATIM-BEGIN PM1:✱55·233
✱55·233. ⊢ : x≠y .⊃. ↓x ʻʻα ∩ ↓y ʻʻβ = Λ
PM-VERBATIM-END PM1:✱55·233 -/
/- PM-VERBATIM-BEGIN PM1:✱55·24
✱55·24. ⊢ . ṡʻx↓ ʻʻα = ιʻx ↑ α
Dem.
⊢.*41·11.⊃
⊢:. z(ṡʻ x↓ ʻʻα)w. ≡.(∃ R).R∈ x↓ ʻʻα.zRw.
[*55·23] ≡.(∃ R,y).y∈α.R=x↓ y.zRw.
[*13·195] ≡.(∃ y).y∈α.z(x↓ y)w.
[*55·13] ≡.(∃ y).y∈α.z=x.w=y.
[*13·195] ≡.z=x.w∈α.
[*51·15.*35·103] ≡.z(ιʻ x↑α)w:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·24 -/
/- PM-VERBATIM-BEGIN PM1:✱55·241
✱55·241. ⊢ . ṡʻ↓x ʻʻα = α ↑ ιʻx
[Proof as in ✱55·24]
PM-VERBATIM-END PM1:✱55·241 -/
/- PM-VERBATIM-BEGIN PM1:✱55·25
✱55·25. ⊢ : ∃!α .⊃. Dʻʻx↓ ʻʻα = ιʻιʻx
Dem.
⊢.*37·67.*33·12.*55·12.⊃
⊢:β∈Dʻʻx↓ ʻʻ α. ≡.(∃ y).y∈α.β=Dʻx↓ y.
[*55·15] ≡.(∃ y).y∈α.β=ιʻx.
[*10·35] ≡.∃ !α.β=ιʻx (1)
⊢.(1).⊃⊢:.Hp.⊃:β∈Dʻʻ x↓ ʻʻα. ≡.β=ιʻx.
[*51·15] ≡.β∈ιʻιʻx:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·25 -/
/- PM-VERBATIM-BEGIN PM1:✱55·251
✱55·251. ⊢ : ∃!α .⊃. ᗡʻʻ↓x ʻʻα = ιʻιʻx
[Proof as in ✱55·25]
PM-VERBATIM-END PM1:✱55·251 -/
/- PM-VERBATIM-BEGIN PM1:✱55·26
✱55·26. ⊢ . ᗡʻʻx↓ ʻʻα = ιʻʻα
PM-VERBATIM-END PM1:✱55·26 -/
/- PM-VERBATIM-BEGIN PM1:✱55·261
✱55·261. ⊢ . Dʻʻ↓x ʻʻα = ιʻʻα
PM-VERBATIM-END PM1:✱55·261 -/
/- PM-VERBATIM-BEGIN PM1:✱55·262
✱55·262. ⊢ . ↓x ʻʻα = ↓y ʻʻβ .⊃. α=β
PM-VERBATIM-END PM1:✱55·262 -/
/- PM-VERBATIM-BEGIN PM1:✱55·27
✱55·27. ⊢ . Cʻʻ↓x ʻʻα = Cʻʻx↓ ʻʻα = β̂{(∃y).y∈α . β=ιʻx∪ιʻy}
PM-VERBATIM-END PM1:✱55·27 -/
/- PM-VERBATIM-BEGIN PM1:✱55·28
✱55·28. ⊢ . ᗡʻx↓y=ᗡʻx↓z .≡. y=z .≡. x↓y=x↓z
PM-VERBATIM-END PM1:✱55·28 -/
/- PM-VERBATIM-BEGIN PM1:✱55·281
✱55·281. ⊢ . Dʻy↓x=Dʻz↓x .≡. y=z .≡. y↓x=z↓x
PM-VERBATIM-END PM1:✱55·281 -/
/- PM-VERBATIM-BEGIN PM1:✱55·282
✱55·282. ⊢ . Cʻx↓y=Cʻx↓z .≡. y=z .≡. x↓y=x↓z
PM-VERBATIM-END PM1:✱55·282 -/
/- PM-VERBATIM-BEGIN PM1:✱55·283
✱55·283. ⊢ . Cʻy↓x=Cʻz↓x .≡. y=z .≡. y↓x=z↓x
PM-VERBATIM-END PM1:✱55·283 -/
/- PM-VERBATIM-BEGIN PM1:✱55·29
✱55·29. ⊢ . ᗡ|(x↓)=ι
PM-VERBATIM-END PM1:✱55·29 -/
/- PM-VERBATIM-BEGIN PM1:✱55·291
✱55·291. ⊢ . D|(↓x)=ι
PM-VERBATIM-END PM1:✱55·291 -/
/- PM-VERBATIM-BEGIN PM1:✱55·292
✱55·292. ⊢ . C|(x↓)=C|(↓x)=α̂ŷ(α=ιʻx∪ιʻy)
PM-VERBATIM-END PM1:✱55·292 -/
/- PM-VERBATIM-BEGIN PM1:✱55·3
✱55·3. ⊢ : xRy .≡. x↓y ⊂̇ R .≡. ∃̇!(x↓y) ⊍ R
PM-VERBATIM-END PM1:✱55·3 -/
/- PM-VERBATIM-BEGIN PM1:✱55·31
✱55·31. ⊢ : x↓y=z↓w .≡. z(x↓y)w .≡. x(z↓w)y .≡. x=z . y=w
Dem.
⊢.*55·16.⊃⊢:x↓ y=z↓ w. ≡.Dʻx↓ y=ιʻz.ᗡʻx↓ y=ιʻw.
[*55·15] ≡.ιʻx=ιʻz.ιʻy=ιʻw.
[*51·23] ≡.x=z.y=w. (1)
[*55·13] ≡.x(z↓ w)y. (2)
[(1).*13·16] ≡.z=x.w=y.
[*55·13] ≡.z(x↓ y)w (3)
⊢.(1).(2).(3).⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·31 -/
/- PM-VERBATIM-BEGIN PM1:✱55·32
✱55·32. ⊢ : x↓y ∩̇ z↓w=Λ̇ .≡. x≠z .∨. y≠w
Dem.
⊢.*55·3.⊃⊢:∃̇!x↓ y∩̇z↓ w. ≡.x(z↓ w)y.
[*55·13] ≡.x=z.y=w (1)
⊢.(1).Transp.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·32 -/
/- PM-VERBATIM-BEGIN PM1:✱55·33
✱55·33. ⊢ : xRy .≡. x↓y ∩̇ R=x↓y
PM-VERBATIM-END PM1:✱55·33 -/
/- PM-VERBATIM-BEGIN PM1:✱55·34
✱55·34. ⊢ : ∃̇!R . R⊂̇x↓y .≡. R=x↓y
Dem.
⊢.*55·13.⊃⊢:. ∃̇!R.R⊂̇x↓ y. ≡:(∃ z,w).zRw:zRw.⊃z,w.z=x.w=y:
[*14·123] ≡:zRw.≡z,w.z=x.w=y:
[*55·13] ≡:zRw.≡z,w.z(x↓ y)w:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·34 -/
/- PM-VERBATIM-BEGIN PM1:✱55·341
✱55·341. ⊢ : R⊂̇x↓y .≡. R=Λ̇ .∨. R=x↓y
Dem.
⊢.*4·42.⊃:. R⊂̇x↓ y. ≡:R⊂̇x↓ y.R=Λ̇.∨.R⊂̇x↓ y.R≠Λ̇:
[*25·54] ≡:R⊂̇x↓ y.R=Λ.∨.R⊂̇x↓ y.∃̇!R:
[*55·34] ≡:R⊂̇x↓ y.R=Λ̇.∨.R=x↓ y:
[*25·12] ≡:R=Λ̇.∨.R=x↓ y:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·341 -/
/- PM-VERBATIM-BEGIN PM1:✱55·35
✱55·35. ⊢ : R∩̇x↓y=Λ . R⊍x↓y=S .≡. xSy . R=S−̇x↓y
Dem.
⊢.*25·47.⊃
⊢:R∩̇x↓ y=Λ̇.R⊍x↓ y=S. ≡.x↓ y⊂̇S.R=S-̇x↓ y.
[*55·3] ≡.xSy.R=S-̇x↓ y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·35 -/
/- PM-VERBATIM-BEGIN PM1:✱55·36
✱55·36. ⊢ : xRy .≡. (R−̇x↓y)⊍x↓y=R
Dem.
⊢.*55·3.⊃⊢:xRy. ≡.x↓ y⊂̇R.
[*23·62] ≡.x↓ y⊍R=R.
[*23·91] ≡.R-̇x↓ y⊍x↓ y=R:⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·36 -/
/- PM-VERBATIM-BEGIN PM1:✱55·37
✱55·37. ⊢ : x∈α . y∈β .≡. x↓y⊂̇α↑β
Dem.
⊢.*35·103.⊃⊢:x∈α.y∈β. ≡.x(α↑β)y.
[*55·3] ≡.x↓ y⊂̇α↑β:⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·37 -/
/- PM-VERBATIM-BEGIN PM1:✱55·4
✱55·4. ⊢ : a{x↓y⊍z↓w}b .≡. a=x . b=y .∨. a=z . b=w
PM-VERBATIM-END PM1:✱55·4 -/
/- PM-VERBATIM-BEGIN PM1:✱55·41
✱55·41. ⊢ : R=x↓y⊍z↓w .⊃: aRb .⊃ₐ,ᵦ φ(a,b) :≡. φ(x,y).φ(z,w)
Dem.
⊢.*55·4.⊃⊢::.Hp.⊃:: aRb.⊃ₐ,b.φ(a,b):≡:.
a=x.b=y.∨.a=z.b=w:⊃ₐ,b.φ(a,b):.
[*4·77] ≡:.(a,b):. a=x.b=y.⊃.φ(a,b):a=z.b=w.⊃.φ(a,b):.
[*11·31] ≡:.(a,b):a=x.b=y.⊃.φ(a,b):.(a,b):a=z.b=w.⊃.φ(a,b):.
[*13·21] ≡:. φ(x,y).φ(z,w)::.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·41 -/
/- PM-VERBATIM-BEGIN PM1:✱55·42
✱55·42. ⊢ : R=x↓y⊍z↓w .⊃: (∃a,b).aRb.φ(a,b) .≡: φ(x,y).∨.φ(z,w)
Dem.
⊢.*55·4.⊃⊢::.Hp.⊃::(∃ a,b).aRb.φ(a,b).≡:.
(∃ a,b):. a=x.b=y.∨.a=z.b=w:φ(a,b):.
[*4·4] ≡:.(∃ a,b):a=x.b=y.φ(a,b):∨:a=z.b=w.φ(a,b):.
[*11·41] ≡:.(∃ a,b).a=x.b=y.φ(a,b).∨.(∃ a,b).a=z.b=w.φ(a,b):.
[*13·22] ≡:. φ(x,y).∨.φ(z,w)::.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·42 -/
/- PM-VERBATIM-BEGIN PM1:✱55·43
✱55·43. ⊢ : x↓y⊍z↓w=x↓y⊍c↓d .≡. z=c.w=d .≡. z↓w=c↓d
Dem.
⊢.*55·202. ⊃⊢:z=c.w=d.⊃.z↓ w=c↓ d.
[*23·551] ⊃.x↓ y⊍z↓ w=x↓ y⊍c↓ d (1)
⊢.*23·58. ⊃⊢:. x↓ y⊍z↓ w=x↓ y⊍c↓ d.⊃:
z↓ w⊂̇x↓ y⊍c↓ d.c↓ d⊂̇x↓ y⊍z↓ w:
[*55·3·13.*23·34] ⊃:z=x.w=y.∨.z=c.w=d:c=x.d=y.∨.c=z.d=w:
[*13·16] ⊃:z=x.w=y.∨.z=c.w=d:c=x.d=y.∨.z=c.w=d:
[*4·41] ⊃:z=x.w=y.c=x.d=y.∨.z=c.w=d:
[*13·172] ⊃:z=c.w=d (2)
⊢.(1).(2).⊃⊢:x↓ y⊍z↓ w=x↓ y⊍c↓ d.≡.z=c.w=d (3)
⊢.(3).*55·202.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·43 -/
/- PM-VERBATIM-BEGIN PM1:✱55·431
✱55·431. ⊢ : x↓y⊍z↓w=a↓b⊍c↓d .⊃: x=a.y=b .∨. x=c.y=d
Dem.
⊢.*55·4.⊃⊢::Hp. ≡:. u=x.v=y.∨.u=z.v=w:
≡u,v:u=a.v=b.∨.u=c.v=d:.
[*11·1] ⊃:. x=x.y=y.∨.x=z.y=w:
≡ :x=a.y=b.∨.x=c.y=d:.
[*13·15] ⊃:. x=a.y=b.∨.x=c.y=d (1)
⊢.*55·43. ⊃⊢:. x=a.y=b.⊃:x↓ y⊍z↓ w=a↓ b⊍z↓ w:
[*13·171] ⊃:Hp.⊃.a↓ b⊍z↓ w=a↓ b⊍c↓ d.
[*55·43] ⊃.z=c.w=d (2)
⊢.(2).Comm.*4·7. ⊃⊢:.Hp.⊃:x=a.y=b.⊃.x=a.y=b.z=c.w=d (3)
Similarly ⊢:.Hp.⊃:x=c.y=d.⊃.x=c.y=d.z=a.w=b (4)
⊢.(1).(3).(4).⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·431 -/
/- PM-VERBATIM-BEGIN PM1:✱55·44
✱55·44. ⊢ : x↓y⊍z↓w=a↓b⊍c↓d . x↓y≠z↓w .⊃: x=a.y=b.z=c.w=d .∨. x=c.y=d.z=a.w=b
Dem.
⊢.*55·43. ⊃⊢:x=a.y=b.⊃.x↓ y⊍z↓ w=a↓ b⊍z↓ w:
z=c.w=d.⊃.a↓ b⊍z↓ w=a↓ b⊍c↓ d:
[*3·47.*13·17] ⊃⊢:x=a.y=b.z=c.w=d.
⊃.x↓ y⊍z↓ w=a↓ b⊍c↓ d (1)
Similarly ⊢:x=c.y=d.z=a.w=b.
⊃.x↓ y⊍z↓ w=a↓ b⊍c↓ d (2)
⊢.(1).(2).*55·431·202.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·44 -/
/- PM-VERBATIM-BEGIN PM1:✱55·5
✱55·5. ⊢ : R⊂̇x↓y⊍z↓w .⊃: R=Λ̇ .∨. R=x↓y .∨. R=z↓w .∨. R=x↓y⊍z↓w
Dem.
⊢.*25·12.*23·58·42.⊃
⊢:. R=Λ̇.∨.R=x↓ y.∨.R=z↓ w.∨.R=x↓ y⊍z↓ w:
⊃.R⊂̇x↓ y⊍z↓ w (1)
⊢.*25·49. ⊃⊢:. R⊂̇x↓ y⊍z↓ w.R∩̇x↓ y=Λ.⊃:R⊂̇z↓ w:
[*55·341] ⊃:R=Λ.∨.R=z↓ w (2)
⊢.*25·43. ⊃⊢:. R⊂̇x↓ y⊍z↓ w.⊃:R-̇x↓ y⊂̇z↓ w:
[*55·341] ⊃:R-̇x↓ y=Λ̇.∨.R-̇x↓ y=z↓ w:
[*25·24.*23·551] ⊃:(R-̇x↓ y)⊍x↓ y=x↓ y.∨.
(R-̇x↓ y)⊍x↓ y=x↓ y⊍z↓ w (3)
⊢.*55·3·36.⊃⊢:∃̇!(R∩̇x↓ y).⊃.(R-̇x↓ y)⊍x↓ y=R (4)
⊢.(3).(4).⊃⊢:. R⊂̇x↓ y⊍z↓ w.∃̇!(R∩̇x↓ y).⊃:
R=x↓ y.∨.R=x↓ y⊍z↓ w (5)
⊢.(2).(5).⊃⊢:. R⊂̇x↓ y⊍z↓ w.⊃:
R=Λ̇.∨.R=x↓ y.∨.R=z↓ w.∨.R=x↓ y⊍z↓ w (6)
⊢.(1).(6).⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·5 -/
/- PM-VERBATIM-BEGIN PM1:✱55·52
✱55·52. ⊢ : x=y .≡. x↓y⊂̇I
PM-VERBATIM-END PM1:✱55·52 -/
/- PM-VERBATIM-BEGIN PM1:✱55·521
✱55·521. ⊢ : x≠y .≡. x↓y⊂̇J
PM-VERBATIM-END PM1:✱55·521 -/
/- PM-VERBATIM-BEGIN PM1:✱55·53
✱55·53. ⊢ : x≠y .⊃: CʻR=ιʻx∪ιʻy . R⊂̇J .≡. ∃̇!R . R⊂̇x↓y⊍y↓x
Dem.
⊢. *55·5. ⊃⊢ :. ∃̇ !R.R⊂̇x↓ y⊍y↓ x.≡:
R = x↓ y .∨. R=y↓ x.∨. R = x↓ y⊍y↓ x (1)
⊢ . *55·15. ⊃⊢. Cʻx↓ y = ιʻ x∪ ιʻ y . Cʻ y↓ x = ιʻ x∪ ιʻ y (2)
⊢. (2).*33·262. ⊃⊢. Cʻ (x↓ y⊍y↓ x) = ιʻ x∪ ιʻ y (3)
⊢. *55·521. ⊃⊢: x≠ y .⊃. x ↓ y⊂̇J.y↓ x⊂̇J. (4)
[*23·59] ⊃. x↓ y⊍y ↓ x⊂̇J (5)
⊢.(1).(2). (3).(4).(5). ⊃⊢:.
x≠ y .⊃:∃̇!R . R⊂̇x↓ y⊍y↓ x.⊃. Cʻ R= ιʻ x∪ ιʻ y. R⊂̇J (6)
⊢.*35·91. ⊃⊢ : Cʻ R = ιʻ x∪ ιʻ y .∪ . R⊂̇(ιʻ x∪ ιʻ y)↑ (ιʻ x∪ ιʻ y).
[*55·52] ⊃. R⊂̇x↓ x⊍x ↓ y⊍y ↓ x⊍y ↓ y (7)
⊢· *50·24. ⊃⊢ : R⊂̇J. ⊃ . ∼(xRx).∼(yRy).
[*55·3. Transp] ⊃.R∩̇x↓ x = Λ̇. R∩̇ y ↓ y = Λ̇ (8)
⊢. (7).(8).*25·49. ⊃⊢:Cʻ R = ιʻ x∪ ιʻ y. R⊂̇J .⊃ . R⊂̇x ↓ y⊍y ↓ x (9)
⊢. *33·24.*51·161. ⊃⊢: Cʻ R = ιʻ x∪ ιʻ y . ⊃ .∃̇ !R (10)
⊢. (9).(10). ⊃⊢: Cʻ R = ιʻ x∪ ιʻ y . R⊂̇J .⊃ .∃̇!R.R⊂̇x↓ y⊍y↓ x (11)
⊢. (6).(11). ⊃⊢ .Prop
PM-VERBATIM-END PM1:✱55·53 -/
/- PM-VERBATIM-BEGIN PM1:✱55·54
✱55·54. ⊢ : x≠y .⊃: CʻR=ιʻx∪ιʻy . R∩̇Ř=Λ̇ .≡. R=x↓y .∨. R=y↓x
Dem.
⊢. *50·46.*4·71 . ⊃⊢:R∩̇Ř = Λ̇ .≡ .R ⊂̇ J. R∩̇Ř= Λ̇ (1)
⊢ . (1).*55·53 . ⊃⊢:: x ≠ y. ⊃:. CʻR= ιʻ x∪ ιʻ y. R∩̇Ř= Λ̇.
≡ :∃̇ !R .R⊂̇x↓ y⊍y↓ x.R∩̇Ř= Λ̇ :
[*55·5·134] ≡:R = x↓ y.∨.R = y↓ x.∨.R = x↓ y⊍y↓ x:R∩̇Ř=Λ̇ (2)
⊢. *55·32.⊃⊢:. x≠ y. ⊃: x↓ y∩̇y↓ x= Λ̇:
[*55·14] ⊃: R = x ↓ y .⊃. R∩̇Ř= Λ̇ :
R = y↓ x .⊃. R∩̇Ř= Λ̇ (3)
⊢.*55·14.*31·15·33. ⊃⊢:R=x↓ y⊍y↓ x.⊃.R=Ř.
[*23·5] ⊃.R∩̇Ř=R.
[*55·134] ⊃.∃̇!R∩̇Ř (4)
⊢.(3).(4).*4·71.*5·71.⊃
⊢:: x≠ y.⊃:. R=x↓ y.∨.R=y↓ x.∨.R =x↓ y⊍y↓ x:R∩̇Ř=Λ̇:
≡:R=x↓ y.∨.R=y↓ x (5)
⊢.(2).(5).⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·54 -/
/- PM-VERBATIM-BEGIN PM1:✱55·57
✱55·57. ⊢ . R|(x↓y)=R→ʻx ↑ ιʻy
PM-VERBATIM-END PM1:✱55·57 -/
/- PM-VERBATIM-BEGIN PM1:✱55·571
✱55·571. ⊢ . (x↓y)|S=ιʻx ↑ S←ʻy
PM-VERBATIM-END PM1:✱55·571 -/
/- PM-VERBATIM-BEGIN PM1:✱55·572
✱55·572. ⊢ . R|(x↓y)|S=R→ʻx ↑ S←ʻy
PM-VERBATIM-END PM1:✱55·572 -/
/- PM-VERBATIM-BEGIN PM1:✱55·573
✱55·573. ⊢ . R|(x↓y)|Š=R→ʻx ↑ S→ʻy
PM-VERBATIM-END PM1:✱55·573 -/
/- PM-VERBATIM-BEGIN PM1:✱55·58
✱55·58. ⊢ : E!Rʻx .⊃. R|(x↓y)=(Rʻx)↓y
PM-VERBATIM-END PM1:✱55·58 -/
/- PM-VERBATIM-BEGIN PM1:✱55·581
✱55·581. ⊢ : E!Šʻy .⊃. (x↓y)|S=x↓(Šʻy)
PM-VERBATIM-END PM1:✱55·581 -/
/- PM-VERBATIM-BEGIN PM1:✱55·582
✱55·582. ⊢ : E!Rʻx . E!Šʻy .⊃. R|(x↓y)|S=(Rʻx)↓(Šʻy)
PM-VERBATIM-END PM1:✱55·582 -/
/- PM-VERBATIM-BEGIN PM1:✱55·583
✱55·583. ⊢ : E!Rʻx . E!Sʻy .⊃. R|(x↓y)|Š=(Rʻx)↓(Sʻy)
PM-VERBATIM-END PM1:✱55·583 -/
/- PM-VERBATIM-BEGIN PM1:✱55·6
✱55·6. ⊢ . (R∥Š)ʻ(z↓w)=R→ʻz ↑ S→ʻw
PM-VERBATIM-END PM1:✱55·6 -/
/- PM-VERBATIM-BEGIN PM1:✱55·61
✱55·61. ⊢ : E!Rʻz . E!Sʻw .⊃. (R∥Š)ʻ(z↓w)=(Rʻz)↓(Sʻw)
PM-VERBATIM-END PM1:✱55·61 -/
/- PM-VERBATIM-BEGIN PM1:✱55·62
✱55·62. ⊢ : z≠w . S=x↓z⊍y↓w .⊃. Sʻz=x . Sʻw=y
Dem.
⊢.*55·13. ⊃⊢::Hp.⊃:. uSz.≡:u=x.z=z.∨.u=y.z=w (1)
⊢.(1).*13·15. ⊃ ⊢:.Hp.⊃:uSz.≡.u=x (2)
Similarly ⊢:.Hp.⊃:uSw.≡.u=y (3)
⊢.(2).(3).*30·3.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·62 -/
/- PM-VERBATIM-BEGIN PM1:✱55·621
✱55·621. ⊢ : x≠y . S=x↓z⊍y↓w .⊃. Šʻx=z . Šʻy=w
[Proof as in ✱55·6]
PM-VERBATIM-END PM1:✱55·621 -/
/- PM-VERBATIM-BEGIN PM1:✱55·63
✱55·63. ⊢ : ∃̇!Q∩̇S . P∥Q=R∥S .⊃. P=R
Dem.
⊢.*43·112.⊃⊢::Hp. ⊃:. P|(y↓ z)| Q=R|(y↓ z)| S:.
[*34·1] ⊃:.(∃ u,v).xPu.u(y↓ z)v.vQw.≡ₓ,w.
(∃ u,v).xRu.u(y↓ z)v.vSw:.
[*55·13.*13·22] ⊃:. xPy.zQw.≡ₓ,w.xRy.zSw:.
[*4·73] ⊃:. zQw.zSw.⊃w:xPy.≡ₓ.xRy (1)
⊢.(1).*10·11.*11·35. ⊃⊢:.Hp.⊃:xPy.≡ₓ.xRy (2)
⊢.(2).*10·11·21.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·63 -/
/- PM-VERBATIM-BEGIN PM1:✱55·631
✱55·631. ⊢ : ∃̇!P∩̇R . P∥Q=R∥S .⊃. Q=S
[Proof as in ✱55·63]
PM-VERBATIM-END PM1:✱55·631 -/
/- PM-VERBATIM-BEGIN PM1:✱55·632
✱55·632. ⊢ : P∥Q=R∥S . ∃̇!P . ∃̇!Q .⊃. ∃̇!P∩̇R . ∃̇!Q∩̇S
Dem.
⊢.*55·13. ⊃⊢:xPy.zQw. ⊃.x{P|(y↓ z)| Q}w.
[*43·112] ⊃.x(P∥Q)ʻ (y↓ z)w (1)
⊢.(1).⊃⊢:. Hp. ⊃:xPy.zQw. ⊃.x{(R∥S)ʻ (y↓ z)}w.
[*43·112] ⊃.x{R|(y↓ z)| S}w.
[*34·1] ⊃.(∃ u,v).xRu.u(y↓ z)v.vSw.
[*55·13.*13·22] ⊃.xRy.zSw.
[*4·7] ⊃.x(P∩̇R)y.z(Q∩̇S)w:.⊃⊢.Prop
PM-VERBATIM-END PM1:✱55·632 -/
/- PM-VERBATIM-BEGIN PM1:✱55·64
✱55·64. ⊢ : ∃̇!P . ∃̇!Q .∨. ∃̇!R . ∃̇!S :⊃: P∥Q=R∥S .≡. P=R . Q=S
PM-VERBATIM-END PM1:✱55·64 -/

/- PM-VERBATIM-BEGIN PM1:✱55·122
✱55·122. ⊢:R(x↓)y.≡.R=x↓ y [*55·11]
PM-VERBATIM-END PM1:✱55·122 -/
/- PM-VERBATIM-BEGIN PM1:✱55·13
✱55·13. ⊢:z(x↓ y)w.≡.z=x.w=y
PM-VERBATIM-END PM1:✱55·13 -/
/- PM-VERBATIM-BEGIN PM1:✱55·51
✱55·51. ⊢:. R ⪽ x ↓ y ⊍ S .⊃: x R y .∨. R ⪽ S
PM-VERBATIM-END PM1:✱55·51 -/
