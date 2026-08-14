/-! # ✱121 — Opening (Gutenberg 78255). -/
/- PM-VERBATIM-BEGIN PM2:✱121·01
✱121·01. P(x−y)=P⃖poʻx∩P⃗poʻy Df
PM-VERBATIM-END PM2:✱121·01 -/
/- PM-VERBATIM-BEGIN PM2:✱121·011
✱121·011. P(x⊣y)=P⃖poʻx∩P⃗∗ʻy Df
PM-VERBATIM-END PM2:✱121·011 -/
/- PM-VERBATIM-BEGIN PM2:✱121·012
✱121·012. P(x⟝y)=P⃖∗ʻx∩P⃗poʻy Df
PM-VERBATIM-END PM2:✱121·012 -/
/- PM-VERBATIM-BEGIN PM2:✱121·013
✱121·013. P(x⊢⊣y)=P⃖∗ʻx∩P⃗∗ʻy Df
PM-VERBATIM-END PM2:✱121·013 -/
/- PM-VERBATIM-BEGIN PM2:✱121·02
✱121·02. P_ν=x̂ŷ{N₀cʻP(x⊢⊣y)=ν+_c1} Df
PM-VERBATIM-END PM2:✱121·02 -/
/- PM-VERBATIM-BEGIN PM2:✱121·03
✱121·03. finidʻP=R̂{(∃ν).ν∈NC induct−ιʻΛ.R=P_ν} Df
PM-VERBATIM-END PM2:✱121·03 -/
/- PM-VERBATIM-BEGIN PM2:✱121·031
✱121·031. finʻP=R̂{(∃ν).ν∈NC induct−ιʻΛ−ιʻ0.R=P_ν} Df
PM-VERBATIM-END PM2:✱121·031 -/
/- PM-VERBATIM-BEGIN PM2:✱121·04
✱121·04. ν_P=P̌_{ν−_c1}ʻBʻP Df
PM-VERBATIM-END PM2:✱121·04 -/
/- PM-VERBATIM-BEGIN PM2:✱121·1
✱121·1. ⊢ : z∈P(x−y) .≡. xPpo z.zPpo y
PM-VERBATIM-END PM2:✱121·1 -/
/- PM-VERBATIM-BEGIN PM2:✱121·101
✱121·101. ⊢ : z∈P(x⊣y) .≡. xPpo z.zP∗y
PM-VERBATIM-END PM2:✱121·101 -/
/- PM-VERBATIM-BEGIN PM2:✱121·102
✱121·102. ⊢ : z∈P(x⟝y) .≡. xP∗z.zPpo y
PM-VERBATIM-END PM2:✱121·102 -/
/- PM-VERBATIM-BEGIN PM2:✱121·103
✱121·103. ⊢ : z∈P(x⊢⊣y) .≡. xP∗z.zP∗y
PM-VERBATIM-END PM2:✱121·103 -/
/- PM-VERBATIM-BEGIN PM2:✱121·11
✱121·11. ⊢ : xP_νy .≡. N₀cʻP(x⊢⊣y)=ν+_c1
PM-VERBATIM-END PM2:✱121·11 -/
/- PM-VERBATIM-BEGIN PM2:✱121·12
✱121·12. ⊢ : R∈finidʻP .≡. (∃ν).ν∈NC induct−ιʻΛ.R=P_ν
PM-VERBATIM-END PM2:✱121·12 -/
/- PM-VERBATIM-BEGIN PM2:✱121·121
✱121·121. ⊢ : R∈finʻP .≡. (∃ν).ν∈NC induct−ιʻΛ−ιʻ0.R=P_ν
PM-VERBATIM-END PM2:✱121·121 -/
/- PM-VERBATIM-BEGIN PM2:✱121·13
✱121·13. ⊢ : f(ν_P) .≡. f(P̌_{ν−_c1}ʻBʻP)
PM-VERBATIM-END PM2:✱121·13 -/
/- PM-VERBATIM-BEGIN PM2:✱121·14
✱121·14. ⊢. P(x−y)=P̌(y−x)
PM-VERBATIM-END PM2:✱121·14 -/
/- PM-VERBATIM-BEGIN PM2:✱121·141
✱121·141. ⊢. P(x⊣y)=P̌(y⟝x)
PM-VERBATIM-END PM2:✱121·141 -/
/- PM-VERBATIM-BEGIN PM2:✱121·142
✱121·142. ⊢. P(x⟝y)=P̌(y⊣x)
PM-VERBATIM-END PM2:✱121·142 -/
/- PM-VERBATIM-BEGIN PM2:✱121·143
✱121·143. ⊢. P(x⊢⊣y)=P̌(y⊢⊣x)
PM-VERBATIM-END PM2:✱121·143 -/
/- PM-VERBATIM-BEGIN PM2:✱121·2
✱121·2. ⊢ : ∼(xPpo x) .⊃. x∼∈P(x−y)
PM-VERBATIM-END PM2:✱121·2 -/
/- PM-VERBATIM-BEGIN PM2:✱121·201
✱121·201. ⊢ : ∼(yPpo y) .⊃. y∼∈P(x−y)
PM-VERBATIM-END PM2:✱121·201 -/
/- PM-VERBATIM-BEGIN PM2:✱121·202
✱121·202. ⊢ : Ppo⊂J .⊃. x,y∼∈P(x−y)
PM-VERBATIM-END PM2:✱121·202 -/
/- PM-VERBATIM-BEGIN PM2:✱121·22
✱121·22. ⊢ : xPpo y .≡. x∈P(x⟝y) .≡. ∃!P(x⟝y)
PM-VERBATIM-END PM2:✱121·22 -/
/- PM-VERBATIM-BEGIN PM2:✱121·23
✱121·23. ⊢ : xP∗y .≡. x,y∈P(x⊢⊣y) .≡. ∃!P(x⊢⊣y)
PM-VERBATIM-END PM2:✱121·23 -/
/- PM-VERBATIM-BEGIN PM2:✱121·231
✱121·231. ⊢ : x∈CʻP .≡. x∈P(x⊢⊣x) .≡. ∃!P(x⊢⊣x)
PM-VERBATIM-END PM2:✱121·231 -/
/- PM-VERBATIM-BEGIN PM2:✱121·24
✱121·24. ⊢ : xPpo y .⊃. P(x⊣y)=P(x−y)∪ιʻy

Dem.
⊢ .✱91·54.✱121·101.⊃
⊢ :. z∈ P(x⊣ y). ≡ :xPpoz:zPpoy.∨.z=y.y∈ CʻP:
[✱13·193.✱91·504] ≡:xPpoz.zPpoy.∨.xPpoy.z=y (1)
⊢ .(1).✱4·73.⊃ ⊢ :: Hp.⊃ :. z∈ P(x⊣ y). ≡ :xPpoz.zPpoy.∨.z=y:: ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·24 -/
/- PM-VERBATIM-BEGIN PM2:✱121·241
✱121·241. ⊢ : xPpo y .⊃. P(x⟝y)=P(x−y)∪ιʻx
PM-VERBATIM-END PM2:✱121·241 -/
/- PM-VERBATIM-BEGIN PM2:✱121·242
✱121·242. ⊢ : xP∗y .⊃. P(x⊢⊣y)=P(x⊣y)∪ιʻx=P(x⟝y)∪ιʻy
PM-VERBATIM-END PM2:✱121·242 -/
/- PM-VERBATIM-BEGIN PM2:✱121·251
✱121·251. ⊢. Ppo(x⊣y)=P(x⊣y)
PM-VERBATIM-END PM2:✱121·251 -/
/- PM-VERBATIM-BEGIN PM2:✱121·252
✱121·252. ⊢. Ppo(x⟝y)=P(x⟝y)
PM-VERBATIM-END PM2:✱121·252 -/
/- PM-VERBATIM-BEGIN PM2:✱121·253
✱121·253. ⊢. Ppo(x⊢⊣y)=P(x⊢⊣y)
PM-VERBATIM-END PM2:✱121·253 -/
/- PM-VERBATIM-BEGIN PM2:✱121·254
✱121·254. ⊢. P_ν=(Ppo)_ν
PM-VERBATIM-END PM2:✱121·254 -/
/- PM-VERBATIM-BEGIN PM2:✱121·26
✱121·26. ⊢. P̌_ν=(P̌)_ν

Dem.
⊢ .✱121·11·143.⊃ ⊢ :xP̌ _ν y. ≡ .N₀cʻP̌ (x⊢⊣ y)=ν +_c1.
[✱90·132.✱121·11] ≡ .x(P̌ )_ν y:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·26 -/
/- PM-VERBATIM-BEGIN PM2:✱121·27
✱121·27. ⊢ : xP_νy .⊃. ν,ν+_c1∈NC−ιʻΛ

Dem.
⊢ .✱121·11.✱103·12.⊃ ⊢ :Hp.⊃ .P(x⊢⊣ y)∈ ν +_c1 (1)
⊢ .(1).✱110·4·42.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·27 -/
/- PM-VERBATIM-BEGIN PM2:✱121·271
✱121·271. ⊢ : ∼(ν,ν+_c1∈NC−ιʻΛ) .⊃. P_ν=Λ̇
PM-VERBATIM-END PM2:✱121·271 -/
/- PM-VERBATIM-BEGIN PM2:✱121·272
✱121·272. ⊢ : ∃!P_ν .⊃. ν≥0.ν+_c1>0.ν+_c1≥1

Dem.
⊢ .✱117·5.✱121·27.⊃ ⊢ :Hp. ⊃ .ν ≥ 0. (1)
[✱117·561.✱110·641] ⊃ .ν +_c1≥ 1. (2)
[✱117·511·531] ⊃ .ν +_c1>0 (3)
⊢ .(1).(2).(3).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·272 -/
/- PM-VERBATIM-BEGIN PM2:✱121·273
✱121·273. ⊢ : ∃!P_{ν+_c1} .⊃. ν+_c1>0

Dem.
⊢ .✱121·27.✱110·4.⊃ ⊢ :Hp. ⊃ .ν ∈ NC-℩ʻΛ .
[✱117·6] ⊃ .ν +_c1≥ 1.
[✱117·511·531] ⊃ .ν +_c1>0:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·273 -/
/- PM-VERBATIM-BEGIN PM2:✱121·3
✱121·3. ⊢. P₀⊂1↾CʻP

Dem.
⊢ .✱121·11.⊃ ⊢ :xP₀y. ≡ .P(x⊢⊣ y)∈ 1.
[✱121·23] ⊃ .xP∗y.x=y.
[✱90·12] ⊃ .x(I↾ CʻP)y:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·3 -/
/- PM-VERBATIM-BEGIN PM2:✱121·301
✱121·301. ⊢ : ∼(xPpo x) .⊃: xP₀y .≡. x∈CʻP.x=y

Dem.
⊢ .✱91·542·56. ⊃ ⊢ :xP∗z.zP∗x.x≠ z.⊃ .xPpox (1)
⊢ .(1).Transp. ⊃ ⊢ :. Hp. ⊃ :xP∗z.zP∗x.⊃ ₓ,z.x=z:
[✱121·231] ⊃ :x∈ CʻP.⊃ .P(x⊢⊣ x)=℩ʻx:
[✱13·12.✱52·22] ⊃ :x∈ CʻP.x=y.⊃ .P(x⊢⊣ y)∈ 1.
[✱121·11] ⊃ .xP₀y (2)
⊢ .(2).✱121·3.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·301 -/
/- PM-VERBATIM-BEGIN PM2:✱121·302
✱121·302. ⊢ : Ppo⊂J .⊃. P₀=I↾CʻP
PM-VERBATIM-END PM2:✱121·302 -/
/- PM-VERBATIM-BEGIN PM2:✱121·303
✱121·303. ⊢ : NcʻP(x⊢⊣y)>1 .⊃. xPpo y

Dem.
⊢ .✱121·23.✱52·22.✱117·42.⊃ ⊢ :. Hp. ⊃ :x∈ P(x⊢⊣ y).P(x⊢⊣ y)≠ ℩ʻx:
[✱51·4.Transp] ⊃ :(∃ z).z≠ x.z∈ P(x⊢⊣ y):
[✱121·103.✱91·542] ⊃ :(∃ z).xPpoz.zP∗y:
[✱91·574] ⊃ :xPpoy:. ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·303 -/
/- PM-VERBATIM-BEGIN PM2:✱121·304
✱121·304. ⊢ : Ppo⊂J .⊃: xP₁y .≡. P(x⊢⊣y)=ιʻx∪ιʻy.x≠y

Dem.
⊢ .✱121·303·11.⊃ ⊢ :Hp.xP₁y. ⊃ .xPpoy.
[Hp] ⊃ .x≠ y (1)
⊢ .(1).✱54·53·101.✱121·23·11. ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·304 -/
/- PM-VERBATIM-BEGIN PM2:✱121·305
✱121·305. ⊢ : Ppo⊂J .⊃. P₁⊂P

Dem.
⊢ .✱121·303.⊃ ⊢ :Hp.xP₁y. ⊃ .xPpoy.
[✱91·52] ⊃ .(∃ z).xPz.zP∗y (1)
⊢ .✱121·304.✱91·542.⊃
⊢ :. Hp.xP₁y. ⊃ :xPpoz.zP∗y.⊃ .z=y:
[✱91✱502] ⊃ :xPz.zP∗y.⊃ .z=y (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·305 -/
/- PM-VERBATIM-BEGIN PM2:✱121·306
✱121·306. ⊢ : P∈1→Cls.∼(xPpo x).xPy .⊃. P(x⊢⊣y)=ιʻx∪ιʻy.x≠y

Dem.
⊢ .✱91·542. ⊃ ⊢ :xP∗z.zP∗y.z≠ x.z≠ y.xPy.⊃ :xPpoz.zPpoy.xPy:
[✱34·1] ⊃ :xPpoz.zPpo| P̌ x:
[✱92·11] ⊃ :P∈ 1→Cls.⊃ .xPpoz.zP∗x:
[✱91·574] ⊃ :P∈ 1→Cls.⊃ .xPpox (1)
⊢ .(1).Transp. ⊃ ⊢ :: Hp.⊃ :. xP∗z.zP∗y.⊃ z:z=x.∨.z=y (2)
⊢ .✱121·23. ⊃ ⊢ :Hp.⊃ .x,y∈ P(x⊢⊣ y) (3)
⊢ .✱91·502. ⊃ ⊢ :Hp.⊃ .x≠ y (4)
⊢ .(2).(3).(4).✱121·103.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·306 -/
/- PM-VERBATIM-BEGIN PM2:✱121·307
✱121·307. ⊢ : P∈Cls→1.∼(yPpo y).xPy .⊃. P(x⊢⊣y)=ιʻx∪ιʻy.x≠y
PM-VERBATIM-END PM2:✱121·307 -/
/- PM-VERBATIM-BEGIN PM2:✱121·308
✱121·308. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J .⊃. P⊂P₁
PM-VERBATIM-END PM2:✱121·308 -/
/- PM-VERBATIM-BEGIN PM2:✱121·31
✱121·31. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J .⊃. P₁=P
PM-VERBATIM-END PM2:✱121·31 -/
/- PM-VERBATIM-BEGIN PM2:✱121·32
✱121·32. ⊢. P_ν⊂P∗

Dem.
⊢ .✱121·11.✱120·421.✱101·14.Transp. ⊃ ⊢ :xP_ν y.⊃ .∃ !P(x⊢⊣ y).
[✱121·23] ⊃ .xP∗y:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·32 -/
/- PM-VERBATIM-BEGIN PM2:✱121·321
✱121·321. ⊢ : ν>0 .⊃. P_ν⊂Ppo

Dem.
⊢ .✱120·428.✱121·11.⊃ ⊢ :Hp.xP_ν y. ⊃ .NcʻP(x⊢⊣ y)>1.
[✱117·55.✱52·181.✱121·23] ⊃ .(∃ z).z∈ P(x⊢⊣ y).z≠ x.
[✱121·103.✱91·542] ⊃ .(∃ z).xPpoz.zR∗y.
[✱91·574] ⊃ .xPpoy:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·321 -/
/- PM-VERBATIM-BEGIN PM2:✱121·322
✱121·322. ⊢. CʻP_ν⊂CʻP
PM-VERBATIM-END PM2:✱121·322 -/
/- PM-VERBATIM-BEGIN PM2:✱121·323
✱121·323. ⊢ : ν>0 .⊃. DʻP_ν⊂DʻP.ᗡʻP_ν⊂ᗡʻP
PM-VERBATIM-END PM2:✱121·323 -/
/- PM-VERBATIM-BEGIN PM2:✱121·324
✱121·324. ⊢. DʻP_{ν+_c1}⊂DʻP.ᗡʻP_{ν+_c1}⊂ᗡʻP

Dem.
⊢ .✱121·273·323.⊃ ⊢ :∃̇ !P_ν +_c1.⊃ .DʻP_ν +_c1⊂ DʻP.ᗡʻP_ν +_c1⊂ ᗡʻP (1)
⊢ .(1).✱33·241.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·324 -/
/- PM-VERBATIM-BEGIN PM2:✱121·325
✱121·325. ⊢ : ∃!P_μ∩P_ν .⊃. μ=ν

Dem.
⊢ .✱121·11. ⊃ ⊢ :Hp.⊃ .∃ !(μ +_c1)∩ (ν +_c1)∩ t₀ʻμ .
[✱100·42.✱110·4] ⊃ .∃ !(μ +_c1)∩ t₀ʻμ .(μ +_c1)∩ t₀ʻμ =ν +_c1.
[✱120·311] ⊃ .μ =ν :⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·325 -/
/- PM-VERBATIM-BEGIN PM2:✱121·326
✱121·326. ⊢. finʻP⊂finidʻP.finidʻP−ιʻP₀⊂finʻP
PM-VERBATIM-END PM2:✱121·326 -/
/- PM-VERBATIM-BEGIN PM2:✱121·327
✱121·327. ⊢ : ∃!P₀ .⊃. finʻP=finidʻP−ιʻP₀

Dem.
⊢ .✱121·325.Transp.✱121·121.⊃ ⊢ :. Hp.⊃ :R∈ finʻP.⊃ .R≠ P₀ (1)
⊢ .(1).✱121·326.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·327 -/
/- PM-VERBATIM-BEGIN PM2:✱121·33
✱121·33. ⊢ : P∈1→Cls .⊃: z∈P(x−y) .≡. z∈P(x⊣Pʻy)

Dem.
⊢ .✱71·7.⊃ ⊢ :. Hp.⊃ :zP∗(Pʻy). ≡ .zP∗| Py.
[✱91·52] ≡ .zPpoy (1)
⊢ .(1).✱121·1·101·102·103.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·33 -/
/- PM-VERBATIM-BEGIN PM2:✱121·331
✱121·331. ⊢ : P∈1→Cls.Ppo⊂J .⊃: xP_ν(Pʻy) .≡. xP_{ν+_c1}y

Dem.
⊢ .✱121·324.✱71·16. ⊃ ⊢ :. Hp.⊃ :xP_ν +_c1y.⊃ .E!Pʻy (1)
⊢ .✱121·33. ⊃ ⊢ :Hp.E!Pʻy.⊃ .P(x ⟝ y)=P(x⊢⊣ Pʻy) (2)
⊢ .✱121·242·32.(2). ⊃ ⊢ :Hp(2).xP∗y.⊃ .P(x⊢⊣ y)=P(x⊢⊣ Pʻy)∪ ι ʻy (3)
⊢ .✱91·52. ⊃ ⊢ :Hp. ⊃ .∼(yP∗| Py).
[✱71·7] ⊃ .∼{yP∗ (Pʻy)} .
[✱121·103] ⊃ .∼{y∈ P(x⊢⊣ Pʻy)} (4)
⊢ .(3).(4).✱110·63. ⊃ ⊢ :Hp(3).⊃ .NcʻP(x⊢⊣ y)=NcʻP(x⊢⊣ Pʻy)+_c1 (5)
⊢ .(1).(5).✱121·11·32.⊃
⊢ :Hp.xP_ν +_c 1y. ⊃ .(ν +_c 1) +_c 1 = NcʻP(x⊢⊣ Pʻy)+_c 1.
[✱120·311.✱121·27] ⊃ . ν +_c 1 = NcʻP(x ⊢⊣ Pʻy).
[✱121·11] ⊃ .xP_ν (Pʻy) (6)
⊢ .(5).✱14·21.✱121·11·32. ⊃ ⊢ : Hp.xP_ν (Pʻy).⊃ .NcʻP(x ⊢⊣ y)=(ν +_c 1) +_c 1.
[✱121·11] ⊃ . xP_ν +_c 1y (7)
⊢ .(6).(7).⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱121·331 -/
/- PM-VERBATIM-BEGIN PM2:✱121·332
✱121·332. ⊢ : P∈1→Cls.Ppo⊂J .⊃. P_{ν+_c1}=P_ν|P
PM-VERBATIM-END PM2:✱121·332 -/
/- PM-VERBATIM-BEGIN PM2:✱121·333
✱121·333. ⊢ : P∈Cls→1.Ppo⊂J .⊃. P_{ν+_c1}=P|P_ν
PM-VERBATIM-END PM2:✱121·333 -/
/- PM-VERBATIM-BEGIN PM2:✱121·34
✱121·34. ⊢ : P∈1→Cls.Ppo⊂J.ν∈NC induct .⊃. P_ν∈1→Cls

Dem.
⊢ . ✱121·3. ⊃ ⊢ . P₀ ∈ 1→Cls (1)
⊢ . ✱121·332. ⊃ ⊢ :. Hp. ⊃ : P_ν ∈ 1→Cls. ⊃ . P_ν +_c 1 ∈ 1→Cls (2)
⊢ . (1).(2). ✱120·11.⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱121·34 -/
/- PM-VERBATIM-BEGIN PM2:✱121·341
✱121·341. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct .⊃. P_ν∈Cls→1
PM-VERBATIM-END PM2:✱121·341 -/
/- PM-VERBATIM-BEGIN PM2:✱121·342
✱121·342. ⊢ : P∈1→1.Ppo⊂J.ν∈NC induct .⊃. P_ν∈1→1
PM-VERBATIM-END PM2:✱121·342 -/
/- PM-VERBATIM-BEGIN PM2:✱121·35
✱121·35. ⊢ : P∈1→Cls.Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_{μ+_cν}

Dem.
⊢ . ✱50·62. ✱121·302·322. ⊃ ⊢ : Hp. ⊃ . P_μ | P₀ = P_μ +_c 0 (1)
⊢ . ✱121·332. ⊃ ⊢ :. Hp. ⊃ : μ ,ν ∈ NC induct. P_μ | P_ν = P_μ +_c ν . ⊃ .
P_μ | P_ν +_c 1 = P_μ +_c ν | P
[✱121·332] = P_μ +_c ν +_c 1 (2)
⊢ . (1).(2). ✱120·13.⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱121·35 -/
/- PM-VERBATIM-BEGIN PM2:✱121·351
✱121·351. ⊢ : P∈Cls→1.Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_{μ+_cν}
PM-VERBATIM-END PM2:✱121·351 -/
/- PM-VERBATIM-BEGIN PM2:✱121·352
✱121·352. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_{μ+_cν}
PM-VERBATIM-END PM2:✱121·352 -/
/- PM-VERBATIM-BEGIN PM2:✱121·36
✱121·36. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_ν|P_μ

Dem.
⊢ . ✱121·321.⊃ ⊢ : Hp. ⊃ . P_μ ⪽ Ppo.
[✱91·59·601] ⊃ . (P_μ )ₚₒ ⪽ J. (1)
[✱121·31·34·341] ⊃ .(P_μ )₁ = P_μ (2)
⊢ . ✱121·332·333·352 . (1). ⊃
⊢ :. Hp. ⊃ : (P_μ )_ν +_c 1 = (P_μ )_ν | P_μ :
[✱34·27] ⊃ : (P_μ )_ν = P_μ ×_c ν . ⊃ . (P_μ )_ν +_c 1 = P_μ ×_c ν | P_μ
[✱121·35·351] = P_(μ ×_c ν ) +_c μ
[✱113·671] = P_μ ×_c (ν +_c 1) (3)
⊢ . (2). (3). ✱120·47. ⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱121·36 -/
/- PM-VERBATIM-BEGIN PM2:✱121·361
✱121·361. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J.μ,ν∈NC induct−ιʻ0 .⊃. P_μ|P_ν=P_ν|P_μ
PM-VERBATIM-END PM2:✱121·361 -/
/- PM-VERBATIM-BEGIN PM2:✱121·37
✱121·37. ⊢ : P∈Cls→1.y∈P(x⊢⊣z) .⊃. P(x⊢⊣z)=P(x⊢⊣y)∪P(y⊢⊣z)

Dem.
⊢ .✱121·103. ⊃ ⊢ :Hp.⊃ .xP∗y.yP∗z (1)
⊢ .(1).✱121·103.⊃
⊢ :. Hp. ⊃ :w∈ P(x⊢⊣ z).≡ .xP∗w.wP∗z.xP∗y.yP∗z (2)
⊢ .✱96·302. ⊃ ⊢ :: Hp.⊃ :. xP∗w.xP∗y.⊃ :wP∗y.∨.yP∗w (3)
⊢ .(2).(3).✱4·73.⊃
⊢ :: Hp. ⊃ :. w∈ P(x⊢⊣ z).≡ :xP∗w.wP∗z.xP∗y.yP∗z.wP∗y.∨.
xP∗w.wP∗z.xP∗y.yP∗z.yP∗w (4)
⊢ .✱90·17.✱4·73.⊃ ⊢ :wP∗y.yP∗z. ≡ .wP∗z.wP∗y.yP∗z:
yP∗w.wP∗z.≡ .yP∗z.wP∗z.yP∗w (5)
⊢ .(4).(5).⊃ ⊢ :: Hp. ⊃ :. w∈ P(x⊢⊣ z).≡ :xP∗w.xP∗y.yP∗z.wP∗y.∨.
xP∗w.wP∗z.xP∗y.yP∗w:
[✱90·17.✱4·73] ≡:xP∗w.wP∗y.yP∗z.∨.xP∗y.yP∗w.wP∗z:
[(1).✱4·73] ≡ :xP∗w.wP∗y.∨.yP∗w.wP∗z:
[✱121·103] ≡ :w∈ P(x⊢⊣ y)∪ P(y⊢⊣ z):: ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·37 -/
/- PM-VERBATIM-BEGIN PM2:✱121·371
✱121·371. ⊢ : P∈(Cls→1)∪(1→Cls).y∈P(x⊢⊣z) .⊃. interval decomposition
PM-VERBATIM-END PM2:✱121·371 -/
/- PM-VERBATIM-BEGIN PM2:✱121·372
✱121·372. ⊢ : P∈(Cls→1)∪(1→Cls).y∈P(x⊣z) .⊃. interval decomposition
PM-VERBATIM-END PM2:✱121·372 -/
/- PM-VERBATIM-BEGIN PM2:✱121·373
✱121·373. ⊢ : P∈(Cls→1)∪(1→Cls).y∈P(x⟝z) .⊃. interval decomposition
PM-VERBATIM-END PM2:✱121·373 -/
/- PM-VERBATIM-BEGIN PM2:✱121·374
✱121·374. ⊢ : P∈(Cls→1)∪(1→Cls).y∈P(x−z) .⊃. interval decomposition
PM-VERBATIM-END PM2:✱121·374 -/
/- PM-VERBATIM-BEGIN PM2:✱121·38
✱121·38. ⊢ : R∈Cls→1.xRpo x .⊃. R(x⊢⊣x)=R⃖∗ʻx
PM-VERBATIM-END PM2:✱121·38 -/
/- PM-VERBATIM-BEGIN PM2:✱121·4
✱121·4. ⊢ : R∈Cls→1.xRy.yR∗z .⊃. R(x⊢⊣z)=ιʻx∪R(y⊢⊣z)

Dem.
⊢ .✱90·311.⊃ ⊢ :: Hp.⊃ :. xR∗w. ≡ :x=w.∨.xR| R∗w:
[✱71·701.Hp] ≡ :x=w.∨.yR∗w (1)
⊢ .✱90·172. ⊃ ⊢ :. Hp.⊃ :x=w.⊃ .wR∗z (2)
⊢ .(1).(2).⊃ ⊢ :: Hp.⊃ :. xR∗w.wR∗z. ≡ :x=w.∨.yR∗w.wR∗z (3)
⊢ .(3).✱121·103.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·4 -/
/- PM-VERBATIM-BEGIN PM2:✱121·41
✱121·41. ⊢ : R∈Cls→1.R(z⊢⊣z)∈Cls induct .⊃. R(x⊢⊣z)∈Cls induct

Dem.
⊢ .✱121·4.✱120·251.✱90·172. ⊃ ⊢ :. Hp.⊃ :
yR∗z.R(y⊢⊣ z)∈ Cls induct.xRy.⊃ .xR∗z.R(x⊢⊣ z)∈ Cls induct (1)
⊢ .(1).✱90·112 Ř/R. ⊃ ⊢ :Hp.xR∗z.⊃ .R(x⊢⊣ z)∈ Cls induct (2)
⊢ .✱121·23.✱120·212. ⊃ ⊢ :∼(xR∗z).⊃ .R(x⊢⊣ z)∈ Cls induct (3)
⊢ .(2).(3).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·41 -/
/- PM-VERBATIM-BEGIN PM2:✱121·42
✱121·42. ⊢ : R∈Cls→1.∼(zRpo z) .⊃. R(x⊢⊣z)∈Cls induct

Dem.
⊢ .✱121·303.Transp.✱120·441. ⊃ ⊢ :Hp.⊃ .NcʻR(z⊢⊣ z)≤ 1.
[✱120·48] ⊃ .NcʻR(z⊢⊣ z)∈ NC induct.
[✱120·211] ⊃ .R(z⊢⊣ z)∈ Cls induct (1)
⊢ .(1).✱121·41.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·42 -/
/- PM-VERBATIM-BEGIN PM2:✱121·43
✱121·43. ⊢ : R∈Cls→1.zRpo z .⊃. E!ι̌ʻ(R⃗ʻz∩R⃖∗ʻz)

Dem.
⊢ .✱91·52. ⊃ ⊢ :Hp. ⊃ .(∃ a).zR∗a.aRz (1)
⊢ .✱96·453. ⊃ ⊢ :Hp.⊃ .(R⃖∗ʻz)↿ R∈ 1→1.
[✱71·122] ⊃ .â(zR∗a.aRz)∈ 1∪ ι ʻΛ (2)
⊢ .(1).(2). ⊃ ⊢ :Hp. ⊃ .â(zR∗a.aRz)∈ 1.
[✱52·15] ⊃ .E!ι̌ ʻ(R⃗ʻz∩ R⃖∗ʻz):⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·43 -/
/- PM-VERBATIM-BEGIN PM2:✱121·431
✱121·431. ⊢ : R∈Cls→1.zRpo z.a=ι̌ʻ(R⃗ʻz∩R⃖∗ʻz).α ...

Dem.
⊢ .✱35·61. ⊃ ⊢ :Hp. ⊃ .a∼∈ DʻS.
[✱91·504] ⊃ .a∼∈ DʻSpo.
[✱33·14] ⊃ .∼(aSpoa):⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·431 -/
/- PM-VERBATIM-BEGIN PM2:✱121·432
✱121·432. ⊢ : Hp ✱121·431 .⊃. S(z⊢⊣a)∈Cls induct

Dem.
⊢ .✱71·261.⊃ ⊢ :Hp.⊃ .S∈ Cls→1 (1)
⊢ .(1).✱121·431·42.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·432 -/
/- PM-VERBATIM-BEGIN PM2:✱121·433
✱121·433. ⊢ : Hp ✱121·431.z≠a .⊃. S(z⊢⊣a)=R⃖∗ʻz=R(z⊢⊣z)

Dem.
⊢ .✱96·11. ⊃ ⊢ :. Hp. ⊃ :zS∗w.⊃ .zR∗w (1)
⊢ .✱51·3.✱91·504. ⊃ ⊢ :. Hp. ⊃ :z∈ a.z∈ DʻR:
[✱35·61] ⊃ :z∈ DʻS:
[✱90·12] ⊃ :zS∗z (2)
⊢ .(1).✱90·16. ⊃ ⊢ :: Hp. ⊃ :. zS∗w.wRy.⊃ :w∈ α ∪ ι ʻa.wRy:
[✱35·1] ⊃ :wSy.∨.w=a.wRy:
[Hp.✱71·171] ⊃ :wSy.∨.y=z:
[✱90·16·17.(2)] ⊃ :zS∗y (3)
⊢ .(2).(3).✱90·112. ⊃ ⊢ :. Hp. ⊃ :zR∗w.⊃ .zS∗w: (4)
[Hp] ⊃ ⊢ :zS∗a (5)
⊢ .✱71·171. ⊃ ⊢ :Hp. aRy.⊃ .y=z (6)
⊢ .✱91·542·504.✱35·61. ⊃ ⊢ :. Hp.⊃ :wS∗a.w≠ a.wRy.⊃ .wSpoa.wSy.
[✱92·111] ⊃ .yS∗a (7)
⊢ .(5).(6).(7). ⊃ ⊢ :. Hp.⊃ :wS∗a.wRy.⊃ .yS∗a (8)
⊢ .(5).(8).✱90·112. ⊃ ⊢ :. Hp.⊃ :zR∗y.⊃ .yS∗a (9)
⊢ .(4).(9). ⊃ ⊢ :. Hp.⊃ :zR∗y.⊃ .zS∗y.yS∗a (10)
⊢ .(1) y/w.(10). ⊃ ⊢ :. Hp.⊃ :zS∗y.yS∗a.≡ .zR∗y:
[✱121·103] ⊃ :S(z⊢⊣ a) =R⃖∗ʻz
[✱121·38] =R(z⊢⊣ z):. ⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·433 -/
/- PM-VERBATIM-BEGIN PM2:✱121·434
✱121·434. ⊢ : Hp ✱121·431.z=a .⊃. R⃖∗ʻz=R(z⊢⊣z)=ιʻz

Dem.
⊢ .✱32·18. ⊃ ⊢ :Hp.⊃ .zRz.
[✱96·33] ⊃ .R⃖∗ʻz=ι ʻz. (1)
[✱121·38] ⊃ .R(z⊢⊣ z)=ι ʻz (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·434 -/
/- PM-VERBATIM-BEGIN PM2:✱121·44
✱121·44. ⊢ : R∈Cls→1.zRpo z .⊃. R(z⊢⊣z)∈Cls induct

Dem.
⊢ .✱121·43·432·433.⊃
⊢ :Hp.z≠ ι̌ ʻ(R⃗ʻz∩ R⃖∗ʻz).⊃ .R(z⊢⊣ z)∈ Cls induct (1)
⊢ .✱121·434.✱120·213.⊃
⊢ :Hp.z=ι̌ ʻ(R⃗ʻz∩ R⃖∗ʻz).⊃ .R(z⊢⊣ z)∈ Cls induct (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·44 -/
/- PM-VERBATIM-BEGIN PM2:✱121·441
✱121·441. ⊢ : R∈Cls→1.zRpo z .⊃. R(x⊢⊣z)∈Cls induct
PM-VERBATIM-END PM2:✱121·441 -/
/- PM-VERBATIM-BEGIN PM2:✱121·45
✱121·45. ⊢ : R∈Cls→1 .⊃. R(x⊢⊣z)∈Cls induct
PM-VERBATIM-END PM2:✱121·45 -/
/- PM-VERBATIM-BEGIN PM2:✱121·46
✱121·46. ⊢ : R∈1→Cls .⊃. R(x⊢⊣z)∈Cls induct
PM-VERBATIM-END PM2:✱121·46 -/
/- PM-VERBATIM-BEGIN PM2:✱121·47
✱121·47. ⊢ : R∈(Cls→1)∪(1→Cls) .⊃. R(x⊢⊣z)∈Cls induct
PM-VERBATIM-END PM2:✱121·47 -/
/- PM-VERBATIM-BEGIN PM2:✱121·48
✱121·48. ⊢ : R∈Cls→1 .⊃: cardinal interval comparison

Dem.
⊢ .✱121·39.⊃ ⊢ :. Hp. ⊃ :∃ !R(x⊢⊣ z)-R(x⊢⊣ y).≡ .
R(x⊢⊣ y)⊂ R(x⊢⊣ z).R(x⊢⊣ y)≠ R(x⊢⊣ z).
[✱120·7.✱121·45] ⊃ .NcʻR(x⊢⊣ y)
PM-VERBATIM-END PM2:✱121·48 -/
/- PM-VERBATIM-BEGIN PM2:✱121·481
✱121·481. ⊢ : R∈Cls→1 .⊃: NcʻR(x⊢⊣y)≤NcʻR(x⊢⊣z) .≡. interval inclusion

Dem.
⊢ .✱121·45.✱120·441.⊃
⊢ :. Hp.⊃ :NcʻR(x⊢⊣ y)≤ NcʻR(x⊢⊣ z). ≡ .∼{NcʻR(x⊢⊣ z)
PM-VERBATIM-END PM2:✱121·481 -/
/- PM-VERBATIM-BEGIN PM2:✱121·5
✱121·5. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. finitary-level decomposition

Dem.
⊢ .✱121·302·31. ⊃ ⊢ :Hp. ⊃ .P₀=I↾ CʻP.P₁=P (1)
⊢ .(1).✱121·332·333·352. ⊃ ⊢ :. Hp.ν ∈ NC induct.⊃ :P_ν +_c1=P_ν | P: (2)
[✱91·341] ⊃ :P_ν ∈ PotidʻP.⊃ .P_ν +_c1∈ PotidʻP:P_ν ∈ PotʻP.⊃ .P_ν +_c1∈ PotʻP (3)
⊢ .(1).✱91·35. ⊃ ⊢ :Hp.⊃ .P₀∈ PotidʻP.P₁∈ PotʻP (4)
⊢ .(3).(4).✱120·13·47.⊃ ⊢ :. Hp. ⊃ :ν ∈ NC induct.⊃ .P_ν ∈ PotidʻP:
ν ∈ NC induct-ι ʻ0.⊃ .P_ν ∈ PotʻP:
[✱121·12·121] ⊃ :finidʻP⊂ PotidʻP.finʻP⊂ PotʻP (5)
⊢ .(2).✱121·121.⊃ ⊢ :. Hp. ⊃ :ν ∈ NC induct.⊃ .P_ν | P∈ finʻP:
[✱121·12] ⊃ :Q∈ finidʻP.⊃ .Q| P∈ finʻP:
[(1).✱91·17·171] ⊃ :PotidʻP⊂ finidʻP.PotʻP⊂ finʻP (6)
⊢ .(5).(6).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·5 -/
/- PM-VERBATIM-BEGIN PM2:✱121·501
✱121·501. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J.∃!P .⊃. finitary-level uniqueness

Dem.
⊢ .✱121·302.⊃ ⊢ :Hp.⊃ .∃̇ !P₀ (1)
⊢ .(1).✱121·5·327.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·501 -/
/- PM-VERBATIM-BEGIN PM2:✱121·502
✱121·502. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. finitary-level exhaustion

Dem.
⊢ .✱91·504.✱33·24.✱121·5.⊃ ⊢ :P=Λ̇ .⊃ .ṡ ʻ(finidʻP-ι ʻP₀)=Λ̇ =Ppo (1)
⊢ .(1).✱121·501·5.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·502 -/
/- PM-VERBATIM-BEGIN PM2:✱121·51
✱121·51. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. finid/fin characterization

Dem.
⊢ .✱121·31. ⊃ ⊢ :Hp. ⊃ .P₁=P (1)
⊢ .✱121·332·333. ⊃ ⊢ :Hp.⊃ .P₂ =P₁| P₁
[(1)] =P² (2)
⊢ .✱121·332·333·352. ⊃ ⊢ :Hp.⊃ .P₃ =P₂| P₁
[(1).(2)] =P³ (3)
⊢ .(2).(3). etc. .⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·51 -/
/- PM-VERBATIM-BEGIN PM2:✱121·52
✱121·52. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. ṡʻfinidʻP=P∗
PM-VERBATIM-END PM2:✱121·52 -/
/- PM-VERBATIM-BEGIN PM2:✱121·6
✱121·6. ⊢ : ν≠0 .⊃. f(ν_P) .≡. f[ι̌ʻŷ{N₀cʻP(BʻP⊢⊣y)=ν}]

Dem.
⊢ .✱121·11.✱120·414·416.⊃ ⊢ :. Hp.⊃ :
f[ι̌ ʻŷ {NcʻP (BʻP ⊢⊣ y) = ν}] . ≡ . f[ι̌ ʻŷ {(BʻP)P_ν -_c1y}].
[✱121·13] ≡.f(ν _P):⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·6 -/
/- PM-VERBATIM-BEGIN PM2:✱121·601
✱121·601. ⊢ : E!BʻP .⊃. BʻP=1_P.∼{(BʻP)Ppo(BʻP)}

Dem.
⊢ .✱91·504.✱93·1. ⊃ ⊢ .∼{(BʻP)Ppo(BʻP)}. (1)
[✱121·301] ⊃ ⊢ :. E!BʻP. ⊃ :(BʻP)P₀y.≡ y.BʻP=y:
[✱31·17] ⊃ :BʻP=P̌ ₀ʻBʻP:
[✱121·13] ⊃ :BʻP=1_P (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·601 -/
/- PM-VERBATIM-BEGIN PM2:✱121·602
✱121·602. ⊢ : E!BʻP.P∈1→1 .⊃. P̌ʻBʻP=2_P

Dem.
⊢ .✱121·306·601. ⊃ ⊢ :Hp.⊃ .P(BʻP⊢⊣ P̌ ʻBʻP)∈ 2 (1)
⊢ .✱121·23·601. ⊃ ⊢ :: Hp.⊃ :. (BʻP)Ppoy.⊃ .BʻP,y∈ P(BʻP⊢⊣ y).BʻP≠ y:.
[✱54·53.✱121·303] ⊃ :. P(BʻP⊢⊣ y)∈ 2. ⊃ :P(BʻP⊢⊣ y)=ι ʻBʻP∪ ι ʻy.(BʻP)Ppoy:
[✱92·111] ⊃ :(P̌ ʻBʻP)P∗y.P(BʻP⊢⊣ y)=ι ʻBʻP∪ ι ʻy:
[✱121·103·601] ⊃ :P̌ ʻBʻP∈ ι ʻBʻP∪ ι ʻy.P̌ ʻBʻP≠ BʻP:
[✱51·232] ⊃ :y=P̌ ʻBʻP (2)
⊢ .(1).(2).✱121·6.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·602 -/
/- PM-VERBATIM-BEGIN PM2:✱121·61
✱121·61. ⊢ : P∈1→Cls.Ppo⊂J.x∈sʻgenʻP .⊃. generator rank characterization

Dem.
⊢ .✱93·36. ⊃ ⊢ :. P∈ 1→Cls.x∈ sʻgenʻP.⊃ .(∃ a).a BP.a P∗x (1)
⊢ .✱121·52. ⊃ ⊢ :. P∈ 1→Cls.Ppo ⪽ J.⊃ :a P∗x.≡ .a(ṡ ʻfinidʻP)x (2)
⊢ .(1).(2). ⊃ ⊢ :Hp.⊃ .(∃ a).α BP.a (ṡ ʻfinidʻP)x.
[✱121·12] ⊃ .(∃ a,ν ).a BP.ν ∈ NC induct.a P_ν x:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·61 -/
/- PM-VERBATIM-BEGIN PM2:✱121·62
✱121·62. ⊢ : P∈Cls→1.Ppo⊂J.(BʻP)P∗x .⊃. rank characterization

Dem.
⊢ .✱121·52. ⊃ ⊢ :Hp. ⊃ .(BʻP)(ṡ ʻfinidʻP)x.
[✱121·12] ⊃ .(∃ ν ).ν ∈ NC induct.(BʻP)P_ν x (1)
⊢ .✱121·341. ⊃ ⊢ :Hp.ν ∈ NC induct.⊃ .P_ν ∈ Cls→1 (2)
⊢ .(1).(2). ⊃ ⊢ :Hp. ⊃ .(∃ ν ).ν ∈ NC induct.x=P̌ _ν ʻBʻP.
[✱121·13] ⊃ .(∃ ν ).ν ∈ NC induct.x=(ν +_c1)_P.
[✱120·471] ⊃ .(∃ μ ).μ ∈ NC induct-ι ʻ0.x=μ _P:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·62 -/
/- PM-VERBATIM-BEGIN PM2:✱121·63
✱121·63. ⊢ : E!ν_P .⊃. N₀cʻP(BʻP⊢⊣ν_P)=ν

Dem.
⊢ .✱121·13·131.⊃ ⊢ :Hp. ⊃ .(BʻP)P_ν -_c1ν _P.
[✱121·11] ⊃ .N₀cʻP(BʻP⊢⊣ ν _P)=ν :⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·63 -/
/- PM-VERBATIM-BEGIN PM2:✱121·631
✱121·631. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0 .⊃. ν_P rank properties

Dem.
⊢ .✱120·414·416.✱121·11.⊃
⊢ :. Hp.⊃ :N₀cʻP(BʻP⊢⊣ y)=ν . ≡ .(BʻP)P_{ν -_c1}y. (1)
[✱121·341] ≡ .y=P̌ _ν -_c1ʻBʻP.
[✱121·13] ≡ .y=ν _P (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·631 -/
/- PM-VERBATIM-BEGIN PM2:✱121·632
✱121·632. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0.y=ν_P.yPz .⊃. successor property

Dem.
⊢ .✱121·13. ⊃ ⊢ :Hp. ⊃ .(BʻP)P_ν -_c1y.yPz.
[✱121·333·352] ⊃ .(BʻP)P_ν z.
[✱121·631] ⊃ .z=(ν +_c1)_P:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·632 -/
/- PM-VERBATIM-BEGIN PM2:✱121·633
✱121·633. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0.ν_P∈DʻP .⊃. predecessor property
PM-VERBATIM-END PM2:✱121·633 -/
/- PM-VERBATIM-BEGIN PM2:✱121·634
✱121·634. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0 .⊃. ν_P domain characterization
PM-VERBATIM-END PM2:✱121·634 -/
/- PM-VERBATIM-BEGIN PM2:✱121·635
✱121·635. ⊢ : P∈Cls→1.Ppo⊂J.E!ν_P .⊃. ν∈NC induct−ιʻ0

Dem.
⊢ .✱121·63·45. ⊃ ⊢ :Hp.⊃ .ν ∈ NC induct (1)
⊢ .✱121·13. ⊃ ⊢ :E!ν _P. ⊃ .∃̇ !P_(ν -_c1).
[✱121·272] ⊃ .(ν -_c1)+_c1>0.
[✱120·416] ⊃ .ν >0 (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·635 -/
/- PM-VERBATIM-BEGIN PM2:✱121·636
✱121·636. ⊢ : P∈Cls→1.Ppo⊂J.E!ν_P.∼E!(ν+_c1)_P .⊃. terminal-rank property

Dem.
⊢ .✱121·635. ⊃ ⊢ :Hp. ⊃ .ν ∈ NC induct-ι ʻ0. (1)
[✱121·634.Hp] ⊃ .ν _P∼∈ DʻP (2)
⊢ .(1).✱121·63. ⊃ ⊢ :: Hp. ⊃ :. ∃ !P(BʻP⊢⊣ ν _P):.
[✱121·23] ⊃ :. (BʻP)P∗ν _P:.
[✱96·302.✱91·542] ⊃ :. (BʻP)P∗z.⊃ :zP∗ν _P.∨.ν _PPpoz (3)
⊢ .(2).(3).✱91·504. ⊃ ⊢ :. Hp. ⊃ :(BʻP)P∗z.⊃ .zP∗ν _P:
[✱4·71] ⊃ :(BʻP)P∗z.≡ .(BʻP)P∗z.zP∗v_P:
[✱121·103] ⊃ :P⃖∗ʻBʻP=P(BʻP⊢⊣ ν _P): (4)
[✱121·63] ⊃ :N₀cʻP⃖∗ʻBʻP=ν (5)
⊢ .(4).(5).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·636 -/
/- PM-VERBATIM-BEGIN PM2:✱121·637
✱121·637. ⊢ : E!ν_P .⊃. ν_P∈CʻP

Dem.
⊢ .✱121·13.✱14·28. ⊃ ⊢ :E!ν _P. ≡ .ν _P.=P̌ _ν -_c1ʻBʻP.
[✱121·322] ⊃ .ν _P∈ CʻP:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·637 -/
/- PM-VERBATIM-BEGIN PM2:✱121·638
✱121·638. ⊢ : E!(ν+_c1)_P .⊃: (BʻP)P_νx .≡. x=(ν+_c1)_P : (ν+_c1)−_c1=ν

Dem.
⊢ .✱121·13.⊃ ⊢ :E!(ν +_c1)_P. ≡ .E!P̌_{(ν +_c1)}-_c1ʻBʻP. (1)
[✱121·272] ⊃ .(ν +_c1)-_c1≥ 0.
[✱14·21] ⊃ .E!(ν +_c1)-_c 1.
[✱14·22.(✱120·411)] ⊃ .(ν +_c1)-_c1=ν (2)
⊢ .(2).⊃ ⊢ :. Hp.⊃ :(BʻP)P_ν x. ≡ .(BʻP)P_(ν +_c1)-_c1x.
[(1).✱30·4] ≡ .x=P̌ _(ν +_c1)-_c1ʻBʻP.
[✱121·13] ≡ .x=(ν +_c1)_P (3)
⊢ .(3).(2).⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱121·638 -/
/- PM-VERBATIM-BEGIN PM2:✱121·641
✱121·641. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0 .⊃. rank equivalences
PM-VERBATIM-END PM2:✱121·641 -/
/- PM-VERBATIM-BEGIN PM2:✱121·65
✱121·65. ⊢ : P∈Cls→1.Ppo⊂J.μ≠0.E!(μ+_cν)_P .⊃. μ_P P_ν (μ+_cν)_P

Dem.
⊢ .✱121·631·635·64.✱120·452.⊃
⊢ :Hp. ⊃ .(BʻP)P_μ -_c1μ _P.(BʻP)P_μ +_cν -_c1(μ +_cν )_P.
[✱121·351.✱120·424] ⊃ .(BʻP)P_μ -_c1μ _P.(BʻP)(P_μ -_c1| P_ν )(μ +_cν )_P.
[✱121·341.✱72·591] ⊃ .μ _PP_ν (μ +_cν )_P:⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·65 -/
/- PM-VERBATIM-BEGIN PM2:✱121·66
✱121·66. ⊢ : P∈Cls→1.Ppo⊂J.NcʻP(BʻP⊢⊣x)>ν .⊃. x∈ᗡʻP_ν

Dem.
⊢ .✱121·45.✱120·48.⊃ ⊢ :Hp. ⊃ .ν ∈ NC induct.
[✱120·429] ⊃ .NcʻP(BʻP⊢⊣ x)≥ ν +_c1.
[✱117·31] ⊃ .(∃ μ ).NcʻP(BʻP⊢⊣ x)=ν +_c1+_cμ .
[✱121·11] ⊃ .(∃ μ ).(BʻP)P_ν +_cμ x.
[✱121·351·352] ⊃ .(∃ μ ).(BʻP)(P_μ | P_ν )x.
[✱34·36] ⊃ .x∈ ᗡʻP_ν :⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·66 -/
/- PM-VERBATIM-BEGIN PM2:✱121·7
✱121·7. ⊢ : R∈1→1.aBR.aR∗x .⊃. R⃗∗ʻx=R(a⊢⊣x).R⃗∗ʻx∈Cls induct

Dem.
⊢ .✱96·25.⊃ ⊢ :. Hp. ⊃ :yR∗x.⊃ .aR∗y:
[✱4·71] ⊃ :yR∗x.≡ .aR∗y.yR∗x:
[✱121·103] ⊃ :R⃗∗ʻx=R(a⊢⊣ x) (1)
⊢ .(1).✱121·45.⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·7 -/
/- PM-VERBATIM-BEGIN PM2:✱121·71
✱121·71. ⊢ : R∈1→1 : x∈sʻgenʻR ∨ (∃y).y∈R⃡∗ʻx.yRpo y :⊃. structural property

Dem.
⊢ .✱121·7.✱93·36. ⊃ ⊢ :R∈ 1→1.x∈ sʻgenʻR.⊃ .R⃗∗ʻx∈ Cls induct (1)
⊢ .✱97·55·111.⊃ ⊢ :. R∈ 1→1:(∃ y). y∈ ⃡R∗ʻx.yRpoy:⊃ :
y∈ ⃡R∗ʻx .⊃ y.yRpoy:x∈ ⃡R∗ʻx:
[✱10·26] ⊃ :xRpox:
[✱121·381] ⊃ :R⃗∗ʻx=R(x⊢⊣ x):
[✱121·45] ⊃ :R⃗∗ʻx∈ Cls induct (2)
⊢ .(1).(2).⊃ ⊢ .Prop
PM-VERBATIM-END PM2:✱121·71 -/
/- PM-VERBATIM-BEGIN PM2:✱121·72
✱121·72. ⊢ : R∈1→1.R⃗∗ʻx∼∈Cls induct .⊃. terminal structural property
PM-VERBATIM-END PM2:✱121·72 -/

/- PM-VERBATIM-BEGIN PM2:✱121·21
✱121✱21. ⊢ :xPpoy.≡ .y∈ P(x⊣ y).≡ .∃ !P(x⊣ y)
PM-VERBATIM-END PM2:✱121·21 -/

/- PM-VERBATIM-BEGIN PM2:✱121·39
✱121·39. ⊢ :. R∈Cls→1.⊃ :R(x⊢⊣y)⊂R(x⊢⊣z).∨.R(x⊢⊣z)⊂R(x⊢⊣y)
PM-VERBATIM-END PM2:✱121·39 -/

/- PM-VERBATIM-BEGIN PM2:✱121·64
✱121✱64. ⊢ :P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0.NcʻP⃖∗ʻBʻP≥ν .⊃. E!ν_P
PM-VERBATIM-END PM2:✱121·64 -/
