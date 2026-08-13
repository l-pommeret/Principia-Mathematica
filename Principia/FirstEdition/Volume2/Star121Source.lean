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
PM-VERBATIM-END PM2:✱121·26 -/
/- PM-VERBATIM-BEGIN PM2:✱121·27
✱121·27. ⊢ : xP_νy .⊃. ν,ν+_c1∈NC−ιʻΛ
PM-VERBATIM-END PM2:✱121·27 -/
/- PM-VERBATIM-BEGIN PM2:✱121·271
✱121·271. ⊢ : ∼(ν,ν+_c1∈NC−ιʻΛ) .⊃. P_ν=Λ̇
PM-VERBATIM-END PM2:✱121·271 -/
/- PM-VERBATIM-BEGIN PM2:✱121·272
✱121·272. ⊢ : ∃!P_ν .⊃. ν≥0.ν+_c1>0.ν+_c1≥1
PM-VERBATIM-END PM2:✱121·272 -/
/- PM-VERBATIM-BEGIN PM2:✱121·273
✱121·273. ⊢ : ∃!P_{ν+_c1} .⊃. ν+_c1>0
PM-VERBATIM-END PM2:✱121·273 -/
/- PM-VERBATIM-BEGIN PM2:✱121·3
✱121·3. ⊢. P₀⊂1↾CʻP
PM-VERBATIM-END PM2:✱121·3 -/
/- PM-VERBATIM-BEGIN PM2:✱121·301
✱121·301. ⊢ : ∼(xPpo x) .⊃: xP₀y .≡. x∈CʻP.x=y
PM-VERBATIM-END PM2:✱121·301 -/
/- PM-VERBATIM-BEGIN PM2:✱121·302
✱121·302. ⊢ : Ppo⊂J .⊃. P₀=I↾CʻP
PM-VERBATIM-END PM2:✱121·302 -/
/- PM-VERBATIM-BEGIN PM2:✱121·303
✱121·303. ⊢ : NcʻP(x⊢⊣y)>1 .⊃. xPpo y
PM-VERBATIM-END PM2:✱121·303 -/
/- PM-VERBATIM-BEGIN PM2:✱121·304
✱121·304. ⊢ : Ppo⊂J .⊃: xP₁y .≡. P(x⊢⊣y)=ιʻx∪ιʻy.x≠y
PM-VERBATIM-END PM2:✱121·304 -/
/- PM-VERBATIM-BEGIN PM2:✱121·305
✱121·305. ⊢ : Ppo⊂J .⊃. P₁⊂P
PM-VERBATIM-END PM2:✱121·305 -/
/- PM-VERBATIM-BEGIN PM2:✱121·306
✱121·306. ⊢ : P∈1→Cls.∼(xPpo x).xPy .⊃. P(x⊢⊣y)=ιʻx∪ιʻy.x≠y
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
PM-VERBATIM-END PM2:✱121·32 -/
/- PM-VERBATIM-BEGIN PM2:✱121·321
✱121·321. ⊢ : ν>0 .⊃. P_ν⊂Ppo
PM-VERBATIM-END PM2:✱121·321 -/
/- PM-VERBATIM-BEGIN PM2:✱121·322
✱121·322. ⊢. CʻP_ν⊂CʻP
PM-VERBATIM-END PM2:✱121·322 -/
/- PM-VERBATIM-BEGIN PM2:✱121·323
✱121·323. ⊢ : ν>0 .⊃. DʻP_ν⊂DʻP.ᗡʻP_ν⊂ᗡʻP
PM-VERBATIM-END PM2:✱121·323 -/
/- PM-VERBATIM-BEGIN PM2:✱121·324
✱121·324. ⊢. DʻP_{ν+_c1}⊂DʻP.ᗡʻP_{ν+_c1}⊂ᗡʻP
PM-VERBATIM-END PM2:✱121·324 -/
/- PM-VERBATIM-BEGIN PM2:✱121·325
✱121·325. ⊢ : ∃!P_μ∩P_ν .⊃. μ=ν
PM-VERBATIM-END PM2:✱121·325 -/
/- PM-VERBATIM-BEGIN PM2:✱121·326
✱121·326. ⊢. finʻP⊂finidʻP.finidʻP−ιʻP₀⊂finʻP
PM-VERBATIM-END PM2:✱121·326 -/
/- PM-VERBATIM-BEGIN PM2:✱121·327
✱121·327. ⊢ : ∃!P₀ .⊃. finʻP=finidʻP−ιʻP₀
PM-VERBATIM-END PM2:✱121·327 -/
/- PM-VERBATIM-BEGIN PM2:✱121·33
✱121·33. ⊢ : P∈1→Cls .⊃: z∈P(x−y) .≡. z∈P(x⊣Pʻy)
PM-VERBATIM-END PM2:✱121·33 -/
/- PM-VERBATIM-BEGIN PM2:✱121·331
✱121·331. ⊢ : P∈1→Cls.Ppo⊂J .⊃: xP_ν(Pʻy) .≡. xP_{ν+_c1}y
PM-VERBATIM-END PM2:✱121·331 -/
/- PM-VERBATIM-BEGIN PM2:✱121·332
✱121·332. ⊢ : P∈1→Cls.Ppo⊂J .⊃. P_{ν+_c1}=P_ν|P
PM-VERBATIM-END PM2:✱121·332 -/
/- PM-VERBATIM-BEGIN PM2:✱121·333
✱121·333. ⊢ : P∈Cls→1.Ppo⊂J .⊃. P_{ν+_c1}=P|P_ν
PM-VERBATIM-END PM2:✱121·333 -/
/- PM-VERBATIM-BEGIN PM2:✱121·34
✱121·34. ⊢ : P∈1→Cls.Ppo⊂J.ν∈NC induct .⊃. P_ν∈1→Cls
PM-VERBATIM-END PM2:✱121·34 -/
/- PM-VERBATIM-BEGIN PM2:✱121·341
✱121·341. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct .⊃. P_ν∈Cls→1
PM-VERBATIM-END PM2:✱121·341 -/
/- PM-VERBATIM-BEGIN PM2:✱121·342
✱121·342. ⊢ : P∈1→1.Ppo⊂J.ν∈NC induct .⊃. P_ν∈1→1
PM-VERBATIM-END PM2:✱121·342 -/
/- PM-VERBATIM-BEGIN PM2:✱121·35
✱121·35. ⊢ : P∈1→Cls.Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_{μ+_cν}
PM-VERBATIM-END PM2:✱121·35 -/
/- PM-VERBATIM-BEGIN PM2:✱121·351
✱121·351. ⊢ : P∈Cls→1.Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_{μ+_cν}
PM-VERBATIM-END PM2:✱121·351 -/
/- PM-VERBATIM-BEGIN PM2:✱121·352
✱121·352. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_{μ+_cν}
PM-VERBATIM-END PM2:✱121·352 -/
/- PM-VERBATIM-BEGIN PM2:✱121·36
✱121·36. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J.μ,ν∈NC induct .⊃. P_μ|P_ν=P_ν|P_μ
PM-VERBATIM-END PM2:✱121·36 -/
/- PM-VERBATIM-BEGIN PM2:✱121·361
✱121·361. ⊢ : P∈(1→Cls)∪(Cls→1).Ppo⊂J.μ,ν∈NC induct−ιʻ0 .⊃. P_μ|P_ν=P_ν|P_μ
PM-VERBATIM-END PM2:✱121·361 -/
/- PM-VERBATIM-BEGIN PM2:✱121·37
✱121·37. ⊢ : P∈Cls→1.y∈P(x⊢⊣z) .⊃. P(x⊢⊣z)=P(x⊢⊣y)∪P(y⊢⊣z)
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
PM-VERBATIM-END PM2:✱121·4 -/
/- PM-VERBATIM-BEGIN PM2:✱121·41
✱121·41. ⊢ : R∈Cls→1.R(z⊢⊣z)∈Cls induct .⊃. R(x⊢⊣z)∈Cls induct
PM-VERBATIM-END PM2:✱121·41 -/
/- PM-VERBATIM-BEGIN PM2:✱121·42
✱121·42. ⊢ : R∈Cls→1.∼(zRpo z) .⊃. R(x⊢⊣z)∈Cls induct
PM-VERBATIM-END PM2:✱121·42 -/
/- PM-VERBATIM-BEGIN PM2:✱121·43
✱121·43. ⊢ : R∈Cls→1.zRpo z .⊃. E!ι̌ʻ(R⃗ʻz∩R⃖∗ʻz)
PM-VERBATIM-END PM2:✱121·43 -/
/- PM-VERBATIM-BEGIN PM2:✱121·431
✱121·431. ⊢ : R∈Cls→1.zRpo z.a=ι̌ʻ(R⃗ʻz∩R⃖∗ʻz).α ...
PM-VERBATIM-END PM2:✱121·431 -/
/- PM-VERBATIM-BEGIN PM2:✱121·432
✱121·432. ⊢ : Hp ✱121·431 .⊃. S(z⊢⊣a)∈Cls induct
PM-VERBATIM-END PM2:✱121·432 -/
/- PM-VERBATIM-BEGIN PM2:✱121·433
✱121·433. ⊢ : Hp ✱121·431.z≠a .⊃. S(z⊢⊣a)=R⃖∗ʻz=R(z⊢⊣z)
PM-VERBATIM-END PM2:✱121·433 -/
/- PM-VERBATIM-BEGIN PM2:✱121·434
✱121·434. ⊢ : Hp ✱121·431.z=a .⊃. R⃖∗ʻz=R(z⊢⊣z)=ιʻz
PM-VERBATIM-END PM2:✱121·434 -/
/- PM-VERBATIM-BEGIN PM2:✱121·44
✱121·44. ⊢ : R∈Cls→1.zRpo z .⊃. R(z⊢⊣z)∈Cls induct
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
PM-VERBATIM-END PM2:✱121·48 -/
/- PM-VERBATIM-BEGIN PM2:✱121·481
✱121·481. ⊢ : R∈Cls→1 .⊃: NcʻR(x⊢⊣y)≤NcʻR(x⊢⊣z) .≡. interval inclusion
PM-VERBATIM-END PM2:✱121·481 -/
/- PM-VERBATIM-BEGIN PM2:✱121·5
✱121·5. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. finitary-level decomposition
PM-VERBATIM-END PM2:✱121·5 -/
/- PM-VERBATIM-BEGIN PM2:✱121·501
✱121·501. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J.∃!P .⊃. finitary-level uniqueness
PM-VERBATIM-END PM2:✱121·501 -/
/- PM-VERBATIM-BEGIN PM2:✱121·502
✱121·502. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. finitary-level exhaustion
PM-VERBATIM-END PM2:✱121·502 -/
/- PM-VERBATIM-BEGIN PM2:✱121·51
✱121·51. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. finid/fin characterization
PM-VERBATIM-END PM2:✱121·51 -/
/- PM-VERBATIM-BEGIN PM2:✱121·52
✱121·52. ⊢ : P∈(Cls→1)∪(1→Cls).Ppo⊂J .⊃. ṡʻfinidʻP=P∗
PM-VERBATIM-END PM2:✱121·52 -/
/- PM-VERBATIM-BEGIN PM2:✱121·6
✱121·6. ⊢ : ν≠0 .⊃. f(ν_P) .≡. f[ι̌ʻŷ{N₀cʻP(BʻP⊢⊣y)=ν}]
PM-VERBATIM-END PM2:✱121·6 -/
/- PM-VERBATIM-BEGIN PM2:✱121·601
✱121·601. ⊢ : E!BʻP .⊃. BʻP=1_P.∼{(BʻP)Ppo(BʻP)}
PM-VERBATIM-END PM2:✱121·601 -/
/- PM-VERBATIM-BEGIN PM2:✱121·602
✱121·602. ⊢ : E!BʻP.P∈1→1 .⊃. P̌ʻBʻP=2_P
PM-VERBATIM-END PM2:✱121·602 -/
/- PM-VERBATIM-BEGIN PM2:✱121·61
✱121·61. ⊢ : P∈1→Cls.Ppo⊂J.x∈sʻgenʻP .⊃. generator rank characterization
PM-VERBATIM-END PM2:✱121·61 -/
/- PM-VERBATIM-BEGIN PM2:✱121·62
✱121·62. ⊢ : P∈Cls→1.Ppo⊂J.(BʻP)P∗x .⊃. rank characterization
PM-VERBATIM-END PM2:✱121·62 -/
/- PM-VERBATIM-BEGIN PM2:✱121·63
✱121·63. ⊢ : E!ν_P .⊃. N₀cʻP(BʻP⊢⊣ν_P)=ν
PM-VERBATIM-END PM2:✱121·63 -/
/- PM-VERBATIM-BEGIN PM2:✱121·631
✱121·631. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0 .⊃. ν_P rank properties
PM-VERBATIM-END PM2:✱121·631 -/
/- PM-VERBATIM-BEGIN PM2:✱121·632
✱121·632. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0.y=ν_P.yPz .⊃. successor property
PM-VERBATIM-END PM2:✱121·632 -/
/- PM-VERBATIM-BEGIN PM2:✱121·633
✱121·633. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0.ν_P∈DʻP .⊃. predecessor property
PM-VERBATIM-END PM2:✱121·633 -/
/- PM-VERBATIM-BEGIN PM2:✱121·634
✱121·634. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0 .⊃. ν_P domain characterization
PM-VERBATIM-END PM2:✱121·634 -/
/- PM-VERBATIM-BEGIN PM2:✱121·635
✱121·635. ⊢ : P∈Cls→1.Ppo⊂J.E!ν_P .⊃. ν∈NC induct−ιʻ0
PM-VERBATIM-END PM2:✱121·635 -/
/- PM-VERBATIM-BEGIN PM2:✱121·636
✱121·636. ⊢ : P∈Cls→1.Ppo⊂J.E!ν_P.∼E!(ν+_c1)_P .⊃. terminal-rank property
PM-VERBATIM-END PM2:✱121·636 -/
/- PM-VERBATIM-BEGIN PM2:✱121·637
✱121·637. ⊢ : E!ν_P .⊃. ν_P∈CʻP
PM-VERBATIM-END PM2:✱121·637 -/
/- PM-VERBATIM-BEGIN PM2:✱121·638
✱121·638. ⊢ : E!(ν+_c1)_P .⊃: (BʻP)P_νx .≡. x=(ν+_c1)_P : (ν+_c1)−_c1=ν
PM-VERBATIM-END PM2:✱121·638 -/
/- PM-VERBATIM-BEGIN PM2:✱121·641
✱121·641. ⊢ : P∈Cls→1.Ppo⊂J.ν∈NC induct−ιʻ0 .⊃. rank equivalences
PM-VERBATIM-END PM2:✱121·641 -/
/- PM-VERBATIM-BEGIN PM2:✱121·65
✱121·65. ⊢ : P∈Cls→1.Ppo⊂J.μ≠0.E!(μ+_cν)_P .⊃. μ_P P_ν (μ+_cν)_P
PM-VERBATIM-END PM2:✱121·65 -/
/- PM-VERBATIM-BEGIN PM2:✱121·66
✱121·66. ⊢ : P∈Cls→1.Ppo⊂J.NcʻP(BʻP⊢⊣x)>ν .⊃. x∈ᗡʻP_ν
PM-VERBATIM-END PM2:✱121·66 -/
/- PM-VERBATIM-BEGIN PM2:✱121·7
✱121·7. ⊢ : R∈1→1.aBR.aR∗x .⊃. R⃗∗ʻx=R(a⊢⊣x).R⃗∗ʻx∈Cls induct
PM-VERBATIM-END PM2:✱121·7 -/
/- PM-VERBATIM-BEGIN PM2:✱121·71
✱121·71. ⊢ : R∈1→1 : x∈sʻgenʻR ∨ (∃y).y∈R⃡∗ʻx.yRpo y :⊃. structural property
PM-VERBATIM-END PM2:✱121·71 -/
/- PM-VERBATIM-BEGIN PM2:✱121·72
✱121·72. ⊢ : R∈1→1.R⃗∗ʻx∼∈Cls induct .⊃. terminal structural property
PM-VERBATIM-END PM2:✱121·72 -/
