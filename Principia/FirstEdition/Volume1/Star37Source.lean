/- PM-VERBATIM-BEGIN PM1:✱37·01
✱37·01. Rʻʻβ=x̂{(∃ y).y∈ β.xRy} Df
✱37·01. Rʻʻ\beta=\hat{x}\{(\exists y).y\in \beta.xRy\} \quad\text{Df}
PM-VERBATIM-END PM1:✱37·01 -/
/- PM-VERBATIM-BEGIN PM1:✱37·02
✱37·02. R_∈=α̂β̂(α=Rʻʻβ) Df
✱37·02. R_{\in}=\hat{\alpha}\hat{\beta}(\alpha=Rʻʻ\beta) \quad\text{Df}
PM-VERBATIM-END PM1:✱37·02 -/
/- PM-VERBATIM-BEGIN PM1:✱37·03
✱37·03. Ř_∈=CnvʻR_∈ Df
✱37·03. \breve{R}_{\in}=\text{Cnv}ʻR_{\in} \quad\text{Df}
PM-VERBATIM-END PM1:✱37·03 -/
/- PM-VERBATIM-BEGIN PM1:✱37·04
✱37·04. Rʻʻʻκ=R_∈ʻʻκ Df
✱37·04. Rʻʻʻ\kappa=R_{\in}ʻʻ\kappa \quad\text{Df}
PM-VERBATIM-END PM1:✱37·04 -/
/- PM-VERBATIM-BEGIN PM1:✱37·05
✱37·05. E‼Rʻʻβ.=:y∈ β.⊃y.E!Rʻy Df
✱37·05. \text{E}‼Rʻʻ\beta.=:y\in \beta.\supset_{y}.\text{E}!Rʻy \quad\text{Df}
PM-VERBATIM-END PM1:✱37·05 -/
/- PM-VERBATIM-BEGIN PM1:✱37·33
✱37·33. ⊢.(P| Q)ʻʻγ=PʻʻQʻʻγ
✱37·33. \vdash.(P\mid Q)ʻʻ\gamma=PʻʻQʻʻ\gamma
PM-VERBATIM-END PM1:✱37·33 -/
/- PM-VERBATIM-BEGIN PM1:✱37·401
✱37·401. ⊢.Dʻ(R↾ β)=Rʻʻβ [Similar proof]
✱37·401. \vdash.\text{D}ʻ(R\upharpoonright \beta)=Rʻʻ\beta \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·401 -/
/- PM-VERBATIM-BEGIN PM1:✱37·412
✱37·412. ⊢.(R↾ α)ʻʻβ=Rʻʻ(α∩ β)
✱37·412. \vdash.(R\upharpoonright \alpha)ʻʻ\beta=Rʻʻ(\alpha\cap \beta)
PM-VERBATIM-END PM1:✱37·412 -/
/- PM-VERBATIM-BEGIN PM1:✱37·41
✱37·41. ⊢.Dʻ(R⥏α)=α∩ Rʻʻα.ᗡʻ(R⥏α)=α∩ Řʻʻα [*37·402.*36·11]
✱37·41. \vdash.\text{D}ʻ(R\unicode{x0294f}\alpha)=\alpha\cap Rʻʻ\alpha.\text{ᗡ}ʻ(R\unicode{x0294f}\alpha)=\alpha\cap \breve{R}ʻʻ\alpha \quad[\text{*37·402.*36·11}]
PM-VERBATIM-END PM1:✱37·41 -/
/- PM-VERBATIM-BEGIN PM1:✱37·6
✱37·6. ⊢:E‼Rʻʻβ.⊃.Rʻʻβ=x̂{(∃ y).y∈ β.x=Rʻy}
✱37·6. \vdash:\text{E}‼Rʻʻ\beta.\supset.Rʻʻ\beta=\hat{x}\{(\exists y).y\in \beta.x=Rʻy\}
PM-VERBATIM-END PM1:✱37·6 -/
/- PM-VERBATIM-BEGIN PM1:✱37·15
✱37·15. ⊢.Rʻʻα⊂ DʻR
✱37·15. \vdash.Rʻʻ\alpha\subset \text{D}ʻR
PM-VERBATIM-END PM1:✱37·15 -/
/- PM-VERBATIM-BEGIN PM1:✱37·16
✱37·16. ⊢.Řʻʻα⊂ ᗡʻR [*37·15 Ř/R.*33·2 ]
✱37·16. \vdash.\breve{R}ʻʻ\alpha\subset \text{ᗡ}ʻR \quad\left[\text{*37·15}\, \frac{\breve{R}}{R}.\text{*33·2}\right]
PM-VERBATIM-END PM1:✱37·16 -/
/- PM-VERBATIM-BEGIN PM1:✱37·2
✱37·2. ⊢:α⊂ β.⊃.Pʻʻα⊂ Pʻʻβ
Dem.
⊢.*22·1.⊃⊢:. Hp. ⊃:y∈ α.⊃y.y∈ β:
[*10·31] ⊃:y∈ α.xPy.⊃y.y∈ β.xPy:
[*10·28] ⊃:(∃ y).y∈ α.xPy.⊃.(∃ y).y∈ β.xPy:
[*37·1] ⊃:x∈ α Pʻʻα.⊃.x∈ Pʻʻβ:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·2 -/
/- PM-VERBATIM-BEGIN PM1:✱37·22
✱37·22. ⊢.Pʻʻ(α∪ β)=Pʻʻα∪ Pʻʻβ
Dem.
⊢.*37·1.⊃⊢:. x∈ Pʻʻ(α∪ β). ≡:(∃ y).y∈ α∪ β.xPy:
[*22·34] ≡:(∃ y):y∈ α.∨ .y∈ β:xPy:
[*4·4] ≡:(∃ y):y∈ α.xPy.∨ .y∈ β.xPy:
[*10·42] ≡:(∃ y).y∈ α.xPy:∨ :(∃ y).y∈ β.xPy:
[*37·1] ≡:x∈ Pʻʻα.∨ .x∈ Pʻʻβ:
[*22·34] ≡:x∈ Pʻʻα∪ Pʻʻβ:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·22 -/
/- PM-VERBATIM-BEGIN PM1:✱37·25
✱37·25. ⊢.DʻR=RʻʻᗡʻR.ᗡʻR=ŘʻʻDʻR
Dem.
⊢.*33·13. ⊃⊢:x∈ DʻR. ≡.(∃ y).xRy.
[*33·14.*4·71] ≡.(∃ y).y∈ ᗡʻR.xRy.
[*37·1] ≡.x∈ RʻʻᗡʻR (1)
⊢.*33·131.⊃⊢:y∈ ᗡʻR. ≡.(∃ x).xRy.
[*33·14.*4·71] ≡.(∃ x).x∈ DʻR.xRy.
[*37·105] ≡.y∈ ŘʻʻDʻR (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·25 -/
/- PM-VERBATIM-BEGIN PM1:✱37·26
✱37·26. ⊢.Rʻʻβ=Rʻʻ(β∩ ᗡʻR)
Dem.
⊢.*37·1.⊃⊢:. x∈ Rʻʻβ. ≡:(∃ y).y∈ β.xRy:
[*33·14.*4·71] ≡:(∃ y).y∈ β.y∈ ᗡʻR.xRy:
[*22·33] ≡:(∃ y).y∈ β∩ ᗡʻR.xRy:
[*37·1] ≡:x∈ Rʻʻ(β∩ ᗡʻR):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·26 -/
/- PM-VERBATIM-BEGIN PM1:✱37·265
✱37·265. ⊢.Rʻʻα=Rʻʻ(α∩ CʻR).Řʻʻα=Řʻʻ(α∩ CʻR)
✱37·265. \vdash.Rʻʻ\alpha=Rʻʻ(\alpha\cap CʻR).\breve{R}ʻʻ\alpha=\breve{R}ʻʻ(\alpha\cap CʻR)
PM-VERBATIM-END PM1:✱37·265 -/
/- PM-VERBATIM-BEGIN PM1:✱37·29
✱37·29. ⊢.RʻʻΛ=Λ.ŘʻΛ=Λ
✱37·29. \vdash.Rʻʻ\Lambda=\Lambda.\breve{R}ʻ\Lambda=\Lambda
PM-VERBATIM-END PM1:✱37·29 -/
/- PM-VERBATIM-BEGIN PM1:✱37·32
✱37·32. ⊢.Dʻ(P| Q)=PʻʻDʻQ. ᗡʻ(P| Q)=Q̌ʻʻᗡʻP
✱37·32. \vdash.\text{D}ʻ(P\mid Q)=Pʻʻ\text{D}ʻQ. \text{ᗡ}ʻ(P\mid Q)=\breve{Q}ʻʻ\text{ᗡ}ʻP
PM-VERBATIM-END PM1:✱37·32 -/
/- PM-VERBATIM-BEGIN PM1:✱37·45
✱37·45. ⊢:. (y).E!Rʻy.⊃:∃ !Rʻʻβ.≡.∃ !β [*33·431.*37·43]
✱37·45. \vdash\colon\ldotp (y).\text{E}!Rʻy.\supset:\exists !Rʻʻ\beta.\equiv.\exists !\beta \quad[\text{*33·431.*37·43}]
PM-VERBATIM-END PM1:✱37·45 -/
/- PM-VERBATIM-BEGIN PM1:✱37·46
✱37·46. ⊢:x∈ Rʻʻα.≡.∃ !α∩ R⃖ʻx [*37·1.*32·181]
✱37·46. \vdash:x\in Rʻʻ\alpha.\equiv.\exists !\alpha\cap \overleftarrow{R}ʻx \quad[\text{*37·1.*32·181}]
PM-VERBATIM-END PM1:✱37·46 -/
/- PM-VERBATIM-BEGIN PM1:✱37·61
✱37·61. ⊢:: E‼Rʻʻβ.⊃:. Rʻʻβ⊂α.≡:y∈ β.⊃y.Rʻy∈ α
✱37·61. \vdash\colon\colon \text{E}‼Rʻʻ\beta.\supset\colon\ldotp Rʻʻ\beta\subset\alpha.\equiv:y\in \beta.\supset_{y}.Rʻy\in \alpha
PM-VERBATIM-END PM1:✱37·61 -/
/- PM-VERBATIM-BEGIN PM1:✱37·62
✱37·62. ⊢:E!Rʻy.y∈ α.⊃.Rʻy∈ Rʻʻα
✱37·62. \vdash:\text{E}!Rʻy.y\in \alpha.\supset.Rʻy\in Rʻʻ\alpha
PM-VERBATIM-END PM1:✱37·62 -/
/- PM-VERBATIM-BEGIN PM1:✱37·63
✱37·63. ⊢:: E‼Rʻʻα.⊃:. x∈ Rʻʻα.⊃ₓ.ψ x:≡:y∈ α.⊃y.ψ(Rʻy)
✱37·63. \vdash\colon\colon \text{E}‼Rʻʻ\alpha.\supset\colon\ldotp x\in Rʻʻ\alpha.\supset_{x}.\psi x:\equiv:y\in \alpha.\supset_{y}.\psi(Rʻy)
PM-VERBATIM-END PM1:✱37·63 -/
/- PM-VERBATIM-BEGIN PM1:✱37·1
✱37·1. ⊢:x∈ Rʻʻβ.≡.(∃ y).y∈ β.xRy [*20·3.(*37·01)]
✱37·1. \vdash:x\in Rʻʻ\beta.\equiv.(\exists y).y\in \beta.xRy \quad[\text{*20·3.(*37·01)}]
PM-VERBATIM-END PM1:✱37·1 -/
/- PM-VERBATIM-BEGIN PM1:✱37·101
✱37·101. ⊢:α R_∈β.≡.α=Rʻʻβ [*21·3.(*37·02)]
✱37·101. \vdash:\alpha R_{\in}\beta.\equiv.\alpha=Rʻʻ\beta \quad[\text{*21·3.(*37·02)}]
PM-VERBATIM-END PM1:✱37·101 -/
/- PM-VERBATIM-BEGIN PM1:✱37·102
✱37·102. ⊢:α(Ř)_∈β.≡.α=Řʻʻβ [*37·101]
✱37·102. \vdash:\alpha(\breve{R})_{\in}\beta.\equiv.\alpha=\breve{R}ʻʻ\beta \quad[\text{*37·101}]
PM-VERBATIM-END PM1:✱37·102 -/
/- PM-VERBATIM-BEGIN PM1:✱37·103
✱37·103. ⊢:α∈ Rʻʻʻκ.≡.(∃ β).β∈ κ.α=Rʻʻβ.≡.α∈ R_∈ʻʻκ [*37·1·101.(*37·04)]
✱37·103. \[\begin{align}&\vdash:\alpha\in Rʻʻʻ\kappa.\equiv.(\exists \beta).\beta\in \kappa.\alpha=Rʻʻ\beta.\equiv.\alpha\in R_{\in}ʻʻ\kappa\\ &[\text{*37·1·101.(*37·04)}]\end{align}\]
PM-VERBATIM-END PM1:✱37·103 -/
/- PM-VERBATIM-BEGIN PM1:✱37·104
✱37·104. ⊢:. E‼Rʻʻβ.≡:y∈ β.⊃y.E!Rʻy [*4·2.(*37·05)]
✱37·104. \vdash\colon\ldotp \text{E}‼Rʻʻ\beta.\equiv:y\in \beta.\supset_{y}.\text{E}!Rʻy \quad[\text{*4·2.(*37·05)}]
PM-VERBATIM-END PM1:✱37·104 -/
/- PM-VERBATIM-BEGIN PM1:✱37·105
✱37·105. ⊢:x∈ Řʻʻβ.≡.(∃ y).y∈ β.yRx [*37·1.*31·11]
✱37·105. \vdash:x\in \breve{R}ʻʻ\beta.\equiv.(\exists y).y\in \beta.yRx \quad[\text{*37·1.*31·11}]
PM-VERBATIM-END PM1:✱37·105 -/
/- PM-VERBATIM-BEGIN PM1:✱37·106
✱37·106. ⊢:. E!Rʻx.⊃:x∈ Řʻʻβ.≡.Rʻx∈ β
✱37·106. \vdash\colon\ldotp \text{E}!Rʻx.\supset:x\in \breve{R}ʻʻ\beta.\equiv.Rʻx\in \beta
PM-VERBATIM-END PM1:✱37·106 -/
/- PM-VERBATIM-BEGIN PM1:✱37·11
✱37·11. ⊢.R_∈ʻβ=Rʻʻβ [*37·101.*30·3]
✱37·11. \vdash.R_{\in}ʻ\beta=Rʻʻ\beta \quad[\text{*37·101.*30·3}]
PM-VERBATIM-END PM1:✱37·11 -/
/- PM-VERBATIM-BEGIN PM1:✱37·111
✱37·111. ⊢.E!R_∈ʻβ [*37·11.*14·21]
✱37·111. \vdash.\text{E}!R_{\in}ʻ\beta \quad[\text{*37·11.*14·21}]
PM-VERBATIM-END PM1:✱37·111 -/
/- PM-VERBATIM-BEGIN PM1:✱37·12
✱37·12. ⊢:(β).Rʻʻβ=Qʻβ.≡.R_∈=Q [*30·42.*37·111·11]
✱37·12. \vdash:(\beta).Rʻʻ\beta=Qʻ\beta.\equiv.R_{\in}=Q \quad[\text{*30·42.*37·111·11}]
PM-VERBATIM-END PM1:✱37·12 -/
/- PM-VERBATIM-BEGIN PM1:✱37·13
✱37·13. ⊢:P=Q.⊃.Pʻʻβ=Qʻʻβ
✱37·13. \vdash:P=Q.\supset.Pʻʻ\beta=Qʻʻ\beta
PM-VERBATIM-END PM1:✱37·13 -/
/- PM-VERBATIM-BEGIN PM1:✱37·131
✱37·131. ⊢:P=Q.⊃.P_∈=Q_∈
✱37·131. \vdash:P=Q.\supset.P_{\in}=Q_{\in}
PM-VERBATIM-END PM1:✱37·131 -/
/- PM-VERBATIM-BEGIN PM1:✱37·14
✱37·14. ⊢:P=Q.≡.P_∈=Q_∈
✱37·14. \vdash:P=Q.\equiv.P_{\in}=Q_{\in}
PM-VERBATIM-END PM1:✱37·14 -/
/- PM-VERBATIM-BEGIN PM1:✱37·17
✱37·17. ⊢:. Rʻʻβ⊂ α.≡:y∈ β.xRy.⊃ₓ,y.x∈ α
✱37·17. \vdash\colon\ldotp Rʻʻ\beta\subset \alpha.\equiv:y\in \beta.xRy.\supset_{x,y}.x\in \alpha
PM-VERBATIM-END PM1:✱37·17 -/
/- PM-VERBATIM-BEGIN PM1:✱37·171
✱37·171. ⊢:. Řʻʻα⊂ β.≡:x∈ α.xRy.⊃ₓ,y.y∈ β
✱37·171. \vdash\colon\ldotp \breve{R}ʻʻ\alpha\subset \beta.\equiv:x\in \alpha.xRy.\supset_{x,y}.y\in \beta
PM-VERBATIM-END PM1:✱37·171 -/
/- PM-VERBATIM-BEGIN PM1:✱37·18
✱37·18. ⊢:y∈ β.⊃.R⃗ʻy⊂ Rʻʻβ
✱37·18. \vdash:y\in \beta.\supset.\overrightarrow{R}ʻy\subset Rʻʻ\beta
PM-VERBATIM-END PM1:✱37·18 -/
/- PM-VERBATIM-BEGIN PM1:✱37·181
✱37·181. ⊢:x∈ α.⊃.R⃖ʻx⊂ Řʻʻα [Proof as in *37·18]
✱37·181. \vdash:x\in \alpha.\supset.\overleftarrow{R}ʻx\subset \breve{R}ʻʻ\alpha \quad[\text{Proof as in *37·18}]
PM-VERBATIM-END PM1:✱37·181 -/
/- PM-VERBATIM-BEGIN PM1:✱37·201
✱37·201. ⊢:P⪽Q.⊃.Pʻʻα⊂ Qʻʻα [Similar proof]
✱37·201. \vdash:P\unicode{x2abd}Q.\supset.Pʻʻ\alpha\subset Qʻʻ\alpha \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·201 -/
/- PM-VERBATIM-BEGIN PM1:✱37·202
✱37·202. ⊢:a⊂ β.P⪽Q.⊃.Pʻʻα⊂ Qʻʻβ [*37·2·201]
✱37·202. \vdash:a\subset \beta.P\unicode{x2abd}Q.\supset.Pʻʻ\alpha\subset Qʻʻ\beta \quad[\text{*37·2·201}]
PM-VERBATIM-END PM1:✱37·202 -/
/- PM-VERBATIM-BEGIN PM1:✱37·21
✱37·21. ⊢.Pʻʻ(α∩ β)⊂ Pʻʻα∩ Pʻʻβ
Dem.
⊢.*37·1.⊃⊢:. x∈ Pʻʻ(α∩ β). ≡:(∃ y).y∈ α∩ β.xPy:
[*22·33] ≡:(∃ y).y∈ α.y∈ β.xPy:
[*10·5] ⊃:(∃ y).y∈ α.xPy:(∃ y).y∈ β.xPy:
[*37·1] ⊃:x∈ Pʻʻα.x∈ Pʻʻβ:
[*22·33] ⊃:x∈ Pʻʻα∩ Pʻʻβ:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·21 -/
/- PM-VERBATIM-BEGIN PM1:✱37·211
✱37·211. ⊢.(P∩̇Q)ʻʻα⊂ Pʻʻα∩ Qʻʻα [Similar proof]
✱37·211. \vdash.(P\dot{\cap}Q)ʻʻ\alpha\subset Pʻʻ\alpha\cap Qʻʻ\alpha \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·211 -/
/- PM-VERBATIM-BEGIN PM1:✱37·212
✱37·212. ⊢.(P∩̇Q)ʻʻ(α∩ β)⊂ Pʻʻα∩ Pʻʻβ∩ Qʻʻα∩ Qʻʻβ [*37·21·211]
✱37·212. \vdash.(P\dot{\cap}Q)ʻʻ(\alpha\cap \beta)\subset Pʻʻ\alpha\cap Pʻʻ\beta\cap Qʻʻ\alpha\cap Qʻʻ\beta \quad[\text{*37·21·211}]
PM-VERBATIM-END PM1:✱37·212 -/
/- PM-VERBATIM-BEGIN PM1:✱37·221
✱37·221. ⊢.(P⊍Q)ʻʻα=Pʻʻα∪ Qʻʻα [Similar proof]
✱37·221. \vdash.(P\unicode{x228d}Q)ʻʻ\alpha=Pʻʻ\alpha\cup Qʻʻ\alpha \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·221 -/
/- PM-VERBATIM-BEGIN PM1:✱37·222
✱37·222. ⊢.(P⊍Q)ʻʻ(α∪ β)=Pʻʻα∪ Pʻʻβ∪ Qʻʻα∪ Qʻʻβ [*37·22·221]
✱37·222. \vdash.(P\unicode{x228d}Q)ʻʻ(\alpha\cup \beta)=Pʻʻ\alpha\cup Pʻʻ\beta\cup Qʻʻ\alpha\cup Qʻʻ\beta \quad[\text{*37·22·221}]
PM-VERBATIM-END PM1:✱37·222 -/
/- PM-VERBATIM-BEGIN PM1:✱37·23
✱37·23. ⊢.DʻR_∈=α̂{(∃ β).α=Rʻʻβ} [*37·101.*33·11]
✱37·23. \vdash.DʻR_{\in}=\hat{\alpha}\{(\exists \beta).\alpha=Rʻʻ\beta\} \quad[\text{*37·101.*33·11}]
PM-VERBATIM-END PM1:✱37·23 -/
/- PM-VERBATIM-BEGIN PM1:✱37·231
✱37·231. ⊢.ᗡʻR_∈=Cls
Dem.
⊢.*37·101. ⊃⊢:α R_∈ẑ(φ!z).≡.α=Rʻʻẑ(φ!z):
[*10·11·281] ⊃⊢:(∃ α).α R_∈ẑ(φ!z).≡.(∃ α).α=Rʻʻẑ(φ!z):
[*33·131] ⊃⊢:ẑ(φ!z)∈ ᗡʻR_∈.≡.(∃ α).α=Rʻʻẑ(φ!z) (1)
⊢.*20·2.(*37·01). ⊃⊢:x̂(∃ y).y∈ ẑ(φ!z).xRy=Rʻʻẑ(φ!z):
[*10·11·24] ⊃⊢:(φ):(∃ α).α=Rʻʻẑ(φ!z) (2)
⊢.(1).(2).*2·02. ⊃⊢:ẑ(φ!z)∈ Cls.⊃.ẑ(φ!z)∈ ᗡʻR_∈ (3)
⊢.*20·41.*2·02. ⊃⊢:ẑ(φ!z)∈ ᗡʻR_∈.⊃.ẑ(φ!z)∈ Cls (4)
⊢.(3).(4). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·231 -/
/- PM-VERBATIM-BEGIN PM1:✱37·24
✱37·24. ⊢:α∈ DʻR_∈.⊃.α⊂ DʻR
Dem.
⊢.*33·13.*37·101.⊃⊢:: α∈ DʻR_∈. ≡:. (∃ β).α=Rʻʻβ:.
[*20·33.*37·1] ≡:. (∃ β):x∈ α.≡ₓ.(∃ y).y∈ β.xRy:.
[*11·61] ⊃:. x∈ α.⊃ₓ:(∃ β,y).y∈ β.xRy:
[*11·23] ⊃ₓ:(∃ x,β).y∈ β.xRy:
[*11·55] ⊃ₓ:(∃ y):xRy:(∃ β).y∈ β:
[*10·5] ⊃ₓ:(∃ y).xRy:
[*33·13] ⊃ₓ:x∈ DʻR:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·24 -/
/- PM-VERBATIM-BEGIN PM1:✱37·261
✱37·261. ⊢.Řʻʻβ=Řʻʻ(β∩ DʻR) [*37·26.*33·21]
✱37·261. \vdash.\breve{R}ʻʻ\beta=\breve{R}ʻʻ(\beta\cap \text{D}ʻR) \quad[\text{*37·26.*33·21}]
PM-VERBATIM-END PM1:✱37·261 -/
/- PM-VERBATIM-BEGIN PM1:✱37·262
✱37·262. ⊢:α∩ ᗡʻR=β∩ ᗡʻR.⊃.Rʻʻα=Rʻʻβ [*37·26]
✱37·262. \vdash:\alpha\cap \text{ᗡ}ʻR=\beta\cap \text{ᗡ}ʻR.\supset.Rʻʻ\alpha=Rʻʻ\beta \quad[\text{*37·26}]
PM-VERBATIM-END PM1:✱37·262 -/
/- PM-VERBATIM-BEGIN PM1:✱37·263
✱37·263. ⊢:α∩ DʻR=β∩ DʻR.⊃.Řʻʻα=Řʻʻβ [*37·261]
✱37·263. \vdash:\alpha\cap \text{D}ʻR=\beta\cap \text{D}ʻR.\supset.\breve{R}ʻʻ\alpha=\breve{R}ʻʻ\beta \quad[\text{*37·261}]
PM-VERBATIM-END PM1:✱37·263 -/
/- PM-VERBATIM-BEGIN PM1:✱37·264
✱37·264. ⊢:∃ !α∩ Rʻʻβ.≡.(∃ x,y).x∈ α.y∈ β.xRy.≡.∃ !β∩ Řʻʻα
Dem.
⊢.*22·33.*37·1.⊃⊢:. ∃ !α∩ Rʻʻβ. ≡:(∃ x):x∈ α:(∃ y).y∈ β.xRy: (1)
[*11·55] ≡:(∃ x,y).x∈ α.y∈ β.xRy (2)
⊢.(1).*11·6. ⊃⊢:. ∃ !α∩ Rʻʻβ. ≡:(∃ y):y∈ β:(∃ x).x∈ α.xRy:
[*37·105] ≡:(∃ y).y∈ β.y∈ Řʻʻα:
[*22·33] ≡:∃ !β∩ Řʻʻα (3)
⊢.(2).(3).⊃⊢.Prop
PM-VERBATIM-END PM1:✱37·264 -/
/- PM-VERBATIM-BEGIN PM1:✱37·27
✱37·27. ⊢:ᗡʻR⊂ β.⊃.DʻR=Rʻʻβ [*22·621.*37·25·26]
✱37·27. \vdash:\text{ᗡ}ʻR\subset \beta.\supset.\text{D}ʻR=Rʻʻ\beta \quad[\text{*22·621.*37·25·26}]
PM-VERBATIM-END PM1:✱37·27 -/
/- PM-VERBATIM-BEGIN PM1:✱37·271
✱37·271. ⊢:DʻR⊂ α.⊃.ᗡʻR=Řʻʻα [*22·621.*37·25·261]
✱37·271. \vdash:\text{D}ʻR\subset \alpha.\supset.\text{ᗡ}ʻR=\breve{R}ʻʻ\alpha \quad[\text{*22·621.*37·25·261}]
PM-VERBATIM-END PM1:✱37·271 -/
/- PM-VERBATIM-BEGIN PM1:✱37·28
✱37·28. ⊢.RʻʻV=DʻR.ŘʻʻV=ᗡʻR [*37·27·271.*24·11]
✱37·28. \vdash.Rʻʻ\text{V}=\text{D}ʻR.\breve{R}ʻʻ\text{V}=\text{ᗡ}ʻR \quad[\text{*37·27·271.*24·11}]
PM-VERBATIM-END PM1:✱37·28 -/
/- PM-VERBATIM-BEGIN PM1:✱37·3
✱37·3. ⊢.{sgʻ(P| Q)}ʻz=PʻʻQ⃗ʻz
✱37·3. \vdash.\{\text{sg}ʻ(P\mid Q)\}ʻz=Pʻʻ\overrightarrow{Q}ʻz
PM-VERBATIM-END PM1:✱37·3 -/
/- PM-VERBATIM-BEGIN PM1:✱37·301
✱37·301. ⊢.{gsʻ(P| Q)}ʻx=Q̌ʻʻP⃖ʻx [Similar proof]
✱37·301. \vdash.\{\text{gs}ʻ(P\mid Q)\}ʻx=\breve{Q}ʻʻ\overleftarrow{P}ʻx \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·301 -/
/- PM-VERBATIM-BEGIN PM1:✱37·302
✱37·302. ⊢:R=P| Q.⊃.R⃗ʻz=PʻʻQ⃗ʻz.R⃖ʻx=Q̌ʻʻP⃖ʻx [*37·3·301.*32·23·231·16]
✱37·302. \[\begin{align}&\vdash:R=P\mid Q.\supset.\overrightarrow{R}ʻz=Pʻʻ\overrightarrow{Q}ʻz.\overleftarrow{R}ʻx=\breve{Q}ʻʻ\overleftarrow{P}ʻx\\ &[\text{*37·3·301.*32·23·231·16}]\end{align}\]
PM-VERBATIM-END PM1:✱37·302 -/
/- PM-VERBATIM-BEGIN PM1:✱37·31
✱37·31. ⊢.sgʻ(P| Q)=P_∈| Q⃗
✱37·31. \vdash.\text{sg}ʻ(P\mid Q)=P_{\in}\mid \overrightarrow{Q}
PM-VERBATIM-END PM1:✱37·31 -/
/- PM-VERBATIM-BEGIN PM1:✱37·311
✱37·311. ⊢.gsʻ(P| Q)=(Q̌_∈| P⃖ [Similar proof]
✱37·311. \vdash.\text{gs}ʻ(P\mid Q)=(\breve{Q}_{\in}\mid \overleftarrow{P} \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·311 -/
/- PM-VERBATIM-BEGIN PM1:✱37·321
✱37·321. ⊢:ᗡʻP⊂DʻQ.⊃.Dʻ(P| Q)=DʻP [*37·32·27]
✱37·321. \vdash:\text{ᗡ}ʻP\subset\text{D}ʻQ.\supset.\text{D}ʻ(P\mid Q)=\text{D}ʻP \quad[\text{*37·32·27}]
PM-VERBATIM-END PM1:✱37·321 -/
/- PM-VERBATIM-BEGIN PM1:✱37·322
✱37·322. ⊢:DʻQ⊂ᗡʻP.⊃.ᗡʻ(P| Q)=ᗡʻQ [*37·32·271]
✱37·322. \vdash:\text{D}ʻQ\subset\text{ᗡ}ʻP.\supset.\text{ᗡ}ʻ(P\mid Q)=\text{ᗡ}ʻQ \quad[\text{*37·32·271}]
PM-VERBATIM-END PM1:✱37·322 -/
/- PM-VERBATIM-BEGIN PM1:✱37·323
✱37·323. ⊢:ᗡʻP=DʻQ.⊃.Dʻ(P| Q)=DʻP.ᗡʻ(P| Q)=ᗡʻQ [*37·321·322]
✱37·323. \vdash:\text{ᗡ}ʻP=\text{D}ʻQ.\supset.\text{D}ʻ(P\mid Q)=\text{D}ʻP.\text{ᗡ}ʻ(P\mid Q)=\text{ᗡ}ʻQ \quad[\text{*37·321·322}]
PM-VERBATIM-END PM1:✱37·323 -/
/- PM-VERBATIM-BEGIN PM1:✱37·34
✱37·34. ⊢.(P| Q)_∈=P_∈| Q_∈
✱37·34. \vdash.(P\mid Q)_{\in}=P_{\in}\mid Q_{\in}
PM-VERBATIM-END PM1:✱37·34 -/
/- PM-VERBATIM-BEGIN PM1:✱37·341
✱37·341. ⊢.Cnvʻ(P| Q)_∈=(Q̌)_∈| (P̌)_∈ [*34·2.*37·34]
✱37·341. \vdash.{\text{Cnv}ʻ(P\mid Q)}_{\in}=(\breve{Q})_{\in}\mid (\breve{P})_{\in} \quad[\text{*34·2.*37·34}]
PM-VERBATIM-END PM1:✱37·341 -/
/- PM-VERBATIM-BEGIN PM1:✱37·35
✱37·35. ⊢:(z).Rʻz=PʻQʻz.⊃.(γ).Rʻʻγ=PʻʻQʻʻγ
✱37·35. \vdash:(z).Rʻz=PʻQʻz.\supset.(\gamma).Rʻʻ\gamma=PʻʻQʻʻ\gamma
PM-VERBATIM-END PM1:✱37·35 -/
/- PM-VERBATIM-BEGIN PM1:✱37·351
✱37·351. ⊢:(α).Rʻα=PʻQʻʻα.⊃.(κ).Rʻʻκ=PʻʻQʻʻʻκ [*37·35 Q_∈/Q.*37·11.(*37·04) ]
✱37·351. \[\begin{align}&\vdash:(\alpha).Rʻ\alpha=PʻQʻʻ\alpha.\supset.(\kappa).Rʻʻ\kappa=PʻʻQʻʻʻ\kappa\\ &\left[\text{*37·35} \frac{Q_{\in}}{Q}.\text{*37·11.(*37·04)}\right]\end{align}\]
PM-VERBATIM-END PM1:✱37·351 -/
/- PM-VERBATIM-BEGIN PM1:✱37·352
✱37·352. ⊢:(α).Rʻʻα=PʻQʻʻα.⊃.(κ).Rʻʻʻκ=PʻʻQʻʻʻκ [*37·351 R_∈/R.*37·11.(*37·04) ]
✱37·352. \[\begin{align}&\vdash:(\alpha).Rʻʻ\alpha=PʻQʻʻ\alpha.\supset.(\kappa).Rʻʻʻ\kappa=PʻʻQʻʻʻ\kappa\\ &\left[\text{*37·351}\, \frac{R_{\in}}{R}.\text{*37·11.(*37·04)}\right]\end{align}\]
PM-VERBATIM-END PM1:✱37·352 -/
/- PM-VERBATIM-BEGIN PM1:✱37·353
✱37·353. ⊢:(z).RʻSʻz=PʻQʻz.⊃.(γ).RʻʻSʻʻγ=PʻʻQʻʻγ
✱37·353. \vdash:(z).RʻSʻz=PʻQʻz.\supset.(\gamma).RʻʻSʻʻ\gamma=PʻʻQʻʻ\gamma
PM-VERBATIM-END PM1:✱37·353 -/
/- PM-VERBATIM-BEGIN PM1:✱37·354
✱37·354. ⊢.(α).RʻSʻα=PʻQʻʻα.⊃.(κ).RʻʻSʻʻκ=PʻʻQʻʻʻκ [*37·353 Q_∈/Q ]
✱37·354. \vdash.(\alpha).RʻSʻ\alpha=PʻQʻʻ\alpha.\supset.(\kappa).RʻʻSʻʻ\kappa=PʻʻQʻʻʻ\kappa \quad\left[\text{*37·353}\, \frac{Q_{\in}}{Q}\right]
PM-VERBATIM-END PM1:✱37·354 -/
/- PM-VERBATIM-BEGIN PM1:✱37·355
✱37·355. ⊢:(z).RʻSʻz=PʻʻQʻz.⊃.(γ).RʻʻSʻʻγ=PʻʻʻQʻʻγ [*37·353 P_∈/P ]
✱37·355. \vdash:(z).RʻSʻz=PʻʻQʻz.\supset.(\gamma).RʻʻSʻʻ\gamma=PʻʻʻQʻʻ\gamma \quad\left[\text{*37·353}\, \frac{P_{\in}}{P}\right]
PM-VERBATIM-END PM1:✱37·355 -/
/- PM-VERBATIM-BEGIN PM1:✱37·36
✱37·36. ⊢.DʻR²=RʻʻDʻR.ᗡʻR²=ŘʻʻᗡʻR [*37·32]
✱37·36. \vdash.\text{D}ʻR^{2}=Rʻʻ\text{D}ʻR.\text{ᗡ}ʻR^{2}=\breve{R}ʻʻ\text{ᗡ}ʻR \quad[\text{*37·32}]
PM-VERBATIM-END PM1:✱37·36 -/
/- PM-VERBATIM-BEGIN PM1:✱37·37
✱37·37. ⊢.(R²)_∈=(R_∈)² [*37·34]
✱37·37. \vdash.(R^{2})_{\in}=(R_{\in})^{2} \quad[\text{*37·34}]
PM-VERBATIM-END PM1:✱37·37 -/
/- PM-VERBATIM-BEGIN PM1:✱37·371
✱37·371. R_∈²=(R_∈)² Df
✱37·371. R_{\in}^{2}=(R_{\in})^{2} \quad\text{Df}
PM-VERBATIM-END PM1:✱37·371 -/
/- PM-VERBATIM-BEGIN PM1:✱37·38
✱37·38. ⊢.R⃗²ʻx=RʻʻR⃗ʻx [*37·3]
✱37·38. \vdash.\overrightarrow{R}^{2}ʻx=Rʻʻ\overrightarrow{R}ʻx \quad[\text{*37·3}]
PM-VERBATIM-END PM1:✱37·38 -/
/- PM-VERBATIM-BEGIN PM1:✱37·39
✱37·39. ⊢.R²ʻʻα=RʻʻRʻʻα [*37·33]
✱37·39. \vdash.R^{2}ʻʻ\alpha=RʻʻRʻʻ\alpha \quad[\text{*37·33}]
PM-VERBATIM-END PM1:✱37·39 -/
/- PM-VERBATIM-BEGIN PM1:✱37·4
✱37·4. ⊢.ᗡʻ(α↿ R)=Řʻʻα
✱37·4. \vdash.\text{ᗡ}ʻ(\alpha\upharpoonleft R)=\breve{R}ʻʻ\alpha
PM-VERBATIM-END PM1:✱37·4 -/
/- PM-VERBATIM-BEGIN PM1:✱37·402
✱37·402. ⊢.Dʻ(α↿ R↾ β)=α∩ Rʻʻβ.ᗡʻ(α↿ R↾ β)=β∩ Řʻʻα
✱37·402. \vdash.\text{D}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\alpha\cap Rʻʻ\beta.\text{ᗡ}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\beta\cap \breve{R}ʻʻ\alpha
PM-VERBATIM-END PM1:✱37·402 -/
/- PM-VERBATIM-BEGIN PM1:✱37·411
✱37·411. ⊢.(α↿ R)ʻʻβ=Dʻ(α↿ R↾ β)=α∩ Rʻʻβ
✱37·411. \vdash.(\alpha\upharpoonleft R)ʻʻ\beta=\text{D}ʻ(\alpha\upharpoonleft R\upharpoonright \beta)=\alpha\cap Rʻʻ\beta
PM-VERBATIM-END PM1:✱37·411 -/
/- PM-VERBATIM-BEGIN PM1:✱37·413
✱37·413. ⊢.(R⥏α)ʻʻβ=α∩ Rʻʻ(α∩ β)
✱37·413. \vdash.(R\unicode{x0294f}\alpha)ʻʻ\beta=\alpha\cap Rʻʻ(\alpha\cap \beta)
PM-VERBATIM-END PM1:✱37·413 -/
/- PM-VERBATIM-BEGIN PM1:✱37·42
✱37·42. ⊢:Rʻʻβ⊂ α.⊃.(α↿ R)ʻʻβ=Rʻʻβ [*37·411.*22·621]
✱37·42. \vdash:Rʻʻ\beta\subset \alpha.\supset.(\alpha\upharpoonleft R)ʻʻ\beta=Rʻʻ\beta \quad[\text{*37·411.*22·621}]
PM-VERBATIM-END PM1:✱37·42 -/
/- PM-VERBATIM-BEGIN PM1:✱37·421
✱37·421. ⊢:β⊂ α.⊃.(R↾ α)ʻʻβ=Rʻʻβ [*37·412.*22·621]
✱37·421. \vdash:\beta\subset \alpha.\supset.(R\upharpoonright \alpha)ʻʻ\beta=Rʻʻ\beta \quad[\text{*37·412.*22·621}]
PM-VERBATIM-END PM1:✱37·421 -/
/- PM-VERBATIM-BEGIN PM1:✱37·43
✱37·43. ⊢:. β⊂ ᗡʻR.⊃:∃ !Rʻʻβ.≡.∃ !β
✱37·43. \vdash\colon\ldotp \beta\subset \text{ᗡ}ʻR.\supset:\exists !Rʻʻ\beta.\equiv.\exists !\beta
PM-VERBATIM-END PM1:✱37·43 -/
/- PM-VERBATIM-BEGIN PM1:✱37·431
✱37·431. ⊢:. α⊂ DʻR.⊃:∃ !Řʻʻα.≡.∃ !α [Proof as in *37·43]
✱37·431. \vdash\colon\ldotp \alpha\subset \text{D}ʻR.\supset:\exists !\breve{R}ʻʻ\alpha.\equiv.\exists !\alpha \quad[\text{Proof as in *37·43}]
PM-VERBATIM-END PM1:✱37·431 -/
/- PM-VERBATIM-BEGIN PM1:✱37·44
✱37·44. ⊢:. ᗡʻR=V.⊃:∃ !Rʻʻβ.≡.∃ !β [*37·43.*24·11]
✱37·44. \vdash\colon\ldotp \text{ᗡ}ʻR=V.\supset:\exists !Rʻʻ\beta.\equiv.\exists !\beta \quad[\text{*37·43.*24·11}]
PM-VERBATIM-END PM1:✱37·44 -/
/- PM-VERBATIM-BEGIN PM1:✱37·441
✱37·441. ⊢:. DʻR=V.⊃:∃ !Řʻʻα.≡.∃ !α [Proof as in *37·44]
✱37·441. \vdash\colon\ldotp \text{D}ʻR=V.\supset:\exists !\breve{R}ʻʻ\alpha.\equiv.\exists !\alpha \quad[\text{Proof as in *37·44}]
PM-VERBATIM-END PM1:✱37·441 -/
/- PM-VERBATIM-BEGIN PM1:✱37·451
✱37·451. ⊢:. (x).E!Řʻx.⊃:∃ !Řʻʻα.≡.∃ !α [Proof as in *37·45]
✱37·451. \vdash\colon\ldotp (x).\text{E}!\breve{R}ʻx.\supset:\exists !\breve{R}ʻʻ\alpha.\equiv.\exists !\alpha \quad[\text{Proof as in *37·45}]
PM-VERBATIM-END PM1:✱37·451 -/
/- PM-VERBATIM-BEGIN PM1:✱37·461
✱37·461. ⊢:x∼∈ Rʻʻα.≡.α∩ R⃖ʻx=Λ.≡.R⃖ʻx⊂ -α [*37·46.*24·311]
✱37·461. \vdash:x{\sim}\in Rʻʻ\alpha.\equiv.\alpha\cap \overleftarrow{R}ʻx=\Lambda.\equiv.\overleftarrow{R}ʻx\subset -\alpha \quad[\text{*37·46.*24·311}]
PM-VERBATIM-END PM1:✱37·461 -/
/- PM-VERBATIM-BEGIN PM1:✱37·462
✱37·462. ⊢:x∼∈ Řʻʻα.≡.α∩ R⃗ʻx=Λ.≡.R⃗ʻx⊂ -α [*37·461.*32·241]
✱37·462. \vdash:x{\sim}\in \breve{R}ʻʻ\alpha.\equiv.\alpha\cap \overrightarrow{R}ʻx=\Lambda.\equiv.\overrightarrow{R}ʻx\subset -\alpha \quad[\text{*37·461.*32·241}]
PM-VERBATIM-END PM1:✱37·462 -/
/- PM-VERBATIM-BEGIN PM1:✱37·47
✱37·47. ⊢:∃ !α.≡.∃ !Rʻʻʻα.≡.∃ !Řʻʻʻα
✱37·47. \vdash:\exists !\alpha.\equiv.\exists !Rʻʻʻ\alpha.\equiv.\exists !\breve{R}ʻʻʻ\alpha
PM-VERBATIM-END PM1:✱37·47 -/
/- PM-VERBATIM-BEGIN PM1:✱37·5
✱37·5. ⊢:(β).Pʻʻβ=Qʻβ.⊃.(κ).Pʻʻʻκ=Qʻʻκ
✱37·5. \vdash:(\beta).Pʻʻ\beta=Qʻ\beta.\supset.(\kappa).Pʻʻʻ\kappa=Qʻʻ\kappa
PM-VERBATIM-END PM1:✱37·5 -/
/- PM-VERBATIM-BEGIN PM1:✱37·501
✱37·501. ⊢.β∩ ᗡʻR⊂ ŘʻʻRʻʻβ
✱37·501. \vdash.\beta\cap \text{ᗡ}ʻR\subset \breve{R}ʻʻRʻʻ\beta
PM-VERBATIM-END PM1:✱37·501 -/
/- PM-VERBATIM-BEGIN PM1:✱37·502
✱37·502. ⊢.α∩ DʻR⊂ RʻʻŘʻʻα [Similar proof]
✱37·502. \vdash.\alpha\cap \text{D}ʻR\subset Rʻʻ\breve{R}ʻʻ\alpha \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·502 -/
/- PM-VERBATIM-BEGIN PM1:✱37·51
✱37·51. ⊢:β⊂ ᗡʻR.≡.β⊂ ŘʻʻRʻʻβ
✱37·51. \vdash:\beta\subset \text{ᗡ}ʻR.\equiv.\beta\subset \breve{R}ʻʻRʻʻ\beta
PM-VERBATIM-END PM1:✱37·51 -/
/- PM-VERBATIM-BEGIN PM1:✱37·52
✱37·52. ⊢:α⊂ DʻR.≡.α⊂ RʻʻŘʻʻα [Similar proof]
✱37·52. \vdash:\alpha\subset \text{D}ʻR.\equiv.\alpha\subset Rʻʻ\breve{R}ʻʻ\alpha \quad[\text{Similar proof}]
PM-VERBATIM-END PM1:✱37·52 -/
/- PM-VERBATIM-BEGIN PM1:✱37·601
✱37·601. ⊢:(x).E!Rʻx.⊃.RʻʻV=x̂{(∃ y).x=Rʻy}
✱37·601. \vdash:(x).\text{E}!Rʻx.\supset.Rʻʻ\text{V}=\hat{x}\{(\exists y).x=Rʻy\}
PM-VERBATIM-END PM1:✱37·601 -/
/- PM-VERBATIM-BEGIN PM1:✱37·64
✱37·64. ⊢:. E‼Rʻʻα.⊃:(∃ y).y∈ α.ψ(Rʻy).≡.(∃ x).x∈ Rʻʻα.ψ x
✱37·64. \vdash\colon\ldotp \text{E}‼Rʻʻ\alpha.\supset:(\exists y).y\in \alpha.\psi(Rʻy).\equiv.(\exists x).x\in Rʻʻ\alpha.\psi x
PM-VERBATIM-END PM1:✱37·64 -/
/- PM-VERBATIM-BEGIN PM1:✱37·65
✱37·65. ⊢:E‼Rʻʻβ.α⊂ Rʻʻβ.⊃.α=Rʻʻ(Řʻʻα∩ β)
✱37·65. \vdash:\text{E}‼Rʻʻ\beta.\alpha\subset Rʻʻ\beta.\supset.\alpha=Rʻʻ(\breve{R}ʻʻ\alpha\cap \beta)
PM-VERBATIM-END PM1:✱37·65 -/
/- PM-VERBATIM-BEGIN PM1:✱37·66
✱37·66. ⊢:. E‼Rʻʻβ.⊃:α⊂ Rʻʻβ.≡.(∃ γ).γ⊂ β.α=Rʻʻγ
✱37·66. \vdash\colon\ldotp \text{E}‼Rʻʻ\beta.\supset:\alpha\subset Rʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\alpha=Rʻʻ\gamma
PM-VERBATIM-END PM1:✱37·66 -/
/- PM-VERBATIM-BEGIN PM1:✱37·67
✱37·67. ⊢:. z∈ γ.⊃z.E!RʻSʻz:⊃. RʻʻSʻʻγ=x̂{(∃ z). z∈ γ. x=RʻSʻz}
✱37·67. \vdash\colon\ldotp z\in \gamma.\supset_{z}.\text{E}!RʻSʻz:\supset. RʻʻSʻʻ\gamma=\hat{x}\{(\exists z). z\in \gamma. x=RʻSʻz\}
PM-VERBATIM-END PM1:✱37·67 -/
/- PM-VERBATIM-BEGIN PM1:✱37·68
✱37·68. ⊢:. z∈ γ. ⊃z. PʻQʻz = Rʻz:⊃. PʻʻQʻʻγ = Rʻʻγ
✱37·68. \vdash\colon\ldotp z\in \gamma. \supset_{z}. PʻQʻz = Rʻz:\supset. PʻʻQʻʻ\gamma = Rʻʻ\gamma
PM-VERBATIM-END PM1:✱37·68 -/
/- PM-VERBATIM-BEGIN PM1:✱37·69
✱37·69. ⊢:. y∈ β. ⊃y. Rʻy = Sʻy: ⊃. Rʻʻβ = Sʻʻβ
✱37·69. \vdash\colon\ldotp y\in \beta. \supset_{y}. Rʻy = Sʻy: \supset. Rʻʻ\beta = Sʻʻ\beta
PM-VERBATIM-END PM1:✱37·69 -/
/- PM-VERBATIM-BEGIN PM1:✱37·7
✱37·7. ⊢. R⃗ʻʻβ=α̂{(∃ y) . y∈ β. α= R⃗ʻy} [*37·6 . *32·12]
✱37·7. \vdash. \overrightarrow{R}ʻʻ\beta=\hat{\alpha}\{(\exists y) . y\in \beta. \alpha= \overrightarrow{R}ʻy\} \quad[\text{*37·6 . *32·12}]
PM-VERBATIM-END PM1:✱37·7 -/
/- PM-VERBATIM-BEGIN PM1:✱37·701
✱37·701. ⊢. R⃖ʻʻα = β̂{(∃ x) . x∈ α. β= R⃖ʻx} [*37·6 . *32·121]
✱37·701. \vdash. \overleftarrow{R}ʻʻ\alpha = \hat{\beta}\{(\exists x) . x\in \alpha. \beta= \overleftarrow{R}ʻx\} \quad[\text{*37·6 . *32·121}]
PM-VERBATIM-END PM1:✱37·701 -/
/- PM-VERBATIM-BEGIN PM1:✱37·702
✱37·702. ⊢:. R⃗ʻʻβ⊂ κ.≡:y∈ β.⊃y.R⃗ʻy∈ κ [*37·61]
✱37·702. \vdash\colon\ldotp \overrightarrow{R}ʻʻ\beta\subset \kappa.\equiv:y\in \beta.\supset_{y}.\overrightarrow{R}ʻy\in \kappa \quad[\text{*37·61}]
PM-VERBATIM-END PM1:✱37·702 -/
/- PM-VERBATIM-BEGIN PM1:✱37·703
✱37·703. ⊢:. R⃖ʻʻβ⊂ κ.≡:x∈ β.⊃ₓ.R⃖ʻx∈ κ [*37·61]
✱37·703. \vdash\colon\ldotp \overleftarrow{R}ʻʻ\beta\subset \kappa.\equiv:x\in \beta.\supset_{x}.\overleftarrow{R}ʻx\in \kappa \quad[\text{*37·61}]
PM-VERBATIM-END PM1:✱37·703 -/
/- PM-VERBATIM-BEGIN PM1:✱37·704
✱37·704. ⊢:y∈ α.⊃.R⃗ʻy∈ R⃗ʻʻα [*37·62.*32·12]
✱37·704. \vdash:y\in \alpha.\supset.\overrightarrow{R}ʻy\in \overrightarrow{R}ʻʻ\alpha \quad[\text{*37·62.*32·12}]
PM-VERBATIM-END PM1:✱37·704 -/
/- PM-VERBATIM-BEGIN PM1:✱37·705
✱37·705. ⊢:x∈ α.⊃.R⃖ʻx∈ R⃖ʻʻα [*37·62.*32·121]
✱37·705. \vdash:x\in \alpha.\supset.\overleftarrow{R}ʻx\in \overleftarrow{R}ʻʻ\alpha \quad[\text{*37·62.*32·121}]
PM-VERBATIM-END PM1:✱37·705 -/
/- PM-VERBATIM-BEGIN PM1:✱37·706
✱37·706. ⊢:. α∈ R⃗ʻʻβ.⊃_α.ψα:≡:y∈ β.⊃y.ψ(R⃗ʻy) [*37·63]
✱37·706. \vdash\colon\ldotp \alpha\in \overrightarrow{R}ʻʻ\beta.\supset_{\alpha}.\psi\alpha:\equiv:y\in \beta.\supset_{y}.\psi(\overrightarrow{R}ʻy) \quad[\text{*37·63}]
PM-VERBATIM-END PM1:✱37·706 -/
/- PM-VERBATIM-BEGIN PM1:✱37·707
✱37·707. ⊢:. β∈ R⃖ʻʻα.⊃_β.ψβ:≡:x∈ α.⊃ₓ.ψ(R⃖ʻx) [*37·63]
✱37·707. \vdash\colon\ldotp \beta\in \overleftarrow{R}ʻʻ\alpha.\supset_{\beta}.\psi\beta:\equiv:x\in \alpha.\supset_{x}.\psi(\overleftarrow{R}ʻx) \quad[\text{*37·63}]
PM-VERBATIM-END PM1:✱37·707 -/
/- PM-VERBATIM-BEGIN PM1:✱37·708
✱37·708. ⊢:. (∃ α).α∈ R⃗ʻʻβ.ψα.≡.(∃ y).y∈ β.ψ(R⃗ʻy) [*37·64]
✱37·708. \vdash\colon\ldotp (\exists \alpha).\alpha\in \overrightarrow{R}ʻʻ\beta.\psi\alpha.\equiv.(\exists y).y\in \beta.\psi(\overrightarrow{R}ʻy) \quad[\text{*37·64}]
PM-VERBATIM-END PM1:✱37·708 -/
/- PM-VERBATIM-BEGIN PM1:✱37·709
✱37·709. ⊢:. (∃ α).α∈ R⃖ʻʻβ.ψα.≡.(∃ x).x∈ β.ψ(R⃖ʻx) [*37·64]
✱37·709. \vdash\colon\ldotp (\exists \alpha).\alpha\in \overleftarrow{R}ʻʻ\beta.\psi\alpha.\equiv.(\exists x).x\in \beta.\psi(\overleftarrow{R}ʻx) \quad[\text{*37·64}]
PM-VERBATIM-END PM1:✱37·709 -/
/- PM-VERBATIM-BEGIN PM1:✱37·71
✱37·71. ⊢:κ⊂ R⃗ʻʻβ.⊃.κ=R⃗ʻʻ{(CnvʻR⃗)ʻʻκ∩ β} [*37·65]
✱37·71. \vdash:\kappa\subset \overrightarrow{R}ʻʻ\beta.\supset.\kappa=\overrightarrow{R}ʻʻ\{(\text{Cnv}ʻ\overrightarrow{R})ʻʻ\kappa\cap \beta\} \quad[\text{*37·65}]
PM-VERBATIM-END PM1:✱37·71 -/
/- PM-VERBATIM-BEGIN PM1:✱37·711
✱37·711. ⊢:κ⊂ R⃖ʻʻβ.⊃.κ=R⃖ʻʻ{(CnvʻR⃖)ʻʻκ∩ β} [*37·65]
✱37·711. \vdash:\kappa\subset \overleftarrow{R}ʻʻ\beta.\supset.\kappa=\overleftarrow{R}ʻʻ\{(\text{Cnv}ʻ\overleftarrow{R})ʻʻ\kappa\cap \beta\} \quad[\text{*37·65}]
PM-VERBATIM-END PM1:✱37·711 -/
/- PM-VERBATIM-BEGIN PM1:✱37·712
✱37·712. ⊢:κ⊂ R⃗ʻʻβ.≡.(∃ γ).γ⊂ β.κ=R⃗ʻʻγ [*37·66]
✱37·712. \vdash:\kappa\subset \overrightarrow{R}ʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\kappa=\overrightarrow{R}ʻʻ\gamma \quad[\text{*37·66}]
PM-VERBATIM-END PM1:✱37·712 -/
/- PM-VERBATIM-BEGIN PM1:✱37·713
✱37·713. ⊢:κ⊂ R⃖ʻʻβ.≡.(∃ γ).γ⊂ β.κ=R⃖ʻʻγ [*37·66]
✱37·713. \vdash:\kappa\subset \overleftarrow{R}ʻʻ\beta.\equiv.(\exists \gamma).\gamma\subset \beta.\kappa=\overleftarrow{R}ʻʻ\gamma \quad[\text{*37·66}]
PM-VERBATIM-END PM1:✱37·713 -/
/- PM-VERBATIM-BEGIN PM1:✱37·72
✱37·72. ⊢:R=P| Q.⊃.R⃗ʻʻγ=PʻʻʻQ⃗ʻʻγ
✱37·72. \vdash:R=P\mid Q.\supset.\overrightarrow{R}ʻʻ\gamma=Pʻʻʻ\overrightarrow{Q}ʻʻ\gamma
PM-VERBATIM-END PM1:✱37·72 -/
/- PM-VERBATIM-BEGIN PM1:✱37·721
✱37·721. ⊢:R=P| Q.⊃.R⃖ʻʻγ=Q̌ʻʻʻP⃖ʻʻγ [Proof as in *37·72]
✱37·721. \vdash:R=P\mid Q.\supset.\overleftarrow{R}ʻʻ\gamma=\breve{Q}ʻʻʻ\overleftarrow{P}ʻʻ\gamma \quad[\text{Proof as in *37·72}]
PM-VERBATIM-END PM1:✱37·721 -/
/- PM-VERBATIM-BEGIN PM1:✱37·73
✱37·73. ⊢:∃ !β.≡.∃ !R⃗ʻʻβ.≡.∃ !R⃖ʻʻβ [*37·45.*32·12·121]
✱37·73. \vdash:\exists !\beta.\equiv.\exists !\overrightarrow{R}ʻʻ\beta.\equiv.\exists !\overleftarrow{R}ʻʻ\beta \quad[\text{*37·45.*32·12·121}]
PM-VERBATIM-END PM1:✱37·73 -/
/- PM-VERBATIM-BEGIN PM1:✱37·731
✱37·731. ⊢:β=Λ.≡.R⃗ʻʻβ=Λ.≡.R⃖ʻʻβ=Λ [*37·73.Transp]
✱37·731. \vdash:\beta=\Lambda.\equiv.\overrightarrow{R}ʻʻ\beta=\Lambda.\equiv.\overleftarrow{R}ʻʻ\beta=\Lambda \quad[\text{*37·73.Transp}]
PM-VERBATIM-END PM1:✱37·731 -/
/- PM-VERBATIM-BEGIN PM1:✱37·74
✱37·74. ⊢:. β⊂ᗡʻR.≡:α∈ R⃗ʻʻβ.⊃_α.∃ !α
✱37·74. \vdash\colon\ldotp \beta\subset\text{ᗡ}ʻR.\equiv:\alpha\in \overrightarrow{R}ʻʻ\beta.\supset_{\alpha}.\exists !\alpha
PM-VERBATIM-END PM1:✱37·74 -/
/- PM-VERBATIM-BEGIN PM1:✱37·75
✱37·75. ⊢:. α⊂DʻR.≡:β∈ R⃖ʻʻα.⊃_β.∃ !β [Proof as in *37·74]
✱37·75. \vdash\colon\ldotp \alpha\subset\text{D}ʻR.\equiv:\beta\in \overleftarrow{R}ʻʻ\alpha.\supset_{\beta}.\exists !\beta \quad[\text{Proof as in *37·74}]
PM-VERBATIM-END PM1:✱37·75 -/
/- PM-VERBATIM-BEGIN PM1:✱37·76
✱37·76. ⊢.R⃗ʻʻβ⊂Cls
✱37·76. \vdash.\overrightarrow{R}ʻʻ\beta\subset\text{Cls}
PM-VERBATIM-END PM1:✱37·76 -/
/- PM-VERBATIM-BEGIN PM1:✱37·761
✱37·761. ⊢.R⃖ʻʻα ⊂ Cls [Proof as in *37·76]
✱37·761. \vdash.\overleftarrow{R}ʻʻ\alpha \subset \text{Cls} \quad[\text{Proof as in *37·76}]
PM-VERBATIM-END PM1:✱37·761 -/
/- PM-VERBATIM-BEGIN PM1:✱37·77
✱37·77. ⊢: α∈ R⃗ʻʻᗡʻR.⊃_α.∃ !α [*37·74.*22·42]
✱37·77. \vdash: \alpha\in \overrightarrow{R}ʻʻ\text{ᗡ}ʻR.\supset_{\alpha}.\exists !\alpha \quad[\text{*37·74.*22·42}]
PM-VERBATIM-END PM1:✱37·77 -/
/- PM-VERBATIM-BEGIN PM1:✱37·771
✱37·771. ⊢: β∈ R⃖ʻʻDʻR.⊃_β.∃ !β [Proof as in *37·77]
✱37·771. \vdash: \beta\in \overleftarrow{R}ʻʻ\text{D}ʻR.\supset_{\beta}.\exists !\beta \quad[\text{Proof as in *37·77}]
PM-VERBATIM-END PM1:✱37·771 -/
/- PM-VERBATIM-BEGIN PM1:✱37·772
✱37·772. ⊢. Λ∼∈ R⃗ʻʻᗡʻR [*37·77.*24·63]
✱37·772. \vdash. \Lambda{\sim}\in \overrightarrow{R}ʻʻ\text{ᗡ}ʻR \quad[\text{*37·77.*24·63}]
PM-VERBATIM-END PM1:✱37·772 -/
/- PM-VERBATIM-BEGIN PM1:✱37·773
✱37·773. ⊢. Λ∼∈ R⃖ʻʻDʻR [*37·771.*24·63]
✱37·773. \vdash. \Lambda{\sim}\in \overleftarrow{R}ʻʻ\text{D}ʻR \quad[\text{*37·771.*24·63}]
PM-VERBATIM-END PM1:✱37·773 -/
/- PM-VERBATIM-BEGIN PM1:✱37·78
✱37·78. ⊢. DʻR⃗=R⃗ʻʻV [*37·28]
✱37·78. \vdash. \text{D}ʻ\overrightarrow{R}=\overrightarrow{R}ʻʻ\text{V} \quad[\text{*37·28}]
PM-VERBATIM-END PM1:✱37·78 -/
/- PM-VERBATIM-BEGIN PM1:✱37·781
✱37·781. ⊢. DʻR⃖=R⃖ʻʻV [*37·28]
✱37·781. \vdash. \text{D}ʻ\overleftarrow{R}=\overleftarrow{R}ʻʻ\text{V} \quad[\text{*37·28}]
PM-VERBATIM-END PM1:✱37·781 -/
/- PM-VERBATIM-BEGIN PM1:✱37·79
✱37·79. ⊢. R⃗ʻʻV= α̂{∃ y).α=R⃗ʻy} [*37·601.*32·12]
✱37·79. \vdash. \overrightarrow{R}ʻʻ\text{V}= \hat{\alpha}\{\exists y).\alpha=\overrightarrow{R}ʻy\} \quad[\text{*37·601.*32·12}]
PM-VERBATIM-END PM1:✱37·79 -/
/- PM-VERBATIM-BEGIN PM1:✱37·791
✱37·791. ⊢. R⃖ʻʻV= β̂{(∃ x).β=R⃖ʻx} [*37·601.*32·121]
✱37·791. \vdash. \overleftarrow{R}ʻʻ\text{V}= \hat{\beta}\{(\exists x).\beta=\overleftarrow{R}ʻx\} \quad[\text{*37·601.*32·121}]
PM-VERBATIM-END PM1:✱37·791 -/
/- PM-VERBATIM-BEGIN PM1:✱37·8
✱37·8. ⊢. (α↑ β)| S=α↑ Šʻʻβ
✱37·8. \vdash. (\alpha\uparrow \beta)\mid S=\alpha\uparrow \breve{S}ʻʻ\beta
PM-VERBATIM-END PM1:✱37·8 -/
/- PM-VERBATIM-BEGIN PM1:✱37·81
✱37·81. ⊢.R| (α↑ β)=(Rʻʻα)↑ β [Proof as in *37·8]
✱37·81. \vdash.R\mid (\alpha\uparrow \beta)=(Rʻʻ\alpha)\uparrow \beta \quad[\text{Proof as in *37·8}]
PM-VERBATIM-END PM1:✱37·81 -/
/- PM-VERBATIM-BEGIN PM1:✱37·82
✱37·82. ⊢.R| (α↑ β)| S=(Rʻʻα)↑ (Šʻʻβ) [*37·8·81]
✱37·82. \vdash.R\mid (\alpha\uparrow \beta)\mid S=(Rʻʻ\alpha)\uparrow (\breve{S}ʻʻ\beta) \quad[\text{*37·8·81}]
PM-VERBATIM-END PM1:✱37·82 -/
