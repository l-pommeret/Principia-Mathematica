/-! PM I ✱35, canonical Gutenberg 78050 complete source. -/
/- PM-VERBATIM-BEGIN PM1:✱35·01
α↿ R=x̂ŷ(x∈ α.xRy) Df
✱35·01. \(\alpha\upharpoonleft R=\hat{x}\hat{y}(x\in \alpha.xRy) \quad\text{Df}\)
PM-VERBATIM-END PM1:✱35·01 -/
/- PM-VERBATIM-BEGIN PM1:✱35·02
R↾ β=x̂ŷ(xRy.y∈ β) Df
✱35·02. \(R\upharpoonright \beta=\hat{x}\hat{y}(xRy.y\in \beta) \quad\text{Df}\)
PM-VERBATIM-END PM1:✱35·02 -/
/- PM-VERBATIM-BEGIN PM1:✱35·03
α↿ R↾ β=x̂ŷ(x∈ α.xRy.y∈ β) Df
✱35·03. \(\alpha\upharpoonleft R\upharpoonright \beta=\hat{x}\hat{y}(x\in \alpha.xRy.y\in \beta)\quad\text{Df}\)
PM-VERBATIM-END PM1:✱35·03 -/
/- PM-VERBATIM-BEGIN PM1:✱35·04
α↑ β=x̂ŷ(x∈ α.y∈ β) Df
✱35·04. \(\alpha\uparrow \beta=\hat{x}\hat{y}(x\in \alpha.y\in \beta) \quad\text{Df}\)
PM-VERBATIM-END PM1:✱35·04 -/
/- PM-VERBATIM-BEGIN PM1:✱35·05
Rʻx↑ β=(Rʻx)↑ β Df
✱35·05. \(Rʻx\uparrow \beta=(Rʻx)\uparrow \beta \quad\text{Df}\)
PM-VERBATIM-END PM1:✱35·05 -/
/- PM-VERBATIM-BEGIN PM1:✱35·1
✱35·1. ⊢:x(α↿ R)y.≡.x∈ α.xRy [*21·3.(*35·01)]
PM-VERBATIM-END PM1:✱35·1 -/
/- PM-VERBATIM-BEGIN PM1:✱35·101
✱35·101. ⊢:x(R↾ β)y.≡.xRy.y∈ β
PM-VERBATIM-END PM1:✱35·101 -/
/- PM-VERBATIM-BEGIN PM1:✱35·102
✱35·102. ⊢:x(α↿ R↾ β)y.≡.x∈ α.xRy.y∈ β
PM-VERBATIM-END PM1:✱35·102 -/
/- PM-VERBATIM-BEGIN PM1:✱35·103
✱35·103. ⊢:x(α↑ β)y.≡.x∈ α.y∈ β
PM-VERBATIM-END PM1:✱35·103 -/
/- PM-VERBATIM-BEGIN PM1:✱35·11
✱35·11. ⊢.α↿ R↾ β=(α↿ R)∩̇(R↾ β)
Dem.
⊢.*35·102.⊃⊢:x(α↿ R↾ β)y. ≡.x∈ α.xRy.y∈ β.
[*4·24] ≡.x∈ α.xRy.xRy.y∈ β.
[*35·1·101] ≡.x(α↿ R)y.x(R↾ β)y.
[*23·33] ≡.x{(α↿ R)∩̇(R↾ β)}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·11 -/
/- PM-VERBATIM-BEGIN PM1:✱35·12
✱35·12. ⊢.(α↿ R)∩̇(S↾ β)=α↿ (R∩̇S)↾ β
Dem.
⊢.*23·33.⊃⊢:x{(α↿ R)∩̇(S↾ β)}y. ≡.x(α↿ R)y.x(S↾ β)y.
[*35·1·101] ≡.x∈ α.xRy.xSy.y∈ β.
[*23·33] ≡.x∈ α.x(R∩̇S)y.y∈ β.
[*35·102] ≡.x{α↿ (R∩̇S)↾ β}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·12 -/
/- PM-VERBATIM-BEGIN PM1:✱35·13
✱35·13. ⊢.(α↿ R)∩̇(β↿ S)=(α ∩ β)↿ (R∩̇S)
Dem.
⊢.*23·33.⊃⊢:x{(α↿ R)∩̇(β↿ S)}y. ≡.x(α↿ R)y.x(β↿ S)y.
[*35·1] ≡.x∈ α.xRy.x∈ β.xSy.
[*22·33.*23·33] ≡.x∈ (α ∩ β).x(R∩̇S)y.
[*35·1] ≡.x{(α ∩ β)↿ (R∩̇S)}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·13 -/
/- PM-VERBATIM-BEGIN PM1:✱35·14
✱35·14. ⊢.(R↾ α)∩̇(S↾ β)=(R∩̇S)↾ (α ∩ β) [Similar proof to *35·13]
PM-VERBATIM-END PM1:✱35·14 -/
/- PM-VERBATIM-BEGIN PM1:✱35·15
✱35·15. ⊢.(α↿ R↾ β)∩̇(α'↿ S↾ β')=(α ∩ α')↿ (R∩̇S)↾ (β ∩ β')
Dem.
⊢.*35·11.⊃
⊢.(α↿ R↾ β)∩̇(α'↿ S↾ β') =(α↿ R)∩̇(R↾ β)∩̇(α'↿ S)∩̇(S↾ β')
[*35·13·14] ={(α ∩ α')↿ (R∩̇S)}∩̇{(R∩̇S)↾ (β ∩ β')}
[*35·11] ={(α ∩ α')↿ (R∩̇S)↾ (β ∩ β')}.⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·15 -/
/- PM-VERBATIM-BEGIN PM1:✱35·16
✱35·16. ⊢.(α↿ R)∩̇S=α↿ (R∩̇S)=R∩̇α↿ S [Similar proof to *35·13]
PM-VERBATIM-END PM1:✱35·16 -/
/- PM-VERBATIM-BEGIN PM1:✱35·17
✱35·17. ⊢.(R↾ β)∩̇S=(R∩̇S)↾ β=R∩̇S↾ β [Similar proof to *35·13]
PM-VERBATIM-END PM1:✱35·17 -/
/- PM-VERBATIM-BEGIN PM1:✱35·18
✱35·18. ⊢.(α↿ R↾ β)∩̇S=α↿ (R∩̇S)↾ β=R∩̇α ↿ S↾ β [Similar proof to *35·15]
PM-VERBATIM-END PM1:✱35·18 -/
/- PM-VERBATIM-BEGIN PM1:✱35·21
✱35·21. ⊢.α↿ R↾ β=(α↿ R)↾ β=α↿ (R↾ β)
Dem.
⊢.*35·102.⊃⊢:x(α↿ R↾ β)y. ≡.x∈ α.xRy.y∈ β.
[*35·1] ≡.x(α↿ R)y.y∈ β.
[*35·101] ≡.x{(α↿ R)↾ β}y (1)
⊢.*35·102.⊃⊢:x(α↿ R↾ β)y. ≡.x∈ α.xRy.y∈ β.
[*35·101] ≡.x∈ α.x(R↾ β)y.
[*35·1] ≡.x{α↿ (R↾ β)}y (2)
⊢.(1).(2).⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·21 -/
/- PM-VERBATIM-BEGIN PM1:✱35·22
✱35·22. ⊢.(α↿ R)| S=α↿ (R| S)
Dem.
⊢.*34·1.⊃⊢:. x{(α↿ R)| S}y. ≡:(∃ z).x(α↿ R)z.zSy:
[*35·1] ≡:(∃ z).x∈ α.xRz.zSy:
[*10·35] ≡:x∈ α:(∃ z).xRz.zSy.
[*34·1] ≡:x∈ α.x(R| S)y:
[*35·1] ≡:x{α↿ (R| S)}y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·22 -/
/- PM-VERBATIM-BEGIN PM1:✱35·23
✱35·23. ⊢.S| (R↾ β)=(S| R)↾ β [Similar proof to *35·22]
PM-VERBATIM-END PM1:✱35·23 -/
/- PM-VERBATIM-BEGIN PM1:✱35·24
✱35·24. α↿ R| S=(α↿ R)| S Df
PM-VERBATIM-END PM1:✱35·24 -/
/- PM-VERBATIM-BEGIN PM1:✱35·25
✱35·25. S| R↾ β=(S| R)↾ β Df
PM-VERBATIM-END PM1:✱35·25 -/
/- PM-VERBATIM-BEGIN PM1:✱35·26
✱35·26. ⊢.(α↿ R)| (S↾ β) =α↿ (R| S)↾ β={α↿ (R| S)}↾ β=α↿ {(R| S)↾ β} ={(α↿ R)| S)}↾ β=α↿ {R| (S↾ β)} =(α↿ R| S)↾ β=α↿ (R| S↾ β)
Dem.
⊢.*34·1.⊃⊢:. x{(α↿ R)| (S↾ β)}y. ≡:(∃ z).x(α↿ R)z.z(S↾ β)y:
[*35·1·101] ≡:(∃ z).x∈ α.xRz.zSy.y∈ β:
[*10·35] ≡:x∈ α.y∈ β:(∃ z).xRz.zSy:
[*34·1] ≡:x∈ α.x(R| S)y.y∈ β:
[*35·102] ≡:x{α↿ (R| S)↾ β}y (1)
⊢.(1).*35·21·22·23.(*35·24·25).⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·26 -/
/- PM-VERBATIM-BEGIN PM1:✱35·27
✱35·27. α↿ R| S↾ β=(α↿ R| S)↾ β Df
PM-VERBATIM-END PM1:✱35·27 -/
/- PM-VERBATIM-BEGIN PM1:✱35·31
✱35·31. ⊢.(R↾ α)↾ β=R↾ (α∩ β)
Dem.
⊢.*35·101.⊃⊢:x{(R↾ α)↾ β}y. ≡.x(R↾ α)y.y∈ β.
[*35·101] ≡.xRy.y∈ α.y∈ β.
[*22·33] ≡.xRy.y∈ α∩ β.
[*35·101] ≡.x{R↾ (α∩ β)}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·31 -/
/- PM-VERBATIM-BEGIN PM1:✱35·32
✱35·32. ⊢.α↿ (β↿ R)=(α∩ β)↿ R [Proof similar to that of *35·31]
PM-VERBATIM-END PM1:✱35·32 -/
/- PM-VERBATIM-BEGIN PM1:✱35·33
✱35·33. ⊢.(α↿ R↾ β)↾ γ={α↿ R↾ (β∩ γ)} [Proof similar to that of *35·31]
PM-VERBATIM-END PM1:✱35·33 -/
/- PM-VERBATIM-BEGIN PM1:✱35·34
✱35·34. ⊢.α↿ (β↿ R↾ γ)={(α∩ β)↿ R↾ γ} [Proof similar to that of *35·31]
PM-VERBATIM-END PM1:✱35·34 -/
/- PM-VERBATIM-BEGIN PM1:✱35·35
✱35·35. ⊢.α↿ R=(α∩ DʻR)↿ R
Dem.
⊢.*35·1.⊃⊢:x(α↿ R)y. ≡.x∈ α.xRy.
[*33·14] ≡.x∈ α.x∈ DʻR.xRy.
[*22·33.*35·1] ≡.x{(α∩ DʻR)↿ R}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·35 -/
/- PM-VERBATIM-BEGIN PM1:✱35·351
✱35·351. ⊢.R↾ β=R↾ (β∩ ᗡʻR) [Proof as in *35·35]
PM-VERBATIM-END PM1:✱35·351 -/
/- PM-VERBATIM-BEGIN PM1:✱35·352
✱35·352. ⊢.α↿ R↾ β=(α∩ DʻR)↿ R↾ (β∩ ᗡʻR) [Proof as in *35·35]
PM-VERBATIM-END PM1:✱35·352 -/
/- PM-VERBATIM-BEGIN PM1:✱35·354
✱35·354. ⊢.(R↾ α)| S=R| α↿ S
Dem.
⊢.*34·1.*35·101. ⊃
⊢:x{(R↾ α)| S}z. ≡.(∃ y).xRy.y∈ α.ySz.
[*35·1] ≡.(∃ y).xRy.y(α↿ S)z.
[*34·1] ≡.x{R| (α↿ S)}z:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·354 -/
/- PM-VERBATIM-BEGIN PM1:✱35·41
✱35·41. ⊢.(α∪ α')↿ R=α↿ R⊍α'↿ R [*35·1.*22·34]
PM-VERBATIM-END PM1:✱35·41 -/
/- PM-VERBATIM-BEGIN PM1:✱35·412
✱35·412. ⊢.R↾ (β∪ β')=R↾ β⊍R↾ β' [*35·101.*22·34]
PM-VERBATIM-END PM1:✱35·412 -/
/- PM-VERBATIM-BEGIN PM1:✱35·413
✱35·413. ⊢.(α∪α')↿ R↾ (β∪β') =(α↿ R↾ β)⊍(α↿ R↾ β') ⊍(α'↿ R↾ β)⊍(α'↿ R↾ β') [*35·102.*22·34]
PM-VERBATIM-END PM1:✱35·413 -/
/- PM-VERBATIM-BEGIN PM1:✱35·42
✱35·42. ⊢.α↿ (R⊍S)=(α↿ R)⊍(α↿ S) [*35·1.*23·34]
PM-VERBATIM-END PM1:✱35·42 -/
/- PM-VERBATIM-BEGIN PM1:✱35·421
✱35·421. ⊢.(R⊍S)↾ β=(R↾ β)⊍(S↾ β) [*35·101.*23·34]
PM-VERBATIM-END PM1:✱35·421 -/
/- PM-VERBATIM-BEGIN PM1:✱35·422
✱35·422. ⊢.α↿ (R⊍S)↾ β=(α↿ R↾ β)⊍(α↿ S↾ β) [*35·102.*23·34]
PM-VERBATIM-END PM1:✱35·422 -/
/- PM-VERBATIM-BEGIN PM1:✱35·43
✱35·43. ⊢:α⊂β.⊃.α↿ R⪽β↿ R
Dem.
⊢.*35·1.⊃⊢:. α⊂β.⊃:x(α↿ R)y. ≡.x∈ α.xRy.
[*22·1] ⊃.x∈ β.xRy.
[*35·1] ⊃.x(β↿ R)y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·43 -/
/- PM-VERBATIM-BEGIN PM1:✱35·431
✱35·431. ⊢:β⊂γ.⊃.R↾ β⪽R↾ γ [Proof similar to that of *35·43]
PM-VERBATIM-END PM1:✱35·431 -/
/- PM-VERBATIM-BEGIN PM1:✱35·432
✱35·432. ⊢:α⊂γ.β⊂δ.⊃.α↿ R↾ β ⪽γ↿ R↾ δ [Proof similar to that of *35·43]
PM-VERBATIM-END PM1:✱35·432 -/
/- PM-VERBATIM-BEGIN PM1:✱35·44
✱35·44. ⊢.α↿ R⪽R
Dem.
⊢.*35·1.⊃⊢:x(α↿ R)y. ⊃.x∈ α.xRy.
[*3·27] ⊃.xRy:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·44 -/
/- PM-VERBATIM-BEGIN PM1:✱35·441
✱35·441. ⊢.R↾ β⪽R [Proof similar to that of *35·44]
PM-VERBATIM-END PM1:✱35·441 -/
/- PM-VERBATIM-BEGIN PM1:✱35·442
✱35·442. ⊢.α↿ R↾ β⪽R [Proof similar to that of *35·44]
PM-VERBATIM-END PM1:✱35·442 -/
/- PM-VERBATIM-BEGIN PM1:✱35·451
✱35·451. ⊢:DʻR⊂α.⊃.α↿ R=R
Dem.
⊢.*4·71. ⊃⊢:. Hp.⊃:x∈ DʻR.≡.x∈ DʻR.x∈ α:
[*4·36] ⊃:x∈ DʻR.xRy.≡.x∈ DʻR.xRy.x∈ α (1)
⊢.*33·14.*4·71. ⊃⊢:xRy.≡.x∈ DʻR.xRy (2)
⊢.(1).(2). ⊃⊢:. Hp.⊃:xRy.≡.xRy.x∈ α.
[*35·1] ≡.x(α↿ R)y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·451 -/
/- PM-VERBATIM-BEGIN PM1:✱35·452
✱35·452. ⊢:ᗡʻR⊂β.⊃.R↾ β=R [Similar proof]
PM-VERBATIM-END PM1:✱35·452 -/
/- PM-VERBATIM-BEGIN PM1:✱35·453
✱35·453. ⊢:DʻR⊂α.⊃.α↿ R↾ β=R↾ β [Similar proof]
PM-VERBATIM-END PM1:✱35·453 -/
/- PM-VERBATIM-BEGIN PM1:✱35·454
✱35·454. ⊢:ᗡʻR⊂β.⊃.α↿ R↾ β=α↿ R [Similar proof]
PM-VERBATIM-END PM1:✱35·454 -/
/- PM-VERBATIM-BEGIN PM1:✱35·46
✱35·46. ⊢:R⪽S.⊃.α↿ R⪽α↿ S
Dem.
⊢.*23·1.⊃⊢:. Hp. ⊃:xRy.⊃.xSy:
[Fact] ⊃:x∈ α.xRy.⊃.x∈ α.xSy:
[*35·1] ⊃:x(α↿ R)y.⊃.x(α↿ S)y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·46 -/
/- PM-VERBATIM-BEGIN PM1:✱35·461
✱35·461. ⊢:R⪽S.⊃.R↾ β⪽S↾ β [Similar proof]
PM-VERBATIM-END PM1:✱35·461 -/
/- PM-VERBATIM-BEGIN PM1:✱35·462
✱35·462. ⊢:R⪽S.⊃.α↿ R↾ β⪽α↿ S↾ β [Similar proof]
PM-VERBATIM-END PM1:✱35·462 -/
/- PM-VERBATIM-BEGIN PM1:✱35·471
✱35·471. ⊢:ᗡʻP∩ α=Λ.⊃.P| (α↿ R)=Λ̇
Dem.
⊢.*34·1.⊃⊢:x{P| (α↿ R)}z. ⊃.(∃ y).xPy.y(α↿ R)z.
[*35·1] ⊃.(∃ y).xPy.y∈ α.yRz.
[*33·14.*10·5] ⊃.(∃ y).y∈ ᗡʻP.y∈ α.
[*22·33.*24·5] ⊃.∃ !ᗡʻP∩ α (1)
⊢.(1).Transp.*24·51. ⊃
⊢:ᗡʻP∩ α=Λ. ⊃.∼x{P| (α↿ R)}z:
[*11·11·3] ⊃⊢:ᗡʻP∩ α=Λ.⊃.(x,z).∼x{P| (α↿ R)}z.
[*25·15] ⊃.P| (α↿ R)=Λ̇:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·471 -/
/- PM-VERBATIM-BEGIN PM1:✱35·472
✱35·472. ⊢:DʻP∩ α=Λ.⊃.(R↾ α)| P=Λ̇
PM-VERBATIM-END PM1:✱35·472 -/
/- PM-VERBATIM-BEGIN PM1:✱35·473
✱35·473. ⊢:ᗡʻP∩ α=Λ.⊃.P| (α↿ R↾ β)=Λ̇
PM-VERBATIM-END PM1:✱35·473 -/
/- PM-VERBATIM-BEGIN PM1:✱35·474
✱35·474. ⊢:DʻP∩ β=Λ.⊃.(α↿ R↾ β)| P=Λ̇
PM-VERBATIM-END PM1:✱35·474 -/
/- PM-VERBATIM-BEGIN PM1:✱35·48
✱35·48. ⊢:ᗡʻP⊂α.⊃.P| (α↿ R)=P| R
Dem.
⊢.*22·1. ⊃⊢:. Hp. ⊃:y∈ ᗡʻP.⊃y.y∈ α:
[*4·71] ⊃:y∈ ᗡʻP.y∈ α.≡y.y∈ ᗡʻP:
[*10·311] ⊃:xPy.y∈ ᗡʻP.y∈ α.≡y.xPy.y∈ ᗡʻP (1)
⊢.*33·14.*4·71. ⊃⊢:xPy.y∈ ᗡʻP.≡.xPy (2)
⊢.(1).(2). ⊃⊢:. Hp.⊃:xPy.y∈ α.≡y.xPy:
[*10·311] ⊃:xPy.y∈ α.yRz.≡y.xPy.yRz:
[*35·1] ⊃:xPy.y(α↿ R)z.≡y.xPy.yRz:
[*10·281] ⊃:(∃ y).xPy.y(α↿ R)z.≡.(∃ y).xPy.yRz:
[*34·1] ⊃:x(P| α↿ R)z.≡.x(P| R)z:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·48 -/
/- PM-VERBATIM-BEGIN PM1:✱35·481
✱35·481. ⊢:DʻR⊂β.⊃.(P↾ β)| R=P| R [Similar proof]
PM-VERBATIM-END PM1:✱35·481 -/
/- PM-VERBATIM-BEGIN PM1:✱35·51
✱35·51. ⊢.Cnvʻ(α↿ R)=Ř↾ α
Dem.
⊢.*31·131.⊃⊢:x{Cnvʻ(α↿ R)}y. ≡.y(α↿ R)x.
[*35·1] ≡.y∈ α.yRx.
[*31·11] ≡.xŘy.y∈ α.
[*35·101] ≡.x(Ř↾ α)y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·51 -/
/- PM-VERBATIM-BEGIN PM1:✱35·52
✱35·52. ⊢.Cnvʻ(R↾ β)=β↿ Ř [Proof similar to that of *35·51]
PM-VERBATIM-END PM1:✱35·52 -/
/- PM-VERBATIM-BEGIN PM1:✱35·53
✱35·53. ⊢.Cnvʻ(α↿ R↾ β)=β↿ Ř↾ α [Proof similar to that of *35·51]
PM-VERBATIM-END PM1:✱35·53 -/
/- PM-VERBATIM-BEGIN PM1:✱35·61
✱35·61. ⊢.Dʻ(α↿ R)=α∩ DʻR
Dem.
⊢.*33·13.⊃⊢:. x∈ Dʻ(α↿ R). ≡:(∃ y).x(α↿ R)y:
[*35·1] ≡:(∃ y).x∈ α.xRy:
[*10·35] ≡:x∈ α:(∃ y).xRy:
[*33·13] ≡:x∈ α.x∈ DʻR:
[*22·33] ≡:x∈ (α∩ DʻR):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·61 -/
/- PM-VERBATIM-BEGIN PM1:✱35·62
✱35·62. ⊢:α⊂DʻR.⊃.Dʻ(α↿ R)=α [*35·61.*22·621]
PM-VERBATIM-END PM1:✱35·62 -/
/- PM-VERBATIM-BEGIN PM1:✱35·63
✱35·63. ⊢:DʻR⊂α.≡.α↿ R=R
Dem.
⊢.*35·61.⊃⊢:α↿ R=R. ⊃.α∩ DʻR=DʻR
[*22·621] ⊃.DʻR⊂α (1)
⊢.(1).*35·451.⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·63 -/
/- PM-VERBATIM-BEGIN PM1:✱35·64
✱35·64. ⊢.ᗡʻ(R↾ β)=β∩ ᗡʻR [Proof as in *35·61]
PM-VERBATIM-END PM1:✱35·64 -/
/- PM-VERBATIM-BEGIN PM1:✱35·641
✱35·641. ⊢:α∩ DʻR=Λ.⊃.α↿ R=Λ̇ [*35·61.*33·241]
PM-VERBATIM-END PM1:✱35·641 -/
/- PM-VERBATIM-BEGIN PM1:✱35·642
✱35·642. ⊢:α∩ ᗡʻR=Λ.⊃.R↾ α=Λ̇ [*35·64.*33·241]
PM-VERBATIM-END PM1:✱35·642 -/
/- PM-VERBATIM-BEGIN PM1:✱35·643
✱35·643. ⊢:α∩ DʻR=Λ.⊃.α↿ (R⊍S)=α↿ S [*35·641·42]
PM-VERBATIM-END PM1:✱35·643 -/
/- PM-VERBATIM-BEGIN PM1:✱35·644
✱35·644. ⊢:α∩ ᗡʻR=Λ.⊃.(R⊍S)↾ α=S↾ α [*35·642·421]
PM-VERBATIM-END PM1:✱35·644 -/
/- PM-VERBATIM-BEGIN PM1:✱35·65
✱35·65. ⊢:β⊂ᗡʻR.⊃.ᗡʻ(R↾ β)=β [*35·64.*22·621]
PM-VERBATIM-END PM1:✱35·65 -/
/- PM-VERBATIM-BEGIN PM1:✱35·66
✱35·66. ⊢:ᗡʻR⊂β.≡.R↾ β=R [Proof as in *35·63]
PM-VERBATIM-END PM1:✱35·66 -/
/- PM-VERBATIM-BEGIN PM1:✱35·671
✱35·671. ⊢.Dʻ(R| S)=Dʻ(R↾ DʻS)
Dem.
⊢.*33·13.⊃⊢:. x∈ Dʻ(R| S). ≡:(∃ y).x(R| S)y:
[*34·1] ≡:(∃ y,z).xRz.zSy:
[*11·23] ≡:(∃ z,y).xRz.zSy:
[*10·35] ≡:(∃ z):xRz:(∃ y).zSy:
[*33·13] ≡:(∃ z).xRz.z∈ DʻS:
[*35·101] ≡:(∃ z).x(R↾ DʻS)z:
[*33·13] ≡:x∈ Dʻ(R↾ DʻS):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·671 -/
/- PM-VERBATIM-BEGIN PM1:✱35·672
✱35·672. ⊢.ᗡʻ(R| S)=ᗡʻ(ᗡʻR↿ S) [Similar proof]
PM-VERBATIM-END PM1:✱35·672 -/
/- PM-VERBATIM-BEGIN PM1:✱35·68
✱35·68. ⊢:α∩ β=Λ.⊃.(α↿ R↾ β)²=Λ̇
Dem.
⊢.*35·61·64·21.⊃⊢.Dʻ(α↿ R↾ β) ⊂α.ᗡʻ(α↿ R↾ β)⊂β.
[*22·49.*24·13]⊃⊢:α∩ β=Λ. ⊃.Dʻ(α↿ R↾ β)∩ ᗡʻ(α↿ R↾ β)=Λ.
[*34·531] ⊃.(α↿ R↾ β)²=Λ̇:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·68 -/
/- PM-VERBATIM-BEGIN PM1:✱35·7
✱35·7. ⊢:φ{(R↾ β)ʻy}.≡.y∈ β.φ(Rʻy)
Dem.
⊢.*14·21. ⊃⊢:φ{(R↾ β)ʻy}. ⊃.E!(R↾ β)ʻy.
[*33·43] ⊃.y∈ ᗡʻ(R↾ β).
[*35·64] ⊃.y∈ β (1)
⊢.(1).*4·71.⊃⊢:φ{(R↾ β)ʻy}. ≡.y∈ β.φ{(R↾ β)ʻy} (2)
⊢.*4·73.*35·101.⊃⊢:. y∈ β. ⊃:x(R↾ β)y.≡ₓ.xRy:
[*14·272] ⊃:φ{(R↾ β)ʻy}.≡.φ(Rʻy) (3)
⊢.(3).*5·32.⊃⊢:y∈ β.φ{(R↾ β)ʻy}. ≡.y∈ β.φ(Rʻy) (4)
⊢.(2).(4). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·7 -/
/- PM-VERBATIM-BEGIN PM1:✱35·71
✱35·71. ⊢:. y∈ β.⊃y.Rʻy=Sʻy:⊃.R↾ β=S↾ β
Dem.
⊢.*4·7.⊃⊢:. Hp. ⊃:y∈ β.⊃y.y∈ β.Rʻy=Sʻy:
[*35·7] ⊃:y∈ β.⊃y.(R↾ β)ʻy=(S↾ β)ʻy:
[*35·64] ⊃:y∈ ᗡʻ(R↾ β)∪ ᗡʻ(S↾ β).⊃y.(R↾ β)ʻy=(S↾ β)ʻy:
[*33·45] ⊃:R↾ β=S↾ β:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·71 -/
/- PM-VERBATIM-BEGIN PM1:✱35·75
✱35·75. ⊢.Λ↿ R=R↾ Λ=Λ↿ R↾ β=α↿ R↾ Λ=Λ̇
Dem.
⊢.*35·61. ⊃⊢.Dʻ(Λ↿ R)=Λ.
[*33·241] ⊃⊢.Λ↿ R=Λ̇ (1)
⊢.*35·64. ⊃⊢.ᗡʻ(R↾ Λ)=Λ.
[*33·241] ⊃⊢.R↾ Λ=Λ̇ (2)
⊢.*35·441·21. ⊃⊢.Λ↿ R↾ β⪽Λ↿ R.
[(1).*25·13] ⊃⊢.Λ↿ R↾ β=Λ̇ (3)
⊢.*35·44·21. ⊃⊢.α↿ R↾ Λ⪽R↾ Λ.
[(2).*25·13] ⊃⊢.α↿ R↾ Λ=Λ̇ (4)
⊢.(1).(2).(3).(4). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·75 -/
/- PM-VERBATIM-BEGIN PM1:✱35·76
✱35·76. ⊢.V↿ R=R↾ V=V↿ R↾ V=R
Dem.
⊢.*35·1. ⊃⊢:x(V↿ R)y. ≡.x∈ V.xRy.
[*24·104.*4·73] ≡.xRy (1)
⊢.*35·101.⊃⊢:x(R↾ V)y. ≡.xRy.y∈ V.
[*24·104.*4·73] ≡.xRy (2)
⊢.*35·102.⊃⊢:x(V↿ R↾ V)y. ≡.x∈ V.xRy.y∈ V.
[*24·104.*4·73] ≡.xRy (3)
⊢.(1).(2).(3).⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·76 -/
/- PM-VERBATIM-BEGIN PM1:✱35·81
✱35·81. ⊢:x(α↿ V̇)y.≡.x∈ α [*35·1.*25·104]
PM-VERBATIM-END PM1:✱35·81 -/
/- PM-VERBATIM-BEGIN PM1:✱35·812
✱35·812. ⊢:x(V̇↾ β)y.≡.y∈ β [*35·101.*25·104]
PM-VERBATIM-END PM1:✱35·812 -/
/- PM-VERBATIM-BEGIN PM1:✱35·82
✱35·82. ⊢.α↑ β=α↿ V̇↾ β
Dem.
⊢.*35·103.⊃⊢:x(α↑ β)y. ≡.x∈ α.y∈ β.
[*25·104] ≡.x∈ α.xV̇y.y∈ β.
[*35·102] ≡.x(α↿ V̇↾ β)y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·82 -/
/- PM-VERBATIM-BEGIN PM1:✱35·822
✱35·822. ⊢.α↿ R↾ β=R∩̇(α↑ β)
Dem.
⊢.*35·102.⊃⊢:x(α↿ R↾ β)y. ≡.x∈ α.xRy.y∈ β.
[*4·3] ≡.xRy.x∈ α.y∈ β.
[*35·103] ≡.xRy.x(α↑ β)y.
[*23·33] ≡.x{R∩̇(α↑ β)}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·822 -/
/- PM-VERBATIM-BEGIN PM1:✱35·83
✱35·83. ⊢:DʻR⊂ α.ᗡʻR⊂ β.≡.R⪽α↑ β
Dem.
⊢.*33·14. ⊃⊢:. xRy.⊃:x∈ DʻR.y∈ ᗡʻR:
[*22·46] ⊃:DʻR⊂ α.ᗡʻR⊂ β.⊃.x∈ α.y∈ β (1)
⊢.(1).Comm. ⊃⊢:. DʻR⊂ α.ᗡʻR⊂ β.⊃:xRy.⊃.x∈ α.y∈ β.
[*35·103] ⊃.x(α↑ β)y (2)
⊢.*35·103. ⊃⊢:. R⪽α↑ β.⊃:xRy.⊃ₓ,y.x∈ α.y∈ β:
[*33·35·351] ⊃:DʻR⊂ α.ᗡʻR⊂ β (3)
⊢.(2).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·83 -/
/- PM-VERBATIM-BEGIN PM1:✱35·831
✱35·831. ⊢.-̇(α↑ β)=(-α↑ β)⊍(α↑ -β)⊍(-α↑ -β)
Dem.
⊢.*23·35.⊃⊢:: x-̇(α↑ β)y. ≡:. ∼{x(α↑ β)y}:.
[*35·103] ≡:. ∼(x∈ α.y∈ β):.
[*4·51] ≡:. x∼∈ α.∨ .y∼∈ β:.
[*4·42] ≡:. x∼∈ α:y∈ β.∨ .y∼∈ β:. ∨ :. x∈ α.∨ .x∼∈ α:y∼∈ β:.
[*4·4] ≡:. x∼∈ α.y∈ β.∨ .x∼∈ α.y∼∈ β.∨ .x∈ α.y∼∈ β.∨ .x∼∈ α.y∼∈ β:.
[*4·25·31·37] ≡:. x∼∈ α.y∈ β.∨ .x∈ α.y∼∈ β.∨ .x∼∈ α.y∼∈ β:.
[*22·35] ≡:. x∈ -α.y∈ β.∨ .x∈ α.y∈ -β.∨ .x∈ -α.y∈ -β:.
[*35·103] ≡:. x(-α↑ β)y.∨ .x(α↑ -β)y.∨ .x(-α↑ -β)y:.
[*23·34] ≡:. x{(-α↑ β)⊍(α↑ -β)⊍(-α↑ -β)}y:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·831 -/
/- PM-VERBATIM-BEGIN PM1:✱35·832
✱35·832. -̇(α↿ R↾ β)=(-α↑ β)⊍(α↑ -β)⊍(-α↑ -β)⊍-̇R [*35·822·831.Transp.*23·84]
PM-VERBATIM-END PM1:✱35·832 -/
/- PM-VERBATIM-BEGIN PM1:✱35·834
✱35·834. ⊢.(α↑ β)∩̇(γ↑ δ)=(α∩ γ)↑ (β∩ δ)
Dem.
⊢.*35·103.⊃
⊢:x{(α↑ β)∩̇(γ↑ δ)}y. ≡.x∈ α.y∈ β.x∈ γ.y∈ δ.
[*22·33.*35·103] ≡.x{(α∩ γ)↑ (β∩ δ)}y:⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·834 -/
/- PM-VERBATIM-BEGIN PM1:✱35·84
✱35·84. ⊢.Cnvʻ(α↑ β)=β↑ α [*35·103.*31·131]
PM-VERBATIM-END PM1:✱35·84 -/
/- PM-VERBATIM-BEGIN PM1:✱35·85
✱35·85. ⊢:∃ !β.⊃.Dʻ(α↑ β)=α
Dem.
⊢.*35·103.*10·281.⊃
⊢:. (∃ y).x(α↑ β)y. ≡:(∃ y).x∈ α.y∈ β:
[*10·35] ≡:x∈ α:(∃ y).y∈ β:
[*24·5] ≡:x∈ α.∃ !β (1)
⊢.(1).*33·13.*10·35.⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·85 -/
/- PM-VERBATIM-BEGIN PM1:✱35·86
✱35·86. ⊢:∃ !α.⊃.ᗡʻ(α↑ β)=β [Similar proof]
PM-VERBATIM-END PM1:✱35·86 -/
/- PM-VERBATIM-BEGIN PM1:✱35·87
✱35·87. ⊢:∃̇!(α↑ β).≡.∃ !α.∃ !β
Dem.
⊢.*35·103.⊃⊢:. ∃̇!(α↑ β). ≡:(∃ x,y).x∈ α.y∈ β:
[*11·54] ≡:(∃ x).x∈ α:(∃ y).y∈ β:
[*24·5] ≡:∃ !α.∃ !β:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·87 -/
/- PM-VERBATIM-BEGIN PM1:✱35·88
✱35·88. ⊢:. α↑ β=Λ̇.≡:α=Λ.∨.β=Λ [*35·87.Transp.*24·51.*25·51]
PM-VERBATIM-END PM1:✱35·88 -/
/- PM-VERBATIM-BEGIN PM1:✱35·881
✱35·881. ⊢:ᗡʻR⊂α.⊃.R| (α↑ β)=DʻR↑ β
Dem.
⊢.*34·1.*35·103.⊃
⊢:x{R| (α↑ β)}y.≡.(∃ z).xRz.z∈ α.y∈ β (1)
⊢.*33·14.⊃⊢:. ᗡʻR⊂α. ⊃:xRz.⊃.z∈ α:
[*4·73] ⊃:xRz.≡.xRz.z∈ α (2)
⊢.(1).(2).⊃⊢:: Hp.⊃:. x{R| (α↑ β)}y. ≡:(∃ z).xRz.y∈ β:
[*10·35] ≡:(∃ z).xRz:y∈ β:
[*33·13] ≡:x∈ DʻR.y∈ β:
[*35·103] ≡:x(DʻR↑ β)y:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·881 -/
/- PM-VERBATIM-BEGIN PM1:✱35·882
✱35·882. ⊢:DʻR⊂β.⊃.(α↑ β)| R=α↑ ᗡʻR [Similar proof]
PM-VERBATIM-END PM1:✱35·882 -/
/- PM-VERBATIM-BEGIN PM1:✱35·89
✱35·89. ⊢:∃ !β.⊃.(α↑ β)| (β↑ γ)=(α↑ γ):∼∃ !β.⊃.(α↑ β)| (β↑ γ)=Λ̇
Dem.
⊢.*34·1.⊃⊢:. x{(α↑ β)| (β↑ γ)}z.
≡:(∃ y).x(α↑ β)y.y(β↑ γ)z:
[*35·103] ≡:(∃ y).x∈ α.y∈ β.y∈ β.z∈ γ:
[*4·24] ≡:(∃ y).x∈ α.y∈ β.z∈ γ:
[*10·35] ≡:∃ !β:x∈ α.z∈ γ:
[*35·103] ≡:∃ !β:x(α↑ γ)z (1)
⊢.(1).⊃⊢:: ∃ !β.⊃:x{(α↑ β)| (β↑ γ)}z.≡.x(α↑ γ)z:.
∼∃ !β.⊃:∼[x{(α↑ β)| (β↑ γ)}z]:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·89 -/
/- PM-VERBATIM-BEGIN PM1:✱35·891
✱35·891. ⊢:. ∃ !β.∨ .∼∃ !α:⊃.(α↑ β)| (β↑ α)=(α↑ α)
Dem.
⊢.*35·88.⊃⊢:∼∃ !α. ⊃.α↑ α=Λ̇.α↑ β=Λ̇.
[*34·32] ⊃.α↑ α=Λ̇.(α↑ β)| (β↑ α)=Λ̇.
[*21·24] ⊃.(α↑ α)=(α↑ β)| (β↑ α) (1)
⊢.(1).*35·89.⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·891 -/
/- PM-VERBATIM-BEGIN PM1:✱35·892
✱35·892. ⊢:(α↑ α)²=(α↑ α) [*35·891 α/β ]
PM-VERBATIM-END PM1:✱35·892 -/
/- PM-VERBATIM-BEGIN PM1:✱35·895
✱35·895. ⊢:α ∩ β=Λ.⊃.(α↑ β)²=Λ̇ [*35·68·82]
PM-VERBATIM-END PM1:✱35·895 -/
/- PM-VERBATIM-BEGIN PM1:✱35·9
✱35·9. ⊢.Dʻ(α↑ α)=ᗡʻ(α↑ α)=Cʻ(α↑ α)=α
Dem.
⊢.*35·85·86. ⊃⊢:∃ !α.⊃.Dʻ(α↑ α)=α.Dʻ(α↑ α)=α (1)
⊢.*35·88. ⊃⊢:∼∃ !α. ⊃.∼∃̇!(α↑ α).
[*33·29] ⊃.Dʻ(α↑ α)=Λ.ᗡʻ(α↑ α)=Λ.
[*24·51] ⊃.Dʻ(α↑ α)=α.ᗡʻ(α↑ α)=α (2)
⊢.(1).(2).*4·83. ⊃⊢.Dʻ(α↑ α)=ᗡʻ(α↑ α)=α.⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·9 -/
/- PM-VERBATIM-BEGIN PM1:✱35·91
✱35·91. ⊢:R⪽α↑ α.≡.CʻR⊂α
Dem.
⊢.*35·103. ⊃⊢:. R⪽α↑ α. ≡:xRy.⊃ₓ,y.x,y∈ α:
[*33·352] ≡:CʻR⊂α:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·91 -/
/- PM-VERBATIM-BEGIN PM1:✱35·92
✱35·92. ⊢:. (∃ α).P=α↑ α.⊃:R⪽P.≡.CʻR⊂ CʻP [*35·9·91]
PM-VERBATIM-END PM1:✱35·92 -/
/- PM-VERBATIM-BEGIN PM1:✱35·93
✱35·93. ⊢:(R).φ(DʻR).≡.(α).φα
Dem.
⊢.*33·12.*14·18. ⊃⊢:(α).φα.⊃.φ(DʻR):
[*10·11·21] ⊃⊢:(α).φα.⊃.(R).φ(DʻR) (1)
⊢.*10·1. ⊃⊢:(R).φ(DʻR).⊃.φ{Dʻ(α↑ α)}.
[*35·9] ⊃.φα:
[*10·11·21] ⊃⊢:(R).φ(DʻR).⊃.(α).φα (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱35·93 -/
/- PM-VERBATIM-BEGIN PM1:✱35·931
✱35·931. ⊢:(R).φ(ᗡʻR).≡.(α).φα [Proof as in *35·93]
PM-VERBATIM-END PM1:✱35·931 -/
/- PM-VERBATIM-BEGIN PM1:✱35·932
✱35·932. ⊢:(R).φ(CʻR).≡.(α).φα [Proof as in *35·93]
PM-VERBATIM-END PM1:✱35·932 -/
/- PM-VERBATIM-BEGIN PM1:✱35·94
✱35·94. ⊢:(∃ R).φ(DʻR).≡.(∃ α).φα [*35·93.Transp]
PM-VERBATIM-END PM1:✱35·94 -/
/- PM-VERBATIM-BEGIN PM1:✱35·941
✱35·941. ⊢:(∃ R).φ(ᗡʻR).≡.(∃ α).φα [*35·931. Transp]
PM-VERBATIM-END PM1:✱35·941 -/
/- PM-VERBATIM-BEGIN PM1:✱35·942
✱35·942. ⊢:(∃ R).φ(CʻR).≡.(∃ α).φα [*35·932.Transp]
PM-VERBATIM-END PM1:✱35·942 -/
