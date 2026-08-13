/-! # PM II ✱216 — derivatives (PG78255, opening) -/
/- PM-VERBATIM-BEGIN PM2:✱216·01
✱216·01. δₚʻα=ltₚʻʻCl exʻ(α∩CʻP) Df
PM-VERBATIM-END PM2:✱216·01 -/
/- PM-VERBATIM-BEGIN PM2:✱216·02
✱216·02. denseʻP=α̂(α−→minₚʻα⊂δₚʻα) Df
PM-VERBATIM-END PM2:✱216·02 -/
/- PM-VERBATIM-BEGIN PM2:✱216·03
✱216·03. closedʻP=α̂{Cl exʻ(α∩CʻP)⊂ᗡʻlimaxₚ.δₚʻα⊂α} Df
PM-VERBATIM-END PM2:✱216·03 -/
/- PM-VERBATIM-BEGIN PM2:✱216·04
✱216·04. perfʻP=denseʻP∩closedʻP Df
PM-VERBATIM-END PM2:✱216·04 -/
/- PM-VERBATIM-BEGIN PM2:✱216·05
✱216·05. ∇ʻP=P↏Dʻltₚ Df
PM-VERBATIM-END PM2:✱216·05 -/
/- PM-VERBATIM-BEGIN PM2:✱216·1
✱216·1. ⊢ : x∈δₚʻα .≡. (∃β).β⊂α∩CʻP.∃!β.x ltₚ β
PM-VERBATIM-END PM2:✱216·1 -/
/- PM-VERBATIM-BEGIN PM2:✱216·101
✱216·101. ⊢ : x∈δPʻα .≡. (∃β).β⊂α.∃!β.β⊂Pʻʻβ.x seqP β
PM-VERBATIM-END PM2:✱216·101 -/
/- PM-VERBATIM-BEGIN PM2:✱216·11
✱216·11. ⊢ . δPʻα⊂P̌ʻʻα
PM-VERBATIM-END PM2:✱216·11 -/
/- PM-VERBATIM-BEGIN PM2:✱216·111
✱216·111. ⊢ . δPʻα⊂ᗡʻP
PM-VERBATIM-END PM2:✱216·111 -/
/- PM-VERBATIM-BEGIN PM2:✱216·12
✱216·12. ⊢ . δPʻα=δPʻ(α∩CʻP)
PM-VERBATIM-END PM2:✱216·12 -/
/- PM-VERBATIM-BEGIN PM2:✱216·13
✱216·13. ⊢ : P∈Ser .⊃: x∈δPʻα .≡: x∈ᗡʻP : yPx .⊃y. ∃!α∩←Pʻy∩→Pʻx
PM-VERBATIM-END PM2:✱216·13 -/
/- PM-VERBATIM-BEGIN PM2:✱216·14
✱216·14. ⊢ : P∈Ser .⊃. δ²ʻα⊂δPʻα
PM-VERBATIM-END PM2:✱216·14 -/
/- PM-VERBATIM-BEGIN PM2:✱216·15
✱216·15. ⊢ : α⊂β .⊃. δPʻα⊂δPʻβ
PM-VERBATIM-END PM2:✱216·15 -/
/- PM-VERBATIM-BEGIN PM2:✱216·16
✱216·16. ⊢ : P∈trans∩connex .⊃. δPʻα=δPʻ(α−→minPʻα)
PM-VERBATIM-END PM2:✱216·16 -/
/- PM-VERBATIM-BEGIN PM2:✱216·2
✱216·2. ⊢ . δPʻCʻP=DʻltP−→BʻP
PM-VERBATIM-END PM2:✱216·2 -/
/- PM-VERBATIM-BEGIN PM2:✱216·21
✱216·21. ⊢ : P∈ᗡʻʻʻJ∩connex .⊃. δPʻCʻP=ᗡʻP−ᗡʻ(P−̇P²)
PM-VERBATIM-END PM2:✱216·21 -/
/- PM-VERBATIM-BEGIN PM2:✱216·22
✱216·22. ⊢ : P∈ᗡʻʻʻJ∩connex.P⊂P² .⊃. δPʻCʻP=ᗡʻP
PM-VERBATIM-END PM2:✱216·22 -/
/- PM-VERBATIM-BEGIN PM2:✱216·23
✱216·23. ⊢ : P∈trans .⊃. δPʻCʻP=seqPʻʻᗡʻsgmʻP=ltPʻʻᗡʻsgmʻP
PM-VERBATIM-END PM2:✱216·23 -/
/- PM-VERBATIM-BEGIN PM2:✱216·3
✱216·3. ⊢ : α∈denseʻP .≡. α−→minPʻα⊂δPʻα
PM-VERBATIM-END PM2:✱216·3 -/
/- PM-VERBATIM-BEGIN PM2:✱216·31
✱216·31. ⊢ : α∈denseʻP .≡. α⊂CʻP.α∩P̌ʻʻα⊂δPʻα
PM-VERBATIM-END PM2:✱216·31 -/
/- PM-VERBATIM-BEGIN PM2:✱216·32
✱216·32. ⊢ : α∈closedʻP .≡. Cl exʻ(α∩CʻP)⊂ᗡʻlimaxP.δPʻα⊂α
PM-VERBATIM-END PM2:✱216·32 -/
/- PM-VERBATIM-BEGIN PM2:✱216·33
✱216·33. ⊢ : α∈closedʻP .≡: β⊂α.∃!β.β⊂Pʻʻβ .⊃β. ∃!→ltPʻβ.→ltPʻβ⊂α
PM-VERBATIM-END PM2:✱216·33 -/
/- PM-VERBATIM-BEGIN PM2:✱216·34
✱216·34. ⊢ : P∈connex .⊃: α∈closedʻP .≡: β⊂α.∃!β.β⊂Pʻʻβ .⊃β. ltPʻβ∈α
PM-VERBATIM-END PM2:✱216·34 -/
/- PM-VERBATIM-BEGIN PM2:✱216·35
✱216·35. ⊢ : P∈Ser.Cl exʻα⊂ᗡʻlimaxP .⊃. Cl exʻδPʻα⊂ᗡʻlimaxP
PM-VERBATIM-END PM2:✱216·35 -/
/- PM-VERBATIM-BEGIN PM2:✱216·36
✱216·36. ⊢ : α∈perfʻP .≡. α∈denseʻP∩closedʻP
PM-VERBATIM-END PM2:✱216·36 -/
/- PM-VERBATIM-BEGIN PM2:✱216·37
✱216·37. ⊢ : α∈perfʻP .≡. Cl exʻα⊂ᗡʻlimaxP.δPʻα=α−→minPʻα
PM-VERBATIM-END PM2:✱216·37 -/
/- PM-VERBATIM-BEGIN PM2:✱216·371
✱216·371. ⊢ : α∈perfʻP .≡. Cl exʻα⊂ᗡʻlimaxP.α⊂CʻP.δPʻα=α∩P̌ʻʻα
PM-VERBATIM-END PM2:✱216·371 -/
/- PM-VERBATIM-BEGIN PM2:✱216·38
✱216·38. ⊢ : P∈trans∩connex.α∈denseʻP .⊃. δPʻα∈denseʻP.δPʻα⊂δPʻδPʻα
PM-VERBATIM-END PM2:✱216·38 -/
/- PM-VERBATIM-BEGIN PM2:✱216·381
✱216·381. ⊢ : P∈Ser.α∈denseʻP .⊃. δPʻα=δPʻδPʻα.→minPʻδPʻα=Λ
PM-VERBATIM-END PM2:✱216·381 -/
/- PM-VERBATIM-BEGIN PM2:✱216·382
✱216·382. ⊢ : P∈Ser.α∈denseʻP.Cl exʻα⊂ᗡʻlimaxP .⊃. δPʻα∈perfʻP
PM-VERBATIM-END PM2:✱216·382 -/
/- PM-VERBATIM-BEGIN PM2:✱216·4
✱216·4. ⊢ : S∈P smor Q .⊃. δPʻα=SʻʻδQʻŠʻʻα.ŠʻʻδPʻα=δQʻŠʻʻα
PM-VERBATIM-END PM2:✱216·4 -/
/- PM-VERBATIM-BEGIN PM2:✱216·401
✱216·401. ⊢ : S∈P smor Q .⊃. P↏δPʻα=S;(Q↏δQʻŠʻʻα)
PM-VERBATIM-END PM2:✱216·401 -/
/- PM-VERBATIM-BEGIN PM2:✱216·41
✱216·41. ⊢ : S∈P smor Q.α⊂CʻP .⊃: α∈denseʻP .≡. Šʻʻα∈denseʻQ
PM-VERBATIM-END PM2:✱216·41 -/
/- PM-VERBATIM-BEGIN PM2:✱216·411
✱216·411. ⊢ : S∈P smor Q.α⊂CʻP .⊃: α∈closedʻP .≡. Šʻʻα∈closedʻQ
PM-VERBATIM-END PM2:✱216·411 -/
/- PM-VERBATIM-BEGIN PM2:✱216·412
✱216·412. ⊢ : S∈P smor Q.α⊂CʻP .⊃: α∈perfʻP .≡. Šʻʻα∈perfʻQ
PM-VERBATIM-END PM2:✱216·412 -/
/- PM-VERBATIM-BEGIN PM2:✱216·5
✱216·5. ⊢ : P∈Ser .⊃. ᗡʻςʻP−→PʻʻCʻP⊂δ(ςʻP)ʻ→PʻʻCʻP
PM-VERBATIM-END PM2:✱216·5 -/
/- PM-VERBATIM-BEGIN PM2:✱216·51
✱216·51. ⊢ : P∈Ser .⊃. δ(ςʻP)ʻ→PʻʻCʻP=δ(ςʻP)ʻCʻςʻP=Dʻlt(ςʻP)−ιʻΛ=ᗡʻsgmʻP
PM-VERBATIM-END PM2:✱216·51 -/
/- PM-VERBATIM-BEGIN PM2:✱216·52
✱216·52. ⊢ : P∈Ser.∃̇!P.α⊂CʻP .⊃. δ(ςʻP)ʻ→Pʻʻα=Pʻʻʻ(Cl exʻα−ᗡʻmaxP)
PM-VERBATIM-END PM2:✱216·52 -/
/- PM-VERBATIM-BEGIN PM2:✱216·521
✱216·521. ⊢ : P∈Ser.α⊂CʻP .⊃. →Pʻʻ(α−→minPʻα)=→Pʻʻα−→min(ςʻP)ʻ→Pʻʻα
PM-VERBATIM-END PM2:✱216·521 -/
/- PM-VERBATIM-BEGIN PM2:✱216·53
✱216·53. ⊢ : P∈Ser.∃̇!P.α⊂CʻP .⊃: α∈denseʻP .≡. →Pʻʻα∈denseʻςʻP
PM-VERBATIM-END PM2:✱216·53 -/
/- PM-VERBATIM-BEGIN PM2:✱216·54
✱216·54. ⊢ : P∈Ser.∃̇!P.α⊂CʻP .⊃: α∈closedʻP .≡. δ(ςʻP)ʻ→Pʻʻα⊂→Pʻʻα
PM-VERBATIM-END PM2:✱216·54 -/
/- PM-VERBATIM-BEGIN PM2:✱216·55
✱216·55. ⊢ : P∈Ser.∃̇!P.α⊂CʻP .⊃: α∈closedʻP .≡. →Pʻʻα∈closedʻςʻP
PM-VERBATIM-END PM2:✱216·55 -/
/- PM-VERBATIM-BEGIN PM2:✱216·56
✱216·56. ⊢ : P∈Ser.∃̇!P.α⊂CʻP .⊃: α∈perfʻP .≡. →Pʻʻα∈perfʻςʻP .≡. δ(ςʻP)ʻ→Pʻʻα=→Pʻʻα−→min(ςʻP)ʻ→Pʻʻα
PM-VERBATIM-END PM2:✱216·56 -/
/- PM-VERBATIM-BEGIN PM2:✱216·6
✱216·6. ⊢ : x(∇ʻP)y .≡. x,y∈DʻltP.xPy
PM-VERBATIM-END PM2:✱216·6 -/
/- PM-VERBATIM-BEGIN PM2:✱216·601
✱216·601. ⊢ : x∈DʻltP∩ᗡʻP.P∈connex.E!BʻP .⊃. (BʻP)(∇ʻP)x
PM-VERBATIM-END PM2:✱216·601 -/
/- PM-VERBATIM-BEGIN PM2:✱216·602
✱216·602. ⊢ : P∈connex.E!BʻP .⊃. ᗡʻ∇ʻP=DʻltP−→BʻP=δPʻCʻP
PM-VERBATIM-END PM2:✱216·602 -/
/- PM-VERBATIM-BEGIN PM2:✱216·603
✱216·603. ⊢ : P∈connex.∃̇!∇ʻP .⊃. Cʻ∇ʻP=DʻltP
PM-VERBATIM-END PM2:✱216·603 -/
/- PM-VERBATIM-BEGIN PM2:✱216·61
✱216·61. ⊢ : P∈Ser.E!BʻP .⊃. ᗡʻ∇ʻP=ᗡʻP−ᗡʻP₁
PM-VERBATIM-END PM2:✱216·61 -/
/- PM-VERBATIM-BEGIN PM2:✱216·611
✱216·611. ⊢ : P∈Ser.∃̇!∇ʻP .⊃. Cʻ∇ʻP=CʻP−ᗡʻP₁=δPʻCʻP∪→BʻP
PM-VERBATIM-END PM2:✱216·611 -/
/- PM-VERBATIM-BEGIN PM2:✱216·612
✱216·612. ⊢ : P∈Ser .⊃. ᗡʻ∇ʻP⊂ᗡʻP−ᗡʻP₁
PM-VERBATIM-END PM2:✱216·612 -/
/- PM-VERBATIM-BEGIN PM2:✱216·62
✱216·62. ⊢ : P∈Ser.∃̇!∇ʻP .⊃. Cʻ∇ʻP=seqPʻʻCʻsgmʻP=ltPʻʻCʻsgmʻP
PM-VERBATIM-END PM2:✱216·62 -/
/- PM-VERBATIM-BEGIN PM2:✱216·621
✱216·621. ⊢ : P∈Ser.∃̇!∇ʻP .⊃. ∃̇!sgmʻP.∃!ᗡʻP−ᗡʻP₁
PM-VERBATIM-END PM2:✱216·621 -/
