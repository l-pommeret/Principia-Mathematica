/-! PM II ✱207, canonical Gutenberg 78255, opening macro-lot. -/
/- PM-VERBATIM-BEGIN PM2:✱207·01
✱207·01. lt_P=lt(P)=seq_P↾(−ᗡʻmax_P) Df
PM-VERBATIM-END PM2:✱207·01 -/
/- PM-VERBATIM-BEGIN PM2:✱207·02
✱207·02. tl_P=tl(P)=prec_P↾(−ᗡʻmin_P) Df
PM-VERBATIM-END PM2:✱207·02 -/
/- PM-VERBATIM-BEGIN PM2:✱207·03
✱207·03. limax_P=max_P∪̇lt_P Df
PM-VERBATIM-END PM2:✱207·03 -/
/- PM-VERBATIM-BEGIN PM2:✱207·04
✱207·04. limin_P=min_P∪̇tl_P Df
PM-VERBATIM-END PM2:✱207·04 -/
/- PM-VERBATIM-BEGIN PM2:✱207·121
✱207·121. ⊢ : α∩CʻP⊂Pʻʻα .⊃. lt→_Pʻα=seq→_Pʻα
PM-VERBATIM-END PM2:✱207·121 -/
/- PM-VERBATIM-BEGIN PM2:✱207·13
✱207·13. ⊢ : ∃!lt→_Pʻα .≡. ∼∃!max→_Pʻα
PM-VERBATIM-END PM2:✱207·13 -/
/- PM-VERBATIM-BEGIN PM2:✱207·14
✱207·14. ⊢ : ∃!max→_Pʻα .∨. ∃!seq→_Pʻα
PM-VERBATIM-END PM2:✱207·14 -/
/- PM-VERBATIM-BEGIN PM2:✱207·15
✱207·15. ⊢ : x∈lt→_Pʻα .≡. x∈lt→_Pʻ(α∩CʻP)
PM-VERBATIM-END PM2:✱207·15 -/
/- PM-VERBATIM-BEGIN PM2:✱207·16
✱207·16. ⊢ . lt→_Pʻα=lt→_Pʻ(α∩CʻP)
PM-VERBATIM-END PM2:✱207·16 -/
/- PM-VERBATIM-BEGIN PM2:✱207·17
✱207·17. ⊢ . lt→_PʻΛ=B→ʻP
PM-VERBATIM-END PM2:✱207·17 -/
/- PM-VERBATIM-BEGIN PM2:✱207·18
✱207·18. ⊢ : ᗡʻP⊂Dʻlt_P .≡. CʻP=Dʻlt_P
PM-VERBATIM-END PM2:✱207·18 -/
/- PM-VERBATIM-BEGIN PM2:✱207·21
✱207·21. ⊢ : P²⊂̇J . x∈CʻP . α∩CʻP⊂P→ʻx . P→ʻx⊂Pʻʻα .⊃. x lt_P α
PM-VERBATIM-END PM2:✱207·21 -/
/- PM-VERBATIM-BEGIN PM2:✱207·22
✱207·22. ⊢ : P∈connex . P²⊂̇J .⊃. lt→_Pʻα⊂CʻP
PM-VERBATIM-END PM2:✱207·22 -/
/- PM-VERBATIM-BEGIN PM2:✱207·23
✱207·23. ⊢ : P∈Ser .⊃. lt→_Pʻα=CʻP∩x̂(P→ʻx=Pʻʻα . α∩CʻP⊂Pʻʻα)
PM-VERBATIM-END PM2:✱207·23 -/
/- PM-VERBATIM-BEGIN PM2:✱207·231
✱207·231. ⊢ : P∈Ser . ∃!lt→_Pʻα .⊃. lt→_Pʻα=ιʻlt_Pʻα
PM-VERBATIM-END PM2:✱207·231 -/
/- PM-VERBATIM-BEGIN PM2:✱207·232
✱207·232. ⊢ : P∈Ser .⊃: x=lt_Pʻα .≡. x∈CʻP−α . P→ʻx=Pʻʻα
PM-VERBATIM-END PM2:✱207·232 -/
/- PM-VERBATIM-BEGIN PM2:✱207·24
✱207·24. ⊢ : P∈connex .⊃. lt→_Pʻα∈0∪1 . lt_P∈1→Cls
PM-VERBATIM-END PM2:✱207·24 -/
/- PM-VERBATIM-BEGIN PM2:✱207·25
✱207·25. ⊢ : P∈trans . β⊂Pʻʻα .⊃. lt→_Pʻ(α∪β)=lt→_Pʻα
PM-VERBATIM-END PM2:✱207·25 -/
/- PM-VERBATIM-BEGIN PM2:✱207·26
✱207·26. ⊢ : P∈trans . ∼(yPy) . ∃!lt→_Pʻβ .⊃. lt→_Pʻβ⊂lt→_Pʻ(β∪ιʻy)
PM-VERBATIM-END PM2:✱207·26 -/
/- PM-VERBATIM-BEGIN PM2:✱207·262
✱207·262. ⊢ : P∈trans∩connex . ∃!lt→_Pʻβ .⊃. lt→_Pʻβ⊂lt→_Pʻ(β∪ιʻy)
PM-VERBATIM-END PM2:✱207·262 -/
/- PM-VERBATIM-BEGIN PM2:✱207·263
✱207·263. ⊢ : P∈trans∩connex .⊃. lt→_Pʻβ⊂lt→_Pʻ(β∪γ)
PM-VERBATIM-END PM2:✱207·263 -/
/- PM-VERBATIM-BEGIN PM2:✱207·31
✱207·31. ⊢ : P⊂̇J . x∈CʻP−ᗡʻ(P−̇P²) .⊃. x lt_P P→ʻx
PM-VERBATIM-END PM2:✱207·31 -/
/- PM-VERBATIM-BEGIN PM2:✱207·34
✱207·34. ⊢ : P∈connex . x lt_P α .⊃. x lt_P P→ʻx . x∉ᗡʻ(P−̇P²)
PM-VERBATIM-END PM2:✱207·34 -/
/- PM-VERBATIM-BEGIN PM2:✱207·35
✱207·35. ⊢ : P∈RlʻJ∩connex .⊃. Dʻlt_P=CʻP−ᗡʻ(P−̇P²)
PM-VERBATIM-END PM2:✱207·35 -/
/- PM-VERBATIM-BEGIN PM2:✱207·4
✱207·4. ⊢ : x limax_P α .≡: x max_P α .∨. x lt_P α
PM-VERBATIM-END PM2:✱207·4 -/
/- PM-VERBATIM-BEGIN PM2:✱207·42
✱207·42. ⊢ : ∃!max→_Pʻα .⊃. limax→_Pʻα=max→_Pʻα
PM-VERBATIM-END PM2:✱207·42 -/
/- PM-VERBATIM-BEGIN PM2:✱207·43
✱207·43. ⊢ : max→_Pʻα=Λ .⊃. limax→_Pʻα=seq→_Pʻα
PM-VERBATIM-END PM2:✱207·43 -/
/- PM-VERBATIM-BEGIN PM2:✱207·44
✱207·44. ⊢ . ᗡʻlimax_P=ᗡʻmax_P∪ᗡʻlt_P=ᗡʻmax_P∪ᗡʻseq_P
PM-VERBATIM-END PM2:✱207·44 -/
/- PM-VERBATIM-BEGIN PM2:✱207·45
✱207·45. ⊢ . limax→_Pʻα=max→_Pʻα∪lt→_Pʻα
PM-VERBATIM-END PM2:✱207·45 -/
/- PM-VERBATIM-BEGIN PM2:✱207·46
✱207·46. ⊢ : x=limax_Pʻα .≡: x=max_Pʻα .∨. x=lt_Pʻα
PM-VERBATIM-END PM2:✱207·46 -/
/- PM-VERBATIM-BEGIN PM2:✱207·47
✱207·47. ⊢ : ∃!lt→_Pʻα .≡. ∃!limax→_Pʻα
PM-VERBATIM-END PM2:✱207·47 -/
/- PM-VERBATIM-BEGIN PM2:✱207·48
✱207·48. ⊢ . limax→_Pʻα=limax→_Pʻ(α∩CʻP)
PM-VERBATIM-END PM2:✱207·48 -/
/- PM-VERBATIM-BEGIN PM2:✱207·481
✱207·481. ⊢ : P∈trans .⊃. limax→_Pʻα⊂limax→_Pʻ(α∪β)
PM-VERBATIM-END PM2:✱207·481 -/
/- PM-VERBATIM-BEGIN PM2:✱207·482
✱207·482. ⊢ : P∈Ser . α⊂CʻP . α=limax_Pʻα .⊃. α⊂P→∗ʻα
PM-VERBATIM-END PM2:✱207·482 -/
/- PM-VERBATIM-BEGIN PM2:✱207·5
✱207·5. ⊢ : P∈Ser .⊃. limax→_Pʻα=seq→_PʻPʻʻα
PM-VERBATIM-END PM2:✱207·5 -/
/- PM-VERBATIM-BEGIN PM2:✱207·51
✱207·51. ⊢ : P∈Ser .⊃: x=limax_Pʻα .≡. x∈CʻP . P→ʻx=Pʻʻα
PM-VERBATIM-END PM2:✱207·51 -/
/- PM-VERBATIM-BEGIN PM2:✱207·52
✱207·52. ⊢ : P∈Ser . ∃!Pʻʻα .⊃: x=limax_Pʻα .≡. P→ʻx=Pʻʻα
PM-VERBATIM-END PM2:✱207·52 -/
/- PM-VERBATIM-BEGIN PM2:✱207·521
✱207·521. ⊢ : P∈Ser .⊃. limax→_Pʻα⊂CʻP
PM-VERBATIM-END PM2:✱207·521 -/
/- PM-VERBATIM-BEGIN PM2:✱207·53
✱207·53. ⊢ : P∈Ser . κ⊂ᗡʻlimax_P .⊃. limax→_Pʻlimax_Pʻʻκ=limax→_Pʻsʻκ
PM-VERBATIM-END PM2:✱207·53 -/
/- PM-VERBATIM-BEGIN PM2:✱207·54
✱207·54. ⊢ : P∈Ser . κ⊂ᗡʻlt_P .⊃. limax→_Pʻlt_Pʻʻκ=limax→_Pʻsʻκ
PM-VERBATIM-END PM2:✱207·54 -/
/- PM-VERBATIM-BEGIN PM2:✱207·55
✱207·55. ⊢ : P∈Ser .⊃. limax_Pʻʻκ⊂P∗ʻʻsʻκ
PM-VERBATIM-END PM2:✱207·55 -/
/- PM-VERBATIM-BEGIN PM2:✱207·6
✱207·6. ⊢ : S∈P smor̄ Q .⊃. lt→_Pʻα=Sʻʻlt→_QʻCnvʻSʻʻα
PM-VERBATIM-END PM2:✱207·6 -/
/- PM-VERBATIM-BEGIN PM2:✱207·61
✱207·61. ⊢ : S∈P smor̄ Q .⊃: E!lt_Pʻα .≡. E!lt_QʻCnvʻSʻʻα
PM-VERBATIM-END PM2:✱207·61 -/
/- PM-VERBATIM-BEGIN PM2:✱207·62
✱207·62. ⊢ : S∈P smor̄ Q . E!lt_Pʻα .⊃. lt_Pʻα=Sʻlt_QʻCnvʻSʻʻα
PM-VERBATIM-END PM2:✱207·62 -/
/- PM-VERBATIM-BEGIN PM2:✱207·63
✱207·63. ⊢ : S∈P smor̄ Q .⊃. lt_Pʻʻκ=Sʻʻlt_QʻʻCnvʻSʻʻʻκ
PM-VERBATIM-END PM2:✱207·63 -/
