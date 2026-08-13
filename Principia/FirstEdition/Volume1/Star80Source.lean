/-! # ✱80 — Selections, first macro-lot (Gutenberg 78050). -/
/- PM-VERBATIM-BEGIN PM1:✱80·01
✱80·01. P_Δ = λ̂κ̂{λ=(1→Cls) ∩ RlʻP ∩ ᗡ⃖ʻκ} Df
PM-VERBATIM-END PM1:✱80·01 -/
/- PM-VERBATIM-BEGIN PM1:✱80·1
✱80·1. ⊢ : λ P_Δ κ .≡. λ=(1→Cls) ∩ RlʻP ∩ ᗡ⃖ʻκ
PM-VERBATIM-END PM1:✱80·1 -/
/- PM-VERBATIM-BEGIN PM1:✱80·11
✱80·11. ⊢. P_Δʻκ=(1→Cls) ∩ RlʻP ∩ ᗡ⃖ʻκ
PM-VERBATIM-END PM1:✱80·11 -/
/- PM-VERBATIM-BEGIN PM1:✱80·12
✱80·12. ⊢. E!P_Δʻκ
PM-VERBATIM-END PM1:✱80·12 -/
/- PM-VERBATIM-BEGIN PM1:✱80·13
✱80·13. ⊢ : λ P_Δʻκ .≡. λ=P_Δʻκ
PM-VERBATIM-END PM1:✱80·13 -/
/- PM-VERBATIM-BEGIN PM1:✱80·14
✱80·14. ⊢ : R∈P_Δʻκ .≡. R∈1→Cls . R⊂P . ᗡʻR=κ
PM-VERBATIM-END PM1:✱80·14 -/
/- PM-VERBATIM-BEGIN PM1:✱80·15
✱80·15. ⊢ : P⊂Q .⊃. P_Δʻκ⊂Q_Δʻκ
PM-VERBATIM-END PM1:✱80·15 -/
/- PM-VERBATIM-BEGIN PM1:✱80·16
✱80·16. ⊢ : R∈P_Δʻκ . R⊂Q .⊃. R∈Q_Δʻκ
PM-VERBATIM-END PM1:✱80·16 -/
/- PM-VERBATIM-BEGIN PM1:✱80·17
✱80·17. ⊢ : Q⊂P .⊃. Q_Δʻκ=P_Δʻκ ∩ RlʻQ
PM-VERBATIM-END PM1:✱80·17 -/
/- PM-VERBATIM-BEGIN PM1:✱80·2
✱80·2. ⊢ : ∃!P_Δʻκ .⊃. κ⊂ᗡʻP
PM-VERBATIM-END PM1:✱80·2 -/
/- PM-VERBATIM-BEGIN PM1:✱80·21
✱80·21. ⊢ : ∼(κ⊂ᗡʻP) .⊃. P_Δʻκ=Λ
PM-VERBATIM-END PM1:✱80·21 -/
/- PM-VERBATIM-BEGIN PM1:✱80·22
✱80·22. ⊢ : P↾κ=Q↾κ .⊃. P_Δʻκ=Q_Δʻκ
PM-VERBATIM-END PM1:✱80·22 -/
/- PM-VERBATIM-BEGIN PM1:✱80·23
✱80·23. ⊢. P_Δʻκ=(P↾κ)_Δʻκ
PM-VERBATIM-END PM1:✱80·23 -/
/- PM-VERBATIM-BEGIN PM1:✱80·24
✱80·24. ⊢ : κ⊂ᗡʻP . Q=P↾κ .⊃. P_Δʻκ=Q_ΔʻᗡʻQ
PM-VERBATIM-END PM1:✱80·24 -/
/- PM-VERBATIM-BEGIN PM1:✱80·25
✱80·25. ⊢ : ∃!P_Δʻκ . Q=P↾κ .⊃. P_Δʻκ=Q_ΔʻᗡʻQ
PM-VERBATIM-END PM1:✱80·25 -/
/- PM-VERBATIM-BEGIN PM1:✱80·26
✱80·26. ⊢. P_ΔʻΛ=ιʻΛ̇
PM-VERBATIM-END PM1:✱80·26 -/
/- PM-VERBATIM-BEGIN PM1:✱80·27
✱80·27. ⊢ : ∃!κ .⊃. Λ̇_Δʻκ=Λ
PM-VERBATIM-END PM1:✱80·27 -/
/- PM-VERBATIM-BEGIN PM1:✱80·28
✱80·28. ⊢ : ∃!κ .⊃. Λ̇∼∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·28 -/
/- PM-VERBATIM-BEGIN PM1:✱80·29
✱80·29. ⊢ : R∈P_Δʻκ .⊃. R=R↾κ
PM-VERBATIM-END PM1:✱80·29 -/
/- PM-VERBATIM-BEGIN PM1:✱80·291
✱80·291. ⊢ : R∈P_Δʻκ .⊃. R⊂P↾κ
PM-VERBATIM-END PM1:✱80·291 -/
/- PM-VERBATIM-BEGIN PM1:✱80·3
✱80·3. ⊢ : R∈P_Δʻκ . y∈κ .⊃. E!Rʻy
PM-VERBATIM-END PM1:✱80·3 -/
/- PM-VERBATIM-BEGIN PM1:✱80·31
✱80·31. ⊢ : R∈P_Δʻκ . y∈κ .⊃. Rʻy∈P⃗ʻy
PM-VERBATIM-END PM1:✱80·31 -/
/- PM-VERBATIM-BEGIN PM1:✱80·32
✱80·32. ⊢ : R∈P_Δʻκ .⊃: y∈κ .≡. E!Rʻy .≡. Rʻy∈P⃗ʻy
PM-VERBATIM-END PM1:✱80·32 -/
/- PM-VERBATIM-BEGIN PM1:✱80·33
✱80·33. ⊢ : R∈P_Δʻκ .⊃. DʻR⊂Pʻʻκ
PM-VERBATIM-END PM1:✱80·33 -/
/- PM-VERBATIM-BEGIN PM1:✱80·34
✱80·34. ⊢ : R∈P_Δʻκ .⊃. E‼Rʻʻκ . Rʻʻκ=DʻR
PM-VERBATIM-END PM1:✱80·34 -/
/- PM-VERBATIM-BEGIN PM1:✱80·35
✱80·35. ⊢ : R∈P_Δʻκ .⊃. DʻR=x̂{(∃y).y∈κ.x=Rʻy}
PM-VERBATIM-END PM1:✱80·35 -/
/- PM-VERBATIM-BEGIN PM1:✱80·36
✱80·36. ⊢ : R,S∈P_Δʻκ .⊃. R↾α ⊍ S↾−α∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·36 -/
/- PM-VERBATIM-BEGIN PM1:✱80·4
✱80·4. ⊢ : R∈P_Δʻκ.y∈κ.xRy.x′Py .⊃. {(R−x↓y)⊍x′↓y}∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·4 -/
/- PM-VERBATIM-BEGIN PM1:✱80·41
✱80·41. ⊢ : R∈P_Δʻκ.y∈κ.x′Py .⊃. [{R−(Rʻy)↓y}⊍x′↓y]∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·41 -/
/- PM-VERBATIM-BEGIN PM1:✱80·42
✱80·42. ⊢ : ∃!P_Δʻκ .⊃. ṡʻP_Δʻκ=P↾κ
PM-VERBATIM-END PM1:✱80·42 -/
/- PM-VERBATIM-BEGIN PM1:✱80·43
✱80·43. ⊢ : xPy .≡. x↓y∈P_Δʻιʻy
PM-VERBATIM-END PM1:✱80·43 -/
/- PM-VERBATIM-BEGIN PM1:✱80·44
✱80·44. ⊢ : R∈P_Δʻιʻy .⊃. R=(Rʻy)↓y
PM-VERBATIM-END PM1:✱80·44 -/
/- PM-VERBATIM-BEGIN PM1:✱80·45
✱80·45. ⊢. P_Δʻιʻy=↓yʻʻP⃗ʻy
PM-VERBATIM-END PM1:✱80·45 -/
/- PM-VERBATIM-BEGIN PM1:✱80·46
✱80·46. ⊢ : ∃!P_Δʻιʻy .≡. ∃!P⃗ʻy .≡. y∈ᗡʻP
PM-VERBATIM-END PM1:✱80·46 -/
/- PM-VERBATIM-BEGIN PM1:✱80·5
✱80·5. ⊢ : κ∩λ=Λ.R∈P_Δʻκ.S∈Q_Δʻλ .⊃. R⊍S∈(P⊍Q)_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·5 -/
/- PM-VERBATIM-BEGIN PM1:✱80·51
✱80·51. ⊢ : λ∩ᗡʻP=Λ.R∈P_Δʻκ.S∈Q_Δʻλ .⊃. R⊍S∈(P⊍Q)_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·51 -/
/- PM-VERBATIM-BEGIN PM1:✱80·511
✱80·511. ⊢ : κ∩ᗡʻQ=Λ.λ∩ᗡʻP=Λ.M∈(P⊍Q)_Δʻ(κ∪λ) .⊃. M↾κ∈P_Δʻκ.M↾λ∈Q_Δʻλ
PM-VERBATIM-END PM1:✱80·511 -/
/- PM-VERBATIM-BEGIN PM1:✱80·52
✱80·52. ⊢ : κ∩ᗡʻQ=Λ.λ∩ᗡʻP=Λ.M∈(P⊍Q)_Δʻ(κ∪λ) .⊃. M=(M↾κ)⊍(M↾λ)
PM-VERBATIM-END PM1:✱80·52 -/
/- PM-VERBATIM-BEGIN PM1:✱80·53
✱80·53. ⊢ : κ∩ᗡʻQ=Λ.λ∩ᗡʻP=Λ .⊃. (P⊍Q)_Δʻ(κ∪λ)⊂P_Δʻκ ⊍ Q_Δʻλ
PM-VERBATIM-END PM1:✱80·53 -/
/- PM-VERBATIM-BEGIN PM1:✱80·54
✱80·54. ⊢ : κ∩ᗡʻQ=Λ.λ∩ᗡʻP=Λ .⊃. (P⊍Q)_Δʻ(κ∪λ)=P_Δʻκ ⊍ Q_Δʻλ
PM-VERBATIM-END PM1:✱80·54 -/
/- PM-VERBATIM-BEGIN PM1:✱80·6
✱80·6. ⊢ : R∈P_Δʻκ . λ⊂κ .⊃. R↾λ∈P_Δʻλ
PM-VERBATIM-END PM1:✱80·6 -/
/- PM-VERBATIM-BEGIN PM1:✱80·61
✱80·61. ⊢ : M↾κ∈P_Δʻκ . M↾λ∈P_Δʻλ .⊃. M↾(κ∪λ)∈P_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·61 -/
/- PM-VERBATIM-BEGIN PM1:✱80·62
✱80·62. ⊢ : M∈P_Δʻ(κ∪λ) .⊃. M↾κ∈P_Δʻκ . M↾λ∈P_Δʻλ
PM-VERBATIM-END PM1:✱80·62 -/
/- PM-VERBATIM-BEGIN PM1:✱80·621
✱80·621. ⊢ : M↾(κ∪λ)∈P_Δʻ(κ∪λ) .⊃. M↾κ∈P_Δʻκ . M↾λ∈P_Δʻλ
PM-VERBATIM-END PM1:✱80·621 -/
/- PM-VERBATIM-BEGIN PM1:✱80·63
✱80·63. ⊢ : M↾κ∈P_Δʻκ . M↾λ∈P_Δʻλ .≡. M↾(κ∪λ)∈P_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·63 -/
/- PM-VERBATIM-BEGIN PM1:✱80·64
✱80·64. ⊢ : ᗡʻM=κ∪λ .⊃: M↾κ∈P_Δʻκ . M↾λ∈P_Δʻλ .≡. M∈P_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·64 -/
/- PM-VERBATIM-BEGIN PM1:✱80·65
✱80·65. ⊢ : κ∩λ=Λ.R∈P_Δʻκ.S∈P_Δʻλ .⊃. R⊍S∈P_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·65 -/
/- PM-VERBATIM-BEGIN PM1:✱80·651
✱80·651. ⊢ : R∈P_Δʻκ.S∈P_Δʻλ .⊃. R⊍S↾(λ−κ)∈P_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·651 -/
/- PM-VERBATIM-BEGIN PM1:✱80·66
✱80·66. ⊢ : κ∩λ=Λ .⊃: M∈P_Δʻ(κ∪λ) .≡. (∃R,S).R∈P_Δʻκ.S∈P_Δʻλ.M=R⊍S
PM-VERBATIM-END PM1:✱80·66 -/
/- PM-VERBATIM-BEGIN PM1:✱80·661
✱80·661. ⊢ : κ∩λ=Λ.R∈P_Δʻκ.S∈P_Δʻλ .⊃. R=(R⊍S)↾κ . S=(R⊍S)↾λ
PM-VERBATIM-END PM1:✱80·661 -/
/- PM-VERBATIM-BEGIN PM1:✱80·67
✱80·67. ⊢ : κ∩λ=Λ .⊃: R∈P_Δʻκ.S∈P_Δʻλ .≡. R⊍S∈P_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·67 -/
/- PM-VERBATIM-BEGIN PM1:✱80·68
✱80·68. ⊢ : R∈P_Δʻ(κ−ιʻy).y∈κ.xPy .⊃. R⊍x↓y∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·68 -/
/- PM-VERBATIM-BEGIN PM1:✱80·69
✱80·69. ⊢ : ∃!P_Δʻ(κ∪λ) .≡. ∃!P_Δʻκ . ∃!P_Δʻλ
PM-VERBATIM-END PM1:✱80·69 -/
/- PM-VERBATIM-BEGIN PM1:✱80·7
✱80·7. ⊢ : ᗡʻP∩ᗡʻQ=Λ.κ⊂ᗡʻP.λ⊂ᗡʻQ.M∈(P⊍Q)_Δʻ(κ∪λ) .⊃. M−Q∈P_Δʻκ.M−P∈Q_Δʻλ
PM-VERBATIM-END PM1:✱80·7 -/
/- PM-VERBATIM-BEGIN PM1:✱80·71
✱80·71. ⊢ : ᗡʻP∩ᗡʻQ=Λ.M−Q∈P_Δʻκ.M−P∈Q_Δʻλ .⊃. M∈(P⊍Q)_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·71 -/
/- PM-VERBATIM-BEGIN PM1:✱80·72
✱80·72. ⊢ : ᗡʻP∩ᗡʻQ=Λ.κ⊂ᗡʻP.λ⊂ᗡʻQ .⊃: M∈(P⊍Q)_Δʻ(κ∪λ) .≡. M−Q∈P_Δʻκ.M−P∈Q_Δʻλ
PM-VERBATIM-END PM1:✱80·72 -/
/- PM-VERBATIM-BEGIN PM1:✱80·73
✱80·73. ⊢ : Q=P↾κ.R=P↾λ .⊃. P_Δʻ(κ∪λ)=(Q⊍R)_Δʻ(κ∪λ)
PM-VERBATIM-END PM1:✱80·73 -/
/- PM-VERBATIM-BEGIN PM1:✱80·731
✱80·731. ⊢ : Q=P↾κ.R=P↾λ.κ∪λ⊂ᗡʻP .⊃. κ=ᗡʻQ.λ=ᗡʻR
PM-VERBATIM-END PM1:✱80·731 -/
/- PM-VERBATIM-BEGIN PM1:✱80·732
✱80·732. ⊢ : Q=P↾κ.R=P↾λ.κ∩λ=Λ .⊃. ᗡʻQ∩ᗡʻR=Λ
PM-VERBATIM-END PM1:✱80·732 -/
/- PM-VERBATIM-BEGIN PM1:✱80·74
✱80·74. ⊢ : κ∩λ=Λ.M∈P_Δʻ(κ∪λ) .⊃. M−P↾λ∈P_Δʻκ.M−P↾κ∈P_Δʻλ
PM-VERBATIM-END PM1:✱80·74 -/
/- PM-VERBATIM-BEGIN PM1:✱80·75
✱80·75. ⊢ : κ∩λ=Λ.M∈P_Δʻ(κ∪λ) .⊃. M−P↾λ∈P_Δʻκ.M−P↾κ∈P_Δʻλ
PM-VERBATIM-END PM1:✱80·75 -/
/- PM-VERBATIM-BEGIN PM1:✱80·76
✱80·76. ⊢ : M∈P_Δʻμ.R∈P_Δʻκ.R⊂M .⊃. M−R∈P_Δʻ(μ−κ)
PM-VERBATIM-END PM1:✱80·76 -/
/- PM-VERBATIM-BEGIN PM1:✱80·761
✱80·761. ⊢ : κ∩λ=Λ.M∈P_Δʻ(κ∪λ).R∈P_Δʻκ.R⊂M .⊃. M−R∈P_Δʻλ
PM-VERBATIM-END PM1:✱80·761 -/
/- PM-VERBATIM-BEGIN PM1:✱80·77
✱80·77. ⊢ : M∈P_Δʻμ.M−R∈P_Δʻ(μ−κ).R⊂M.κ⊂μ .⊃. R∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·77 -/
/- PM-VERBATIM-BEGIN PM1:✱80·771
✱80·771. ⊢ : κ∩λ=Λ.M∈P_Δʻ(κ∪λ).M−R∈P_Δʻλ.R⊂M .⊃. R∈P_Δʻκ
PM-VERBATIM-END PM1:✱80·771 -/
/- PM-VERBATIM-BEGIN PM1:✱80·78
✱80·78. ⊢ : M∈P_Δʻμ.xMy .⊃. M−x↓y∈P_Δʻ(μ−ιʻy)
PM-VERBATIM-END PM1:✱80·78 -/
/- PM-VERBATIM-BEGIN PM1:✱80·8
✱80·8. ⊢ : ∃!P_Δʻκ .⊃. ᗡʻṡʻP_Δʻκ=κ
PM-VERBATIM-END PM1:✱80·8 -/
/- PM-VERBATIM-BEGIN PM1:✱80·81
✱80·81. ⊢ : ∃!P_Δʻα.P_Δʻα=P_Δʻβ .⊃. α=β
PM-VERBATIM-END PM1:✱80·81 -/
/- PM-VERBATIM-BEGIN PM1:✱80·82
✱80·82. ⊢ : α≠β .⊃. P_Δʻα∩P_Δʻβ=Λ
PM-VERBATIM-END PM1:✱80·82 -/
/- PM-VERBATIM-BEGIN PM1:✱80·83
✱80·83. ⊢. (−ιʻΛ)↿P_Δ∈1→1
PM-VERBATIM-END PM1:✱80·83 -/
/- PM-VERBATIM-BEGIN PM1:✱80·84
✱80·84. ⊢ : Λ∼∈P_Δʻʻκ .⊃. P_Δʻʻκ sm κ
PM-VERBATIM-END PM1:✱80·84 -/
/- PM-VERBATIM-BEGIN PM1:✱80·9
✱80·9. ⊢ : y≠z .⊃: M∈P_Δʻ(ιʻy∪ιʻz) .≡. (∃u,v).uPy.vPz.M=u↓y⊍v↓z
PM-VERBATIM-END PM1:✱80·9 -/
/- PM-VERBATIM-BEGIN PM1:✱80·91
✱80·91. ⊢ : M∈P_Δʻ(ιʻy∪ιʻz) .⊃. M=(Mʻy)↓y⊍(Mʻz)↓z
PM-VERBATIM-END PM1:✱80·91 -/
/- PM-VERBATIM-BEGIN PM1:✱80·92
✱80·92. ⊢ : y≠z .⊃. DʻʻP_Δʻ(ιʻy∪ιʻz)=ξ̂{(∃u,v).uPy.vPz.ξ=ιʻu∪ιʻv}
PM-VERBATIM-END PM1:✱80·92 -/
/- PM-VERBATIM-BEGIN PM1:✱80·93
✱80·93. ⊢ : ∃!P_Δʻ(ιʻy∪ιʻz) .≡. y,z∈ᗡʻP
PM-VERBATIM-END PM1:✱80·93 -/
/- PM-VERBATIM-BEGIN PM1:✱80·94
✱80·94. ⊢ : ∃!P_Δʻ(β∪ιʻz) .≡. ∃!P_Δʻβ . z∈ᗡʻP
PM-VERBATIM-END PM1:✱80·94 -/
