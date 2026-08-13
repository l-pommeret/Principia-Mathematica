/-! # PM II ✱124 — reflexive classes (PG78255, opening) -/
/- PM-VERBATIM-BEGIN PM2:✱124·01
✱124·01. Cls refl = Dʻ{(1→1)∩R̂(ᗡʻR⊂DʻR)∩R̂(∃!→BʻR)} Df
PM-VERBATIM-END PM2:✱124·01 -/
/- PM-VERBATIM-BEGIN PM2:✱124·02
✱124·02. NC refl=N₀cʻʻCls refl Df
PM-VERBATIM-END PM2:✱124·02 -/
/- PM-VERBATIM-BEGIN PM2:✱124·021
✱124·021. Ncʻρ∈NC refl .=. N₀cʻρ∈NC refl Df
PM-VERBATIM-END PM2:✱124·021 -/
/- PM-VERBATIM-BEGIN PM2:✱124·03
✱124·03. NC mult=NC∩α̂{κ∈α∩Cls ex² excl .⊃κ. ∃!∈Δʻκ} Df
PM-VERBATIM-END PM2:✱124·03 -/
/- PM-VERBATIM-BEGIN PM2:✱124·1
✱124·1. ⊢ : ρ∈Cls refl .≡. (∃R).R∈1→1.ᗡʻR⊂DʻR.∃!→BʻR.ρ=DʻR
PM-VERBATIM-END PM2:✱124·1 -/
/- PM-VERBATIM-BEGIN PM2:✱124·11
✱124·11. ⊢ : R∈1→1.ᗡʻR⊂DʻR.∃!→BʻR .⊃. DʻR∈Cls refl
PM-VERBATIM-END PM2:✱124·11 -/
/- PM-VERBATIM-BEGIN PM2:✱124·12
✱124·12. ⊢ . ℵ₀⊂Cls refl
PM-VERBATIM-END PM2:✱124·12 -/
/- PM-VERBATIM-BEGIN PM2:✱124·13
✱124·13. ⊢ : ρ∈Cls refl .⊃. ∃!ℵ₀∩Clʻρ
PM-VERBATIM-END PM2:✱124·13 -/
/- PM-VERBATIM-BEGIN PM2:✱124·14
✱124·14. ⊢ : ρ∈Cls refl .⊃. ρ∪σ∈Cls refl
PM-VERBATIM-END PM2:✱124·14 -/
/- PM-VERBATIM-BEGIN PM2:✱124·141
✱124·141. ⊢ : ∃!Clʻρ∩Cls refl .⊃. ρ∈Cls refl
PM-VERBATIM-END PM2:✱124·141 -/
/- PM-VERBATIM-BEGIN PM2:✱124·15
✱124·15. ⊢ : ρ∈Cls refl .≡. ∃!ℵ₀∩Clʻρ
PM-VERBATIM-END PM2:✱124·15 -/
/- PM-VERBATIM-BEGIN PM2:✱124·151
✱124·151. ⊢ : ρ∈Cls refl .≡. Ncʻρ≥ℵ₀
PM-VERBATIM-END PM2:✱124·151 -/
/- PM-VERBATIM-BEGIN PM2:✱124·16
✱124·16. ⊢ : ρ∈Cls refl .≡. (∃σ).σ⊂ρ.∃!ρ−σ.ρ sm σ .≡. ∃!Ncʻρ∩Clʻρ−ιʻρ
PM-VERBATIM-END PM2:✱124·16 -/
/- PM-VERBATIM-BEGIN PM2:✱124·17
✱124·17. ⊢ : ρ∈Cls refl .≡. (∃x).x∈ρ.ρ−ιʻx sm ρ
PM-VERBATIM-END PM2:✱124·17 -/
/- PM-VERBATIM-BEGIN PM2:✱124·18
✱124·18. ⊢ : ρ∈Cls refl.ρ sm σ .⊃. σ∈Cls refl
PM-VERBATIM-END PM2:✱124·18 -/
/- PM-VERBATIM-BEGIN PM2:✱124·181
✱124·181. ⊢ : ρ∈Cls refl .⊃. ρ−ιʻx∈Cls refl.ρ−ιʻx sm ρ
PM-VERBATIM-END PM2:✱124·181 -/
/- PM-VERBATIM-BEGIN PM2:✱124·182
✱124·182. ⊢ : ρ∈Cls refl.σ∈Cls induct .⊃. ρ−σ∈Cls refl.ρ−σ sm ρ
PM-VERBATIM-END PM2:✱124·182 -/
/- PM-VERBATIM-BEGIN PM2:✱124·2
✱124·2. ⊢ : μ∈NC refl .≡. (∃ρ).ρ∈Cls refl.μ=N₀cʻρ
PM-VERBATIM-END PM2:✱124·2 -/
/- PM-VERBATIM-BEGIN PM2:✱124·21
✱124·21. ⊢ : μ∈NC refl .≡. (∃R).R∈1→1.ᗡʻR⊂DʻR.∃!→BʻR.μ=N₀cʻDʻR
PM-VERBATIM-END PM2:✱124·21 -/
/- PM-VERBATIM-BEGIN PM2:✱124·23
✱124·23. ⊢ : μ∈NC refl .≡. μ≥ℵ₀
PM-VERBATIM-END PM2:✱124·23 -/
/- PM-VERBATIM-BEGIN PM2:✱124·231
✱124·231. ⊢ : ∃!NC refl .≡. ∃!Cls refl .≡. ∃!ℵ₀
PM-VERBATIM-END PM2:✱124·231 -/
/- PM-VERBATIM-BEGIN PM2:✱124·232
✱124·232. ⊢ : ∃!NC refl .⊃. Infin ax
PM-VERBATIM-END PM2:✱124·232 -/
/- PM-VERBATIM-BEGIN PM2:✱124·24
✱124·24. ⊢ : μ∈NC refl .≡: μ∈N₀C : (∃ν).μ=ℵ₀+꜀ν.ν∈NC
PM-VERBATIM-END PM2:✱124·24 -/
/- PM-VERBATIM-BEGIN PM2:✱124·25
✱124·25. ⊢ : μ∈NC refl .≡. μ∈N₀C.μ=μ+꜀1 .≡. ∃!μ.μ=μ+꜀1
PM-VERBATIM-END PM2:✱124·25 -/
/- PM-VERBATIM-BEGIN PM2:✱124·251
✱124·251. ⊢ : μ∈NC refl .⊃. μ=μ+꜀1
PM-VERBATIM-END PM2:✱124·251 -/
/- PM-VERBATIM-BEGIN PM2:✱124·252
✱124·252. ⊢ : μ∈NC refl.ν∈NC induct .⊃. μ=μ+꜀ν
PM-VERBATIM-END PM2:✱124·252 -/
/- PM-VERBATIM-BEGIN PM2:✱124·253
✱124·253. ⊢ : μ∈NC refl .⊃. μ=μ+꜀ℵ₀
PM-VERBATIM-END PM2:✱124·253 -/
/- PM-VERBATIM-BEGIN PM2:✱124·26
✱124·26. ⊢ : μ∈NC refl .⊃: ν∈NC induct .⊃ν. μ>ν
PM-VERBATIM-END PM2:✱124·26 -/
/- PM-VERBATIM-BEGIN PM2:✱124·27
✱124·27. ⊢ . NC refl∩NC induct=Λ
PM-VERBATIM-END PM2:✱124·27 -/
/- PM-VERBATIM-BEGIN PM2:✱124·271
✱124·271. ⊢ . Cls refl∩Cls induct=Λ
PM-VERBATIM-END PM2:✱124·271 -/
/- PM-VERBATIM-BEGIN PM2:✱124·28
✱124·28. ⊢ : ρ∈Cls refl .≡. N₀cʻρ∈NC refl .≡. Ncʻρ∈NC refl
PM-VERBATIM-END PM2:✱124·28 -/
/- PM-VERBATIM-BEGIN PM2:✱124·29
✱124·29. ⊢ . sʻNC refl=Cls refl
PM-VERBATIM-END PM2:✱124·29 -/
/- PM-VERBATIM-BEGIN PM2:✱124·3
✱124·3. ⊢ : ∃!ℵ₀ .⊃: μ<ℵ₀ .∨. μ≥ℵ₀ :≡. μ∈NC induct∪NC refl
PM-VERBATIM-END PM2:✱124·3 -/
/- PM-VERBATIM-BEGIN PM2:✱124·31
✱124·31. ⊢ : ∃!ℵ₀ .⊃. specʻℵ₀=NC induct∪NC refl
PM-VERBATIM-END PM2:✱124·31 -/
/- PM-VERBATIM-BEGIN PM2:✱124·33
✱124·33. ⊢ : ∃!ℵ₀ .⊃: μ∈NC−NC induct−NC refl .≡. μ∈NC.¬(μ<ℵ₀).¬(μ≥ℵ₀)
PM-VERBATIM-END PM2:✱124·33 -/
/- PM-VERBATIM-BEGIN PM2:✱124·34
✱124·34. ⊢ : ∃!ℵ₀ .⊃: α∉(Cls induct∪Cls refl) .≡: ¬(∃γ):γ∈ℵ₀:α⊂γ .∨. γ⊂α
PM-VERBATIM-END PM2:✱124·34 -/
/- PM-VERBATIM-BEGIN PM2:✱124·4
✱124·4. ⊢ : μ∈NC mult .≡: μ∈NC : κ∈μ∩Cls ex² excl .⊃κ. ∃!∈Δʻκ
PM-VERBATIM-END PM2:✱124·4 -/
/- PM-VERBATIM-BEGIN PM2:✱124·41
✱124·41. ⊢ . NC induct⊂NC mult
PM-VERBATIM-END PM2:✱124·41 -/
/- PM-VERBATIM-BEGIN PM2:✱124·51
✱124·51. ⊢ : ρ∉Cls induct.Q=(∩Clʻρ)|N|Cnvʻ(∩Clʻρ) .⊃. Q∈Prog.DʻQ⊂ClʻClʻρ.DʻQ=(∩Clʻρ)ʻʻNC induct
PM-VERBATIM-END PM2:✱124·51 -/
/- PM-VERBATIM-BEGIN PM2:✱124·511
✱124·511. ⊢ : ρ∉Cls induct .⊃. ClʻClʻρ∈Cls refl.(∩Clʻρ)ʻʻNC induct∈ℵ₀∩Cls² excl
PM-VERBATIM-END PM2:✱124·511 -/
/- PM-VERBATIM-BEGIN PM2:✱124·512
✱124·512. ⊢ : P∈∈Δʻ(∩Clʻρ)ʻʻNC induct .⊃. DʻP∈ℵ₀∩ClʻClʻρ.DʻP⊂Cls induct
PM-VERBATIM-END PM2:✱124·512 -/
/- PM-VERBATIM-BEGIN PM2:✱124·513
✱124·513. ⊢ : ∃!∈Δʻ(∩Clʻρ)ʻʻNC induct .⊃. Clʻρ∈Cls refl
PM-VERBATIM-END PM2:✱124·513 -/
/- PM-VERBATIM-BEGIN PM2:✱124·514
✱124·514. ⊢ : ℵ₀∈NC mult .⊃: ρ∉Cls induct .⊃. Clʻρ∈Cls refl
PM-VERBATIM-END PM2:✱124·514 -/
/- PM-VERBATIM-BEGIN PM2:✱124·52
✱124·52. ⊢ : R∈Prog.σ=β̂{(∃γ).γ∈DʻR.β=γ−sʻ→R_poʻγ.∃!β} .⊃: σ∈Cls ex² excl : γ,δ∈DʻR.γ≠δ .⊃. (...)∩(...)=Λ
PM-VERBATIM-END PM2:✱124·52 -/
/- PM-VERBATIM-BEGIN PM2:✱124·521
✱124·521. ⊢ : Hp✱124·52.π=γ̂{γ∈DʻR.∃!γ−sʻ→R_poʻγ} .⊃. σ sm π
PM-VERBATIM-END PM2:✱124·521 -/
/- PM-VERBATIM-BEGIN PM2:✱124·53
✱124·53. ⊢ : R∈Prog .⊃. sʻDʻR∉Cls induct
PM-VERBATIM-END PM2:✱124·53 -/
/- PM-VERBATIM-BEGIN PM2:✱124·531
✱124·531. ⊢ : R∈Prog.DʻR⊂Cls induct .⊃. sʻ→R_*ʻγ∈Cls induct
PM-VERBATIM-END PM2:✱124·531 -/
/- PM-VERBATIM-BEGIN PM2:✱124·532
✱124·532. ⊢ : R∈Prog.DʻR⊂Cls induct .⊃. ∃!sʻDʻR−sʻ→R_*ʻγ
PM-VERBATIM-END PM2:✱124·532 -/
/- PM-VERBATIM-BEGIN PM2:✱124·533
✱124·533. ⊢ : R∈Prog.DʻR⊂Cls induct.γ∈DʻR .⊃. (∃β).γR_poβ.∃!β−sʻ→R_poʻβ
PM-VERBATIM-END PM2:✱124·533 -/
/- PM-VERBATIM-BEGIN PM2:✱124·534
✱124·534. ⊢ : R∈Prog.DʻR⊂Cls induct.π=γ̂{γ∈DʻR.∃!γ−sʻ→R_poʻγ} .⊃. π∈ℵ₀
PM-VERBATIM-END PM2:✱124·534 -/
/- PM-VERBATIM-BEGIN PM2:✱124·535
✱124·535. ⊢ : R∈Prog.DʻR⊂Cls induct.σ=β̂{(∃γ).γ∈DʻR.β=γ−sʻ→R_poʻγ.∃!β} .⊃. σ∈ℵ₀
PM-VERBATIM-END PM2:✱124·535 -/
/- PM-VERBATIM-BEGIN PM2:✱124·536
✱124·536. ⊢ : R∈Prog.DʻR⊂Cls induct.σ=... . S∈∈Δʻσ .⊃. DʻS∈ℵ₀.DʻS⊂sʻDʻR
PM-VERBATIM-END PM2:✱124·536 -/
/- PM-VERBATIM-BEGIN PM2:✱124·54
✱124·54. ⊢ : ℵ₀∈NC mult.R∈Prog.DʻR⊂Cls induct .⊃. ∃!ℵ₀∩ClʻsʻDʻR
PM-VERBATIM-END PM2:✱124·54 -/
/- PM-VERBATIM-BEGIN PM2:✱124·541
✱124·541. ⊢ : ℵ₀∈NC mult.P∈∈Δʻ(∩Clʻρ)ʻʻNC induct .⊃. ∃!ℵ₀∩ClʻsʻDʻP.sʻDʻP⊂ρ
PM-VERBATIM-END PM2:✱124·541 -/
/- PM-VERBATIM-BEGIN PM2:✱124·55
✱124·55. ⊢ : ℵ₀∈NC mult.ρ∉Cls induct .⊃. ∃!ℵ₀∩Clʻρ
PM-VERBATIM-END PM2:✱124·55 -/
/- PM-VERBATIM-BEGIN PM2:✱124·56
✱124·56. ⊢ : ℵ₀∈NC mult .⊃. −Cls induct=Cls refl . N₀C−NC induct=NC refl
PM-VERBATIM-END PM2:✱124·56 -/
/- PM-VERBATIM-BEGIN PM2:✱124·57
✱124·57. ⊢ : μ∈N₀C−NC induct .⊃. 2^(2^μ)∈NC refl
PM-VERBATIM-END PM2:✱124·57 -/
/- PM-VERBATIM-BEGIN PM2:✱124·58
✱124·58. ⊢ : 2^μ∈NC refl .⊃μ. μ∈NC refl :⊃. N₀C−NC induct=NC refl
PM-VERBATIM-END PM2:✱124·58 -/
/- PM-VERBATIM-BEGIN PM2:✱124·6
✱124·6. ⊢ : ρ∉Cls induct .≡. ClʻClʻρ∈Cls refl
PM-VERBATIM-END PM2:✱124·6 -/
/- PM-VERBATIM-BEGIN PM2:✱124·61
✱124·61. ⊢ : ℵ₀∈NC mult .⊃: ρ∈Cls refl .≡. Clʻρ∈Cls refl .≡. ClʻClʻρ∈Cls refl
PM-VERBATIM-END PM2:✱124·61 -/
