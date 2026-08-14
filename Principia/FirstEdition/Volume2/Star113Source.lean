/-! # ✱113 — Opening catalogue (first edition, volume II, pp. 108–109). -/

/- PM-VERBATIM-BEGIN PM2:✱113·1
✱113·1. ⊢ . β×α = sʻα↓₍₍ʸʸβ  [(✱113·02)]
PM-VERBATIM-END PM2:✱113·1 -/

/- PM-VERBATIM-BEGIN PM2:✱113·101
✱113·101. ⊢ : R∈β×α .≡. (∃x,y). x∈α . y∈β . R=x↓y  [✱40·7.✱113·1]
PM-VERBATIM-END PM2:✱113·101 -/

/- PM-VERBATIM-BEGIN PM2:✱113·102
✱113·102. ⊢ : y∈β .⊃. α↓₍₍ʸy = (α↑β)Δʻιʻy

Dem.
  ⊢ . ✱35·103 . ⊃
  ⊢ :. Hp . ⊃ : x (α ↑ β ) y . ≡ . x ∈ α :
  [✱85·51] ⊃ : (α ↑ β )Δ ʻι ʻy = ↓ yʻʻα
  [(✱38·03)] = α ↓₍₍ y : ⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱113·102 -/

/- PM-VERBATIM-BEGIN PM2:✱113·104
✱113·104. ⊢ . E! α↓₍₍ʸy  [✱38·12]
PM-VERBATIM-END PM2:✱113·104 -/

/- PM-VERBATIM-BEGIN PM2:✱113·105
✱113·105. ⊢ : ∃!α .⊃. α↓₍₍ ∈ 1→1

Dem.
  ⊢ . ✱113·104. ✱71·166 . ⊃ ⊢ . α ↓₍₍ ∈ 1 → Cls (1)
  ⊢ . ✱38·131. ⊃ ⊢ : α ↓₍₍ ʻy = α ↓₍₍ ʻz . x ∈ α . ⊃ . x ↓ y ∈ α ↓₍₍ ʻz .
  [✱38·131] ⊃ . (∃ xʻ) . xʻ ∈ α . x ↓ y = xʻ ↓ z.
  [✱55·202] ⊃ . y = z (2)
  ⊢ .(2). ✱10·11·23·35. ⊃ ⊢ : ∃ ! α .α ↓₍₍ ʻy = α ↓₍₍ ʻz . ⊃ . y = z (3)
  ⊢ .(1).(3). ✱71·54. ⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱113·105 -/

/- PM-VERBATIM-BEGIN PM2:✱113·106
✱113·106. ⊢ : x∈α . y∈β .⊃. x↓y∈β×α  [✱113·101]
PM-VERBATIM-END PM2:✱113·106 -/

/- PM-VERBATIM-BEGIN PM2:✱113·107
✱113·107. ⊢ : ∃!α . ∃!β .⊃. ∃!β×α  [✱113·106]
PM-VERBATIM-END PM2:✱113·107 -/

/- PM-VERBATIM-BEGIN PM2:✱113·11
✱113·11. ⊢ : ∃!α .⊃. α↓₍₍ʸʸβ∈Ncʻβ : (y). α↓₍₍ʸy∈Ncʻα

Dem.
  ⊢ . ✱113·105·104 . ✱73·26 . ⊃ ⊢ : ∃ ! α . ⊃ . α ↓₍₍ ʻʻβ sm β (1)
  ⊢ . ✱38·2. ✱73·611. ⊃ ⊢ . α ↓₍₍ y sm α (2)
  ⊢ . (1) . (2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱113·11 -/

/- PM-VERBATIM-BEGIN PM2:✱113·111
✱113·111. ⊢ . α↓₍₍ʸʸβ∈Cls² excl  [✱113·103.✱85·55]
PM-VERBATIM-END PM2:✱113·111 -/

/- PM-VERBATIM-BEGIN PM2:✱113·112
✱113·112. ⊢ : α=Λ . ∃!β .⊃. α↓₍₍ʸʸβ=ιʻΛ

Dem.
  ⊢ . ✱38·3 . ⊃ ⊢ : Hp . ⊃ . α ↓₍₍ ʻʻβ = μ̂ { (∃ y).y ∈ β . μ = ↓ yʻʻΛ }
  [✱37·29] = μ̂ { (∃ y).y ∈ β . μ = Λ}
  [Hp] = ι ʻΛ
PM-VERBATIM-END PM2:✱113·112 -/

/- PM-VERBATIM-BEGIN PM2:✱113·113
✱113·113. ⊢ : β=Λ .⊃. α↓₍₍ʸʸβ=Λ  [✱37·29]
PM-VERBATIM-END PM2:✱113·113 -/
/- PM-VERBATIM-BEGIN PM2:✱113·114
✱113·114. ⊢ :. α=Λ .∨. β=Λ :≡. β×α=Λ  [✱113·1·112·113·107.✱53·24]
PM-VERBATIM-END PM2:✱113·114 -/
/- PM-VERBATIM-BEGIN PM2:✱113·115
✱113·115. ⊢ . ṡʻ(β×α)=α↑β

Dem.
  ⊢ . ✱113·101.✱41·11. ⊃
  ⊢ : u { ṡ ʻ(β × α )} v. ≡ . (∃ R, x, y) . x ∈ α . y ∈ β . R = x ↓ y . uRv .
  [✱13·195.✱55·13] ≡ . (∃ x, y) . x ∈ α . y ∈ β . u = x . v = y .
  [✱13·22] ≡ . u ∈ α . v ∈ β .
  [✱35·103] ≡ . u (α ↑ β ) v : ⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱113·115 -/
/- PM-VERBATIM-BEGIN PM2:✱113·117
✱113·117. ⊢ :. α=Λ .∨. β=Λ :⊃. sʻDʸʸ(β×α)=Λ . sʻᗡʸʸ(β×α)=Λ  [✱113·115.✱41·43·44.✱35·88]
PM-VERBATIM-END PM2:✱113·117 -/
/- PM-VERBATIM-BEGIN PM2:✱113·118
✱113·118. ⊢ . sʻDʸʸ(β×α)⊂α . sʻᗡʸʸ(β×α)⊂β  [✱113·116·117]
PM-VERBATIM-END PM2:✱113·118 -/

/- PM-VERBATIM-BEGIN PM2:✱113·121
✱113·121. ⊢ . Σʻα↓₍₍ʸʸβ sm β×α  [✱112·15.✱113·111·1]
PM-VERBATIM-END PM2:✱113·121 -/
/- PM-VERBATIM-BEGIN PM2:✱113·122
✱113·122. ⊢ : R↾γ,S↾δ∈Cls→1 . γ⊂ᗡʻR . δ⊂ᗡʻS .⊃. (R∥S̆)↾(δ×γ)∈1→1  [✱74·773.✱113·118]
PM-VERBATIM-END PM2:✱113·122 -/
/- PM-VERBATIM-BEGIN PM2:✱113·123
✱113·123. ⊢ : R↾γ,S↾δ∈1→Cls . γ⊂ᗡʻR . δ⊂ᗡʻS . z∈γ . w∈δ .⊃. (R∥S̆)ʻ(z↓w)=(Rʻz)↓(Sʻw)  [✱55·61]
PM-VERBATIM-END PM2:✱113·123 -/
/- PM-VERBATIM-BEGIN PM2:✱113·124
✱113·124. ⊢ : R↾γ,S↾δ∈1→Cls . γ⊂ᗡʻR . δ⊂ᗡʻS . w∈δ .⊃. (R∥S̆)ʸʸγ↓₍₍ʸw=(Rʸʸγ)↓₍₍ʸ(Sʻw)

Dem.
  ⊢ . ✱113·123 . ✱38·131 . ⊃ ⊢ : Hp . ⊃ . (R ∥ Š )ʻʻ ↓ wʻʻγ = ↓ (Sʻw)ʻʻRʻʻγ .
  [✱38·2] ⊃ . (R ∥ Š )ʻʻγ ↓₍₍ w = (Rʻʻγ ) ↓₍₍ (Sʻw) : ⊃ ⊢ . Prop
PM-VERBATIM-END PM2:✱113·124 -/
/- PM-VERBATIM-BEGIN PM2:✱113·125
✱113·125. ⊢ : R↾γ,S↾δ∈1→Cls . γ⊂ᗡʻR . δ⊂ᗡʻS .⊃. (R∥S̆)∈ʸʸγ↓₍₍ʸʸδ=(Rʸʸγ)↓₍₍ʸʸ(Sʸʸδ)  [✱113·124]
PM-VERBATIM-END PM2:✱113·125 -/

/- PM-VERBATIM-BEGIN PM2:✱113·126
✱113·126. ⊢ : Hp ✱113·125 . ⊃ . (R ∥ Š )ʻʻ(δ × γ ) = (Sʻʻδ ) × (Rʻʻγ )
PM-VERBATIM-END PM2:✱113·126 -/

/- PM-VERBATIM-BEGIN PM2:✱113·142
✱113·142. ⊢ : ∃ ! β . ⊃ . Dʻʻ(β × α ) = ιʻʻα : ∃ ! α . ⊃ . ᗡʻʻ(β × α ) = ιʻʻβ
PM-VERBATIM-END PM2:✱113·142 -/

/- PM-VERBATIM-BEGIN PM2:✱113·143
✱113·143. ⊢ :α ≠ β .P = x↓ y. R = x↓ α ⊍ y↓ β .⊃ . P = (Rʻα )↓ (Rʻβ ).R = DʻP↑ ι ʻα ⊍ ᗡʻP↑ ι ʻβ
PM-VERBATIM-END PM2:✱113·143 -/

/- PM-VERBATIM-BEGIN PM2:✱113·144
✱113·144. ⊢ :α ≠ β .T = P̂ R̂ {(∃ x,y).x∈ α .y∈ β .P = x↓ y.R = x↓ α ⊍ y↓ β}. ⊃ .T∈ 1 → 1.DʻT = β × α .ᗡʻT = ∈Δʻ(ι ʻα ∪ ι ʻβ )
PM-VERBATIM-END PM2:✱113·144 -/

/- PM-VERBATIM-BEGIN PM2:✱113·147
✱113·147. ⊢ :Hp*133·144. β × α = μ .⊃ . T = P̂ R̂ {P∈ μ .R = DʻP↑ ι ʻsʻDʻʻμ ⊍ ᗡʻP↑ ι ʻsʻᗡʻʻμ }
PM-VERBATIM-END PM2:✱113·147 -/

/- PM-VERBATIM-BEGIN PM2:✱113·148
✱113·148. ⊢ :α ∩ β = Λ .⊃ .C↾ (α × β )∈ 1 → 1
PM-VERBATIM-END PM2:✱113·148 -/

/- PM-VERBATIM-BEGIN PM2:✱113·15
✱113·15. ⊢ .Cʻʻ(α × β ) = Cʻʻ(β × a) = ξ̂ {(∃ x,y).x∈ α .y∈ β .ξ = ι ʻx∪ ι ʻy}
PM-VERBATIM-END PM2:✱113·15 -/

/- PM-VERBATIM-BEGIN PM2:✱113·152
✱113·152. ⊢ :α ∩ β = Λ .⊃ .Cʻʻ(α × β ) sm (α × β ).Dʻʻ∈Δʻ(ι ʻα ∪ ι ʻβ ) sm (α × β )
PM-VERBATIM-END PM2:✱113·152 -/

/- PM-VERBATIM-BEGIN PM2:✱113·153
✱113·153. ⊢ :ṡ ʻλ ∩̇ ṡ ʻμ = Λ̇ .⊃ .ṡ | C↾ (λ × μ )∈ (sʻλ ⊍₍₍ʻʻμ ) sm ̅ (λ × μ ).sʻλ ⊍₍₍ʻʻμ sm λ × μ
PM-VERBATIM-END PM2:✱113·153 -/

/- PM-VERBATIM-BEGIN PM2:✱113·16
✱113·16. ⊢ : tʻα = tʻβ .⊃ .Ncʻ(α × β ) = ξ̂ {(∃ γ ,δ ).γ ∈ N¹cʻα .δ ∈ N¹cʻβ .γ ∩ δ = Λ .ξ sm Dʻʻ∈Δʻ(ι ʻγ ∪ ι ʻδ )}
PM-VERBATIM-END PM2:✱113·16 -/

/- PM-VERBATIM-BEGIN PM2:✱113·17
✱113·17. ⊢ .β × α ∈ tʻtʻ(α ↑ β)
PM-VERBATIM-END PM2:✱113·17 -/

/- PM-VERBATIM-BEGIN PM2:✱113·171
✱113·171. ⊢ :α ∩ β = Λ .⊃ .∃ !Nc(tʻα )ʻ(α × β )
PM-VERBATIM-END PM2:✱113·171 -/

/- PM-VERBATIM-BEGIN PM2:✱113·172
✱113·172. ⊢ :α ∈ tʻβ .⊃ .∃ !Nc(t²ʻα )ʻ(α × β )
PM-VERBATIM-END PM2:✱113·172 -/

/- PM-VERBATIM-BEGIN PM2:✱113·18
✱113·18. ⊢ :∃ !α .∃ !β .α × β = α' × β'.⊃ .α = α'.β = β'
PM-VERBATIM-END PM2:✱113·18 -/

/- PM-VERBATIM-BEGIN PM2:✱113·181
✱113·181. ⊢ :∃ !α .∃ !α'.α × β = α' × β'.⊃ .β = β'
PM-VERBATIM-END PM2:✱113·181 -/

/- PM-VERBATIM-BEGIN PM2:✱113·183
✱113·183. ⊢ :∃ !α .∃ !β .⊃ .Fʻʻ(α × β ) = sʻCʻʻ(α × β ) = α ∪ β
PM-VERBATIM-END PM2:✱113·183 -/

/- PM-VERBATIM-BEGIN PM2:✱113·19
✱113·19. ⊢ :∃ !(α × β )∩ (γ × δ ). ≡ .∃ !α ∩ γ .∃ !β ∩ δ
PM-VERBATIM-END PM2:✱113·19 -/

/- PM-VERBATIM-BEGIN PM2:✱113·191
✱113·191. ⊢ :. ∃ !α .⊃ :∃ !α ↓₍₍ʻʻβ ∩ α ↓₍₍ʻʻγ . ≡ .∃ !β ∩ γ
PM-VERBATIM-END PM2:✱113·191 -/

/- PM-VERBATIM-BEGIN PM2:✱113·202
✱113·202. ⊢ :. ξ ∈ μ ×c ν . ≡ :∃ !μ .∃ !ν :(∃ γ ,δ ).μ = Ncʻγ .ν = Ncʻδ .ξ sm (γ × δ )
PM-VERBATIM-END PM2:✱113·202 -/

/- PM-VERBATIM-BEGIN PM2:✱113·22
✱113·22. ⊢ :ξ ∈ Nc(η )ʻγ ×c Nc(ζ )ʻδ . ≡ .∃ !Nc(η )ʻγ .∃ !Nc(ζ )ʻδ .ξ sm (γ × δ )
PM-VERBATIM-END PM2:✱113·22 -/

/- PM-VERBATIM-BEGIN PM2:✱113·222
✱113·222. ⊢ .N₀cʻγ ×c N₀cʻδ = Ncʻ(γ × δ )
PM-VERBATIM-END PM2:✱113·222 -/

/- PM-VERBATIM-BEGIN PM2:✱113·23
✱113·23. ⊢ .μ ×c ν ∈ NC
PM-VERBATIM-END PM2:✱113·23 -/

/- PM-VERBATIM-BEGIN PM2:✱113·26
✱113·26. ⊢ :μ ,ν ∈ NC.∃ ! smη ʻʻμ .∃ ! smζ ʻʻν .⊃ .μ ×c ν = smη ʻʻμ ×c smζ ʻʻν
PM-VERBATIM-END PM2:✱113·26 -/

/- PM-VERBATIM-BEGIN PM2:✱113·261
✱113·261. ⊢ :μ ,ν ∈ NC.⊃ .μ ×c ν = μ ^(1) ×c ν ^(1) = μ _(00) ×c ν _(00) = etc.
PM-VERBATIM-END PM2:✱113·261 -/

/- PM-VERBATIM-BEGIN PM2:✱113·27
✱113·27. ⊢ .μ ×c ν = ν ×c μ
PM-VERBATIM-END PM2:✱113·27 -/

/- PM-VERBATIM-BEGIN PM2:✱113·3
✱113·3. ⊢ :. Mult ax.⊃ :κ ∈ Ncʻβ ∩ ClʻNcʻα .⊃ .Σ ʻκ ∈ Ncʻα ×c Ncʻβ
PM-VERBATIM-END PM2:✱113·3 -/

/- PM-VERBATIM-BEGIN PM2:✱113·4
✱113·4. ⊢ .(β ∪ γ ) × α = (β × α )∪ (γ × α )
PM-VERBATIM-END PM2:✱113·4 -/

/- PM-VERBATIM-BEGIN PM2:✱113·41
✱113·41. ⊢ .Ncʻ(β + γ ) ×c Ncʻα = Ncʻ{(β + γ ) × α} = Ncʻ{(β × α ) + (γ × α )} = Ncʻ(β × α ) +c Ncʻ(γ × α )
PM-VERBATIM-END PM2:✱113·41 -/

/- PM-VERBATIM-BEGIN PM2:✱113·43
✱113·43. ⊢ .(ν +c ϖ ) ×c μ = μ ×c (ν +c ϖ ) = (μ ×c ν ) +c (μ ×c ϖ )
PM-VERBATIM-END PM2:✱113·43 -/

/- PM-VERBATIM-BEGIN PM2:✱113·44
✱113·44. ⊢ .(sʻκ ) × α = sʻ(x α )ʻʻκ
PM-VERBATIM-END PM2:✱113·44 -/

/- PM-VERBATIM-BEGIN PM2:✱113·45
✱113·45. ⊢ :κ ∈ Cls² excl.⊃ . × α ʻʻκ ∈ Cls² excl
PM-VERBATIM-END PM2:✱113·45 -/

/- PM-VERBATIM-BEGIN PM2:✱113·46
✱113·46. ⊢ :κ ∈ Cls² excl.⊃ .Σ ʻ × α ʻʻκ sm (Σ ʻκ ) × α
PM-VERBATIM-END PM2:✱113·46 -/

/- PM-VERBATIM-BEGIN PM2:✱113·48
✱113·48. ⊢ .sʻα × ʻʻκ = α × (sʻκ ) = Cnvʻʻ{(sʻκ ) × α}
PM-VERBATIM-END PM2:✱113·48 -/

/- PM-VERBATIM-BEGIN PM2:✱113·49
✱113·49. ⊢ :κ ∈ Cls² excl.⊃ .Σ ʻα × ʻʻκ sm α × (Σ ʻκ )
PM-VERBATIM-END PM2:✱113·49 -/

/- PM-VERBATIM-BEGIN PM2:✱113·5
✱113·5. ⊢ .(γ × β ) × α = R̂ {(∃ x,y,z).x∈ α .y∈ β .z∈ γ .R = x↓ (y↓ z)}
PM-VERBATIM-END PM2:✱113·5 -/

/- PM-VERBATIM-BEGIN PM2:✱113·51
✱113·51. ⊢ .(α × β ) × γ sm α × (β × γ )
PM-VERBATIM-END PM2:✱113·51 -/

/- PM-VERBATIM-BEGIN PM2:✱113·53
✱113·53. ⊢ . (Ncʻα ×c Ncʻβ ) ×c Ncʻγ = Ncʻα ×c (Ncʻβ ×c Ncʻγ )
PM-VERBATIM-END PM2:✱113·53 -/

/- PM-VERBATIM-BEGIN PM2:✱113·54
✱113·54. ⊢ . (μ ×c ν ) ×c ϖ = μ ×c (ν ×c ϖ )
PM-VERBATIM-END PM2:✱113·54 -/

/- PM-VERBATIM-BEGIN PM2:✱113·6
✱113·6. ⊢ . Ncʻα ×c 0 = 0
PM-VERBATIM-END PM2:✱113·6 -/

/- PM-VERBATIM-BEGIN PM2:✱113·601
✱113·601. ⊢ :μ ∈ NC - ι ʻΛ .⊃ .μ ×c 0 = 0
PM-VERBATIM-END PM2:✱113·601 -/

/- PM-VERBATIM-BEGIN PM2:✱113·602
✱113·602. ⊢ :. μ ×c ν = 0. ≡ :μ ,ν ∈ NC -℩ ʻΛ :μ = 0.∨.ν = 0
PM-VERBATIM-END PM2:✱113·602 -/

/- PM-VERBATIM-BEGIN PM2:✱113·61
✱113·61. ⊢ .ι ʻz × α = ↓ zʻʻα
PM-VERBATIM-END PM2:✱113·61 -/

/- PM-VERBATIM-BEGIN PM2:✱113·62
✱113·62. ⊢ .Ncʻα ×c 1 = Ncʻα
PM-VERBATIM-END PM2:✱113·62 -/

/- PM-VERBATIM-BEGIN PM2:✱113·621
✱113·621. ⊢ :μ ∈ NC.⊃ .μ ×c 1 = sm ʻʻμ
PM-VERBATIM-END PM2:✱113·621 -/

/- PM-VERBATIM-BEGIN PM2:✱113·63
✱113·63. ⊢ :z∼∈ α .⊃ .↓ zʻʻα sm Dʻʻ∈Δʻ(ι ʻα ∪ ι ʻι ʻz)
PM-VERBATIM-END PM2:✱113·63 -/

/- PM-VERBATIM-BEGIN PM2:✱113·64
✱113·64. ⊢ .↓ zʻʻα × ↓ zʻʻβ sm α × β .↓ zʻʻα × ↓ zʻʻβ sm ↓ zʻʻ(α × β )
PM-VERBATIM-END PM2:✱113·64 -/

/- PM-VERBATIM-BEGIN PM2:✱113·65
✱113·65. ⊢ .↓ zʻʻα × ↓ zʻʻβ = (↓ z∥ Cnvʻ↓ z)ʻʻ(α × β )
PM-VERBATIM-END PM2:✱113·65 -/

/- PM-VERBATIM-BEGIN PM2:✱113·66
✱113·66. ⊢ .μ ×c 2 = μ +c μ
PM-VERBATIM-END PM2:✱113·66 -/

/- PM-VERBATIM-BEGIN PM2:✱113·67
✱113·67. ⊢ .Ncʻα ×c Ncʻ(β + ι ʻy) = (Ncʻα ×c Ncʻβ ) +c Ncʻα
PM-VERBATIM-END PM2:✱113·67 -/
