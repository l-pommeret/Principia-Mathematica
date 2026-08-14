/-! Principia Mathematica, first edition, volume II, ✱180.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱180·01
P + Q = {↓ (Λ ∩ CʻQ)^;℩^;P} ⤉ {(Λ ∩ CʻP) ↓ ^;ι ^;Q} Df
PM-VERBATIM-END PM2:✱180·01 -/

/- PM-VERBATIM-BEGIN PM2:✱180·02
μ +̇ ν = R̂ {(∃ P,Q) . μ = N₀rʻP . ν = N₀rʻQ . R smor (P + Q)} Df
PM-VERBATIM-END PM2:✱180·02 -/

/- PM-VERBATIM-BEGIN PM2:✱180·03
NrʻP +̇ ν = N₀rʻP +̇ ν Df
PM-VERBATIM-END PM2:✱180·03 -/

/- PM-VERBATIM-BEGIN PM2:✱180·031
μ +̇ NrʻQ = μ +̇ N₀rʻQ Df
PM-VERBATIM-END PM2:✱180·031 -/

/- PM-VERBATIM-BEGIN PM2:✱180·1
⊢ . P + Q = {↓ (Λ ∩ CʻQ)^;℩^;P} ⤉ {(Λ ∩ CʻP) ↓ ^;℩^;Q} [(*180·01)]
PM-VERBATIM-END PM2:✱180·1 -/

/- PM-VERBATIM-BEGIN PM2:✱180·101
⊢ . Cʻ ↓ (Λ ∩ CʻQ)^;℩^;P = ↓ (Λ ∩ CʻQ)ʻʻ℩ʻʻCʻP. Cʻ(Λ ∩ CʻP) ↓ ^;ι ℩^;Q = (Λ ∩ CʻP) ↓ ʻʻ℩ʻʻCʻQ [*150·22]
PM-VERBATIM-END PM2:✱180·101 -/

/- PM-VERBATIM-BEGIN PM2:✱180·11
⊢ . Cʻ ↓ (Λ ∩ CʻQ)^;℩^;P ∩ Cʻ(Λ ∩ CʻP) ↓ ^;℩^;Q = Λ [*180·101 . *110·11]
PM-VERBATIM-END PM2:✱180·11 -/

/- PM-VERBATIM-BEGIN PM2:✱180·111
⊢ . Cʻ(P + Q) = CʻP + CʻQ
PM-VERBATIM-END PM2:✱180·111 -/

/- PM-VERBATIM-BEGIN PM2:✱180·12
⊢ . ↓ (Λ ∩ CʻP)^;℩^;P smor P . (Λ ∩ CʻP) ↓ ^;℩^;Q smor Q [*151·61·64·65]
PM-VERBATIM-END PM2:✱180·12 -/

/- PM-VERBATIM-BEGIN PM2:✱180·13
⊢ : R smor P . S smor Q . CʻR ∩ CʻS = Λ . ⊃ . R ⤉ S smor P + Q
PM-VERBATIM-END PM2:✱180·13 -/

/- PM-VERBATIM-BEGIN PM2:✱180·14
⊢ : CʻP ∩ CʻQ = Λ . ⊃ . P ⤉ Q smor P + Q [*180·13 . *151·13]
PM-VERBATIM-END PM2:✱180·14 -/

/- PM-VERBATIM-BEGIN PM2:✱180·15
⊢ : R smor P . S smor Q . ⊃ . R + S smor P + Q
PM-VERBATIM-END PM2:✱180·15 -/

/- PM-VERBATIM-BEGIN PM2:✱180·151
⊢ :. CʻP∩ C⊃ Q=Λ .⊃ :Z smor (P⤉Q).≡ . (∃ R,S).R smor P.S smor Q.CʻR∩ CʻS=Λ .Z=R⤉S
PM-VERBATIM-END PM2:✱180·151 -/

/- PM-VERBATIM-BEGIN PM2:✱180·152
⊢ :Z smor (P+Q).≡ . (∃ R,S).R smor P.S smor Q.CʻR∩ CʻS=Λ .Z=R⤉S [*180·151·11·12]
PM-VERBATIM-END PM2:✱180·152 -/

/- PM-VERBATIM-BEGIN PM2:✱180·16
⊢ .Nrʻ (P+Q)= Ẑ {(∃ R,S).R∈ NrʻP.S∈ NrʻQ.CʻR∩ CʻS=Λ .Z=R⤉S} [*180·152.*152·11]
PM-VERBATIM-END PM2:✱180·16 -/

/- PM-VERBATIM-BEGIN PM2:✱180·2
⊢ :Z∈ μ +̇ ν .≡ .(∃ P,Q).μ =N₀rʻP.ν =N₀rʻQ.Z smor (P+Q) [(*180·02)]
PM-VERBATIM-END PM2:✱180·2 -/

/- PM-VERBATIM-BEGIN PM2:✱180·201
⊢ :. Z∈ μ +̇ ν .≡ :μ ,ν ∈ N₀R:(∃ P,Q).P∈ μ .Q∈ ν .Z smor (P+Q) [*155·27.*180·2]
PM-VERBATIM-END PM2:✱180·201 -/

/- PM-VERBATIM-BEGIN PM2:✱180·202
⊢ :. Z∈ μ +̇ ν .≡ : ∃ !μ .∃ !ν :(∃ P,Q).μ =NrʻP.ν =NrʻQ.Z smor (P+Q)
PM-VERBATIM-END PM2:✱180·202 -/

/- PM-VERBATIM-BEGIN PM2:✱180·21
⊢ :. μ ,ν ∈ NR.⊃ :Z∈ μ +̇ ν .≡ .(∃ P,Q).P∈ μ .Q∈ ν .Z smor (P+̇Q)
PM-VERBATIM-END PM2:✱180·21 -/

/- PM-VERBATIM-BEGIN PM2:✱180·211
⊢ :. μ , ν ∈ NR . ⊃ : Z ∈ μ +̇ ν . ≡ . (∃ R, S) . R ∈ smor ʻʻμ . S ∈ smor ʻʻν . CʻR ∩ CʻS = Λ . Z = R ⤉ S
PM-VERBATIM-END PM2:✱180·211 -/

/- PM-VERBATIM-BEGIN PM2:✱180·212
⊢ :. μ , ν ∈ NR . ⊃ : Z ∈ μ +̇ ν . ≡ . (∃ R) . R ∈ smor ʻʻμ . R ⪽ Z . Z ⥏ (- CʻR) ∈ smor ʻʻν
PM-VERBATIM-END PM2:✱180·212 -/

/- PM-VERBATIM-BEGIN PM2:✱180·22
⊢ . N₀rʻP +̇ N₀rʻQ = Nrʻ(P +̇ Q)
PM-VERBATIM-END PM2:✱180·22 -/

/- PM-VERBATIM-BEGIN PM2:✱180·24
⊢ : R smor P . S smor Q . ⊃ . N₀rʻR +̇ N₀rʻS = N₀rʻP +̇ N₀rʻQ [*180·15·22]
PM-VERBATIM-END PM2:✱180·24 -/

/- PM-VERBATIM-BEGIN PM2:✱180·3
⊢ . NrʻP +̇ NrʻQ = N₀rʻP +̇ NrʻQ = NrʻP +̇ N₀rʻQ = N₀rʻP +̇ N₀rʻQ = Nrʻ(P +̇ Q) [*180·22 . (*180·03·031)]
PM-VERBATIM-END PM2:✱180·3 -/

/- PM-VERBATIM-BEGIN PM2:✱180·31
⊢ : P smor R . Q smor S . ⊃ . NrʻP +̇ NrʻQ = NrʻR +̇ NrʻS
PM-VERBATIM-END PM2:✱180·31 -/

/- PM-VERBATIM-BEGIN PM2:✱180·32
⊢ : CʻP ∩ CʻQ = Λ . ⊃ . NrʻP +̇ NrʻQ = Nrʻ(P ⤉ Q) [*180·14·3]
PM-VERBATIM-END PM2:✱180·32 -/

/- PM-VERBATIM-BEGIN PM2:✱180·4
⊢ : ∃ ! μ +̇ ν . ⊃ . μ , ν ∈ NR - ℩ʻΛ . μ , ν ∈ N₀R
PM-VERBATIM-END PM2:✱180·4 -/

/- PM-VERBATIM-BEGIN PM2:✱180·42
⊢ . μ +̇ ν ∈ NR
PM-VERBATIM-END PM2:✱180·42 -/

/- PM-VERBATIM-BEGIN PM2:✱180·43
⊢ : μ +̇ ν = N₀rʻZ . ≡ . Z ∈ μ +̇ ν
PM-VERBATIM-END PM2:✱180·43 -/

/- PM-VERBATIM-BEGIN PM2:✱180·53
⊢ . (P + Q) + R smor P + (Q + R)
PM-VERBATIM-END PM2:✱180·53 -/

/- PM-VERBATIM-BEGIN PM2:✱180·531
P + Q + R = (P + Q) + R Df
PM-VERBATIM-END PM2:✱180·531 -/

/- PM-VERBATIM-BEGIN PM2:✱180·54
⊢ . (NrʻP +̇ NrʻQ) +̇ NrʻR = Nrʻ(P + Q + R)
PM-VERBATIM-END PM2:✱180·54 -/

/- PM-VERBATIM-BEGIN PM2:✱180·541
⊢ . NrʻP +̇ (NrʻQ +̇ NrʻR) = Nrʻ(P + Q + R)
PM-VERBATIM-END PM2:✱180·541 -/

/- PM-VERBATIM-BEGIN PM2:✱180·55
⊢ . (NrʻP +̇ NrʻQ) +̇ NrʻR = NrʻP +̇ (NrʻQ +̇ NrʻR)
PM-VERBATIM-END PM2:✱180·55 -/

/- PM-VERBATIM-BEGIN PM2:✱180·551
⊢ .(N₀rʻP+̇ N₀rʻQ)+̇ N₀rʻR = N₀rʻP+̇ (N₀rʻQ+̇ N₀rʻR)
PM-VERBATIM-END PM2:✱180·551 -/

/- PM-VERBATIM-BEGIN PM2:✱180·56
⊢ .(μ +̇ ν )+̇ ω = μ +̇ (ν +̇ ω )
PM-VERBATIM-END PM2:✱180·56 -/

/- PM-VERBATIM-BEGIN PM2:✱180·561
μ +̇ ν +̇ ω = (μ +̇ ν ])+̇ ω Df
PM-VERBATIM-END PM2:✱180·561 -/

/- PM-VERBATIM-BEGIN PM2:✱180·57
⊢ .(μ +̇ ν )+̇ (ω +̇ ρ ) = μ +̇ ν +̇ ω +̇ ρ
PM-VERBATIM-END PM2:✱180·57 -/

/- PM-VERBATIM-BEGIN PM2:✱180·6
⊢ :μ ∈ NR.⊃ .μ +̇ 0r = smor ʻʻμ = 0r+̇ μ
PM-VERBATIM-END PM2:✱180·6 -/

/- PM-VERBATIM-BEGIN PM2:✱180·61
⊢ .NrʻP+̇ 0r = NrʻP = 0r+̇ NrʻP
PM-VERBATIM-END PM2:✱180·61 -/

/- PM-VERBATIM-BEGIN PM2:✱180·62
⊢ :μ +̇ ν = 0r. ≡ .μ = 0r.ν = 0r
PM-VERBATIM-END PM2:✱180·62 -/

/- PM-VERBATIM-BEGIN PM2:✱180·64
⊢ .0r+̇ 0r = 0r
PM-VERBATIM-END PM2:✱180·64 -/

/- PM-VERBATIM-BEGIN PM2:✱180·642
⊢ .2r+̇ 0r = 0r+̇ 2r = 2r
PM-VERBATIM-END PM2:✱180·642 -/

/- PM-VERBATIM-BEGIN PM2:✱180·7
⊢ .CʻʻNrʻ(P+Q) = CʻʻNrʻP+cCʻʻNrʻQ = NcʻCʻP+cNcʻCʻQ
PM-VERBATIM-END PM2:✱180·7 -/

/- PM-VERBATIM-BEGIN PM2:✱180·71
⊢ :μ ,ν ∈ NR.⊃ .Cʻʻ(μ +̇ ν ) = Cʻʻμ +cCʻʻν
PM-VERBATIM-END PM2:✱180·71 -/
