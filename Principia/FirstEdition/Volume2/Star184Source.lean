/-! Principia Mathematica, first edition, volume II, ✱184.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱184·01
μ ×̇ ν =R̂ {(∃ P,Q).μ =N₀rʻP.ν =N₀rʻQ.R smor (P× Q)} Df
PM-VERBATIM-END PM2:✱184·01 -/

/- PM-VERBATIM-BEGIN PM2:✱184·02
NrʻP×̇ ν =N₀rʻP×̇ ν Df
PM-VERBATIM-END PM2:✱184·02 -/

/- PM-VERBATIM-BEGIN PM2:✱184·03
μ ×̇ NrʻQ=μ ×̇ N₀rʻQ Df
PM-VERBATIM-END PM2:✱184·03 -/

/- PM-VERBATIM-BEGIN PM2:✱184·1
⊢ :R∈ μ ×̇ ν .≡ .(∃ P,Q).μ =N₀rʻP.ν =N₀rʻQ.R smor (P× Q) [(*184·01)]
PM-VERBATIM-END PM2:✱184·1 -/

/- PM-VERBATIM-BEGIN PM2:✱184·11
⊢ :∃ !μ ×̇ ν .⊃ .μ ,ν ∈ N₀R.∃ !μ .∃ !ν
PM-VERBATIM-END PM2:✱184·11 -/

/- PM-VERBATIM-BEGIN PM2:✱184·111
⊢ :∼(μ ,ν ∈ N₀R).⊃ .μ ×̇ ν =Λ
PM-VERBATIM-END PM2:✱184·111 -/

/- PM-VERBATIM-BEGIN PM2:✱184·12
⊢ :. μ ,ν ∈ NR.⊃ :R∈ μ ×̇ ν .≡ .(∃ P,Q).P∈ μ .Q∈ ν .R smor (P× Q)
PM-VERBATIM-END PM2:✱184·12 -/

/- PM-VERBATIM-BEGIN PM2:✱184·13
⊢ .NrʻP×̇ NrʻQ=N₀rʻP×̇ NrʻQ =NrʻP×̇ N₀rʻQ =N₀rʻP×̇ N₀rʻQ=Nrʻ(P× Q)
PM-VERBATIM-END PM2:✱184·13 -/

/- PM-VERBATIM-BEGIN PM2:✱184·14
⊢ :P smor R.Q smor S.⊃ .NrʻP×̇ NrʻQ=NrʻR×̇ NrʻS
PM-VERBATIM-END PM2:✱184·14 -/

/- PM-VERBATIM-BEGIN PM2:✱184·15
⊢ .μ ×̇ ν ∈ NR
PM-VERBATIM-END PM2:✱184·15 -/

/- PM-VERBATIM-BEGIN PM2:✱184·16
⊢ :. μ ×̇ ν =0r.≡ :μ ,ν ∈ NR-ι ʻΛ :μ =0r.∨.ν =0r
PM-VERBATIM-END PM2:✱184·16 -/

/- PM-VERBATIM-BEGIN PM2:✱184·2
⊢ :. Mult ax.⊃ :P∈ NrʻR.CʻP⊂ NrʻS.⊃ .Σ NrʻP =NrʻR×̇ NrʻS [*183·26.*184·13]
PM-VERBATIM-END PM2:✱184·2 -/

/- PM-VERBATIM-BEGIN PM2:✱184·21
⊢ :. Mult ax.⊃ :μ ,ν ∈ NR.ν ≠ Λ .P ∈ μ .CʻP⊂ ν .⊃ .Σ NrʻP =μ ×̇ ν
PM-VERBATIM-END PM2:✱184·21 -/

/- PM-VERBATIM-BEGIN PM2:✱184·3
⊢ .(NrʻP×̇ NrʻQ)×̇ NrʻR=NrʻP×̇ (NrʻQ×̇ NrʻR)=Nrʻ(P× Q× R)
PM-VERBATIM-END PM2:✱184·3 -/

/- PM-VERBATIM-BEGIN PM2:✱184·31
⊢ .(μ ×̇ ν )×̇ ϖ =μ ×̇ (ν ×̇ ϖ )
PM-VERBATIM-END PM2:✱184·31 -/

/- PM-VERBATIM-BEGIN PM2:✱184·32
μ ×̇ ν ×̇ ϖ =(μ ×̇ ν )×̇ ϖ Df
PM-VERBATIM-END PM2:✱184·32 -/

/- PM-VERBATIM-BEGIN PM2:✱184·33
⊢ :P∈ Rel²excl.⊃ .Σ NrʻP×̇ NrʻR=Σ Nrʻ(× R)^;P
PM-VERBATIM-END PM2:✱184·33 -/

/- PM-VERBATIM-BEGIN PM2:✱184·34
⊢ .(NrʻP+̇ NrʻQ)×̇ NrʻR=(NrʻP×̇ NrʻR)+̇ (NrʻQ×̇ NrʻR)
PM-VERBATIM-END PM2:✱184·34 -/

/- PM-VERBATIM-BEGIN PM2:✱184·35
⊢ .(ν +̇ ϖ )×̇ μ =(ν ×̇ μ )+̇ (ϖ ×̇ μ ) [*184·34]
PM-VERBATIM-END PM2:✱184·35 -/

/- PM-VERBATIM-BEGIN PM2:✱184·4
⊢ .2r×̇ μ =μ +̇ μ
PM-VERBATIM-END PM2:✱184·4 -/

/- PM-VERBATIM-BEGIN PM2:✱184·41
⊢ :ν ≠ 0r.⊃ .(ν +̇ 1̇ )×̇ μ = (ν ×̇ μ) +̇ μ
PM-VERBATIM-END PM2:✱184·41 -/

/- PM-VERBATIM-BEGIN PM2:✱184·42
⊢ :ν ≠ 0r.⊃ .(1̇ +̇ ν )×̇ μ = μ +̇ (ν ×̇ μ ) [Proof as in *184·41]
PM-VERBATIM-END PM2:✱184·42 -/

/- PM-VERBATIM-BEGIN PM2:✱184·5
⊢ :μ ,ν ∈ NR.⊃ .Cʻʻ(μ ×̇ ν ) = Cʻʻμ × cCʻʻν
PM-VERBATIM-END PM2:✱184·5 -/
