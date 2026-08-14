/-! Principia Mathematica, first edition, volume II, ✱170.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱170·01
Pcl=α̂ β̂ {α ,β ∈ ClʻCʻP.∃ !α -β -P̌ ʻʻ(β -α )} Df
PM-VERBATIM-END PM2:✱170·01 -/

/- PM-VERBATIM-BEGIN PM2:✱170·02
Pₗc = Cnvʻ(P̌ )cl Df
PM-VERBATIM-END PM2:✱170·02 -/

/- PM-VERBATIM-BEGIN PM2:✱170·1
⊢ :α Pclβ .≡ .a,β ∈ ClʻCʻP.∃ !α -β -P̌ ʻʻ(β -α ) [(*170·01)]
PM-VERBATIM-END PM2:✱170·1 -/

/- PM-VERBATIM-BEGIN PM2:✱170·101
⊢ .Pₗc=Cnvʻ(P̌ )cl [(*170·02)]
PM-VERBATIM-END PM2:✱170·101 -/

/- PM-VERBATIM-BEGIN PM2:✱170·102
⊢ :α Pₗcβ .≡ .a,β ∈ ClʻCʻP.∃ !β -α -Pʻʻ(α -β ) [*170·1·101]
PM-VERBATIM-END PM2:✱170·102 -/

/- PM-VERBATIM-BEGIN PM2:✱170·103
⊢ :y∼∈ P̌ ʻʻ(β-α ).≡ .P⃗ʻy∩ β ⊂ α
PM-VERBATIM-END PM2:✱170·103 -/

/- PM-VERBATIM-BEGIN PM2:✱170·11
⊢ :. α Pclβ .≡ :α ,β ∈ ClʻCʻP:(∃ y).y∈ α -β .P⃗ʻy∩ β ⊂ α [*170·1·103]
PM-VERBATIM-END PM2:✱170·11 -/

/- PM-VERBATIM-BEGIN PM2:✱170·12
⊢ :α Pclβ .≡ .α ,β ∈ ClʻCʻP.∃ !α -(α ∩ β )-P̌ ʻʻ{β -(α ∩ β )} [*170·1.*22·93]
PM-VERBATIM-END PM2:✱170·12 -/

/- PM-VERBATIM-BEGIN PM2:✱170·121
⊢ :. α Pclβ .≡ .α ,β ∈ ClʻCʻP.∃ !(α ∪ β )-β -P̌ ʻʻ{(α ∪ β )-α} [*170·1.*22·9]
PM-VERBATIM-END PM2:✱170·121 -/

/- PM-VERBATIM-BEGIN PM2:✱170·13
⊢ :. α Pclβ .≡ :(∃ ρ ,σ ,γ ).ρ ,σ ,γ ∈ ClʻCʻP. ρ ∩ γ =Λ .σ ∩ γ =Λ .ρ ∩ σ =Λ .α =γ ∪ ρ .β =γ ∪ σ .∃ !ρ -P̌ ʻʻσ
PM-VERBATIM-END PM2:✱170·13 -/

/- PM-VERBATIM-BEGIN PM2:✱170·14
⊢ :. α ,β ∈ ClʻCʻP.⊃ :α -̇ Pclβ .≡ .α -β ⊂ P̌ ʻʻ(β -α ) [*170·1.*24·55]
PM-VERBATIM-END PM2:✱170·14 -/

/- PM-VERBATIM-BEGIN PM2:✱170·141
⊢ :. α ,β ∈ ClʻCʻP.⊃ :α -̇ Pₗcβ .≡ .β -α ⊂ Pʻʻ(α - β ) [*170·14·101]
PM-VERBATIM-END PM2:✱170·141 -/

/- PM-VERBATIM-BEGIN PM2:✱170·15
⊢ :α Pclβ .⊃ .β ∩ pʻP⃗ʻʻ(α -β )⊂ α
PM-VERBATIM-END PM2:✱170·15 -/

/- PM-VERBATIM-BEGIN PM2:✱170·16
⊢ :α ⊂ CʻP.β ⊂ α .β ≠ α .⊃ .α Pclβ
PM-VERBATIM-END PM2:✱170·16 -/

/- PM-VERBATIM-BEGIN PM2:✱170·161
⊢ :α ⊂ CʻP.β ⊂ α .β ≠ α .⊃ .β Pₗcα
PM-VERBATIM-END PM2:✱170·161 -/

/- PM-VERBATIM-BEGIN PM2:✱170·17
⊢ .Pcl ⪽ J.Pₗc ⪽ J
PM-VERBATIM-END PM2:✱170·17 -/

/- PM-VERBATIM-BEGIN PM2:✱170·2
⊢ :. α ,β ∈ ClʻCʻP:(∃ y). y∈ α -β . P⃗ʻy∩ α = P⃗ʻy∩ β :⊃ .α Pclβ [*170·11 .*22·43]
PM-VERBATIM-END PM2:✱170·2 -/

/- PM-VERBATIM-BEGIN PM2:✱170·21
⊢ :. α ⊂ CʻP.⊃ : y min_P(α -β ).≡ . y∈ α -β . P⃗ʻy∩ α ⊂ β
PM-VERBATIM-END PM2:✱170·21 -/

/- PM-VERBATIM-BEGIN PM2:✱170·22
⊢ :. α ⊂ CʻP. y min_P (α -β ).⊃ : P⃗ʻy∩ β ⊂ α .≡ . P⃗ʻy∩ α = P⃗ʻy∩ β
PM-VERBATIM-END PM2:✱170·22 -/

/- PM-VERBATIM-BEGIN PM2:✱170·23
⊢ :. α ⊂ CʻP. y∈ α -β -P̌ ʻʻ (β -α ).⊃ : y min_P (α-β ) .≡ . P⃗ʻy∩ α =P⃗ʻy∩ β
PM-VERBATIM-END PM2:✱170·23 -/

/- PM-VERBATIM-BEGIN PM2:✱170·3
⊢ :α ∈ ClʻCʻP.β ⊂ α .∃ !α -β .⊃ .α Pclβ [*170·16]
PM-VERBATIM-END PM2:✱170·3 -/

/- PM-VERBATIM-BEGIN PM2:✱170·31
⊢ :β ⊂ CʻP.β ≠ CʻP .≡ . (CʻP) Pclβ [*170·16]
PM-VERBATIM-END PM2:✱170·31 -/

/- PM-VERBATIM-BEGIN PM2:✱170·32
⊢ :α ⊂ CʻP.∃ ! α .≡ . α PclΛ [*170·3]
PM-VERBATIM-END PM2:✱170·32 -/

/- PM-VERBATIM-BEGIN PM2:✱170·33
⊢ :∃̇ !P .≡ . (CʻP)PclΛ
PM-VERBATIM-END PM2:✱170·33 -/

/- PM-VERBATIM-BEGIN PM2:✱170·34
⊢ :∃̇ !P .≡ . ∃̇ !Pcl
PM-VERBATIM-END PM2:✱170·34 -/

/- PM-VERBATIM-BEGIN PM2:✱170·35
⊢ .Λ̇ cl=Λ̇ [*170·34. Transp]
PM-VERBATIM-END PM2:✱170·35 -/

/- PM-VERBATIM-BEGIN PM2:✱170·36
⊢ .DʻPcl=Cl exʻCʻP.ᗡʻPcl=ClʻCʻP-ι ʻCʻP
PM-VERBATIM-END PM2:✱170·36 -/

/- PM-VERBATIM-BEGIN PM2:✱170·37
⊢ :∃̇ !P.⊃ .CʻPcl=ClʻCʻP [*170·36]
PM-VERBATIM-END PM2:✱170·37 -/

/- PM-VERBATIM-BEGIN PM2:✱170·371
⊢ .CʻPcl⊂ ClʻCʻP [*170·37·35.*33·241]
PM-VERBATIM-END PM2:✱170·371 -/

/- PM-VERBATIM-BEGIN PM2:✱170·38
⊢ :∃̇ !P.⊃ .BʻPcl=CʻP.BʻCnvʻPcl=Λ [*170·36]
PM-VERBATIM-END PM2:✱170·38 -/

/- PM-VERBATIM-BEGIN PM2:✱170·4
⊢ :S∈ 1 arrow 1.CʻQ=ᗡʻS.⊃ .(S^;Q)cl=S_∈ ^;Qcl
PM-VERBATIM-END PM2:✱170·4 -/

/- PM-VERBATIM-BEGIN PM2:✱170·41
⊢ .(S↾ CʻQ)_∈ ^;Qcl=S_∈ ^;Qcl [*150·95.*170·371]
PM-VERBATIM-END PM2:✱170·41 -/

/- PM-VERBATIM-BEGIN PM2:✱170·42
⊢ :S↾ CʻQ∈ 1 arrow 1.CʻQ⊂ ᗡʻS.⊃ .(S^;Q)cl=S_∈ ^;Qcl
PM-VERBATIM-END PM2:✱170·42 -/

/- PM-VERBATIM-BEGIN PM2:✱170·43
⊢ :S↾ CʻQ∈ P smor̅ Q.⊃ .S_∈ ↾ CʻQcl∈ Pcl smor̅ Qcl
PM-VERBATIM-END PM2:✱170·43 -/

/- PM-VERBATIM-BEGIN PM2:✱170·44
⊢ : P smor Q.⊃ .Pcl smor Qcl [*170·43.*151·23·12]
PM-VERBATIM-END PM2:✱170·44 -/

/- PM-VERBATIM-BEGIN PM2:✱170·5
⊢ .(x↓ x)cl=(ι ʻx)↓ Λ
PM-VERBATIM-END PM2:✱170·5 -/

/- PM-VERBATIM-BEGIN PM2:✱170·51
⊢ :x≠ y.⊃ .(x↓ y)cl=(ι ʻx∪ ι ʻy) ↓ ι ʻx⊍ (ι ʻx∪ ι ʻy)↓ ι ʻy⊍ (ι ʻx∪ ι ʻy)↓ Λ ⊍ ι ʻx↓ ι ʻy⊍ ι ʻx↓ Λ ⊍ ι ʻy↓ Λ
PM-VERBATIM-END PM2:✱170·51 -/

/- PM-VERBATIM-BEGIN PM2:✱170·52
⊢ :x≠ y.⊃ .(x↓ y)cl=(ι ʻx∪ ι ʻy)↓ ι ʻx⤉ι ʻy↓ Λ
PM-VERBATIM-END PM2:✱170·52 -/

/- PM-VERBATIM-BEGIN PM2:✱170·6
⊢ :Λ Pₗcβ .≡ .β ⊂ CʻP.∃ !β [*170·32·101]
PM-VERBATIM-END PM2:✱170·6 -/

/- PM-VERBATIM-BEGIN PM2:✱170·601
⊢ :α Pₗc(CʻP).≡ .α ⊂ CʻP.α ≠ CʻP [*170·31·101]
PM-VERBATIM-END PM2:✱170·601 -/

/- PM-VERBATIM-BEGIN PM2:✱170·61
⊢ :. x∼ ∈ CʻP.∃̇ !P.x∈ α ∩ β .⊃ : α (x⇷P)clβ .≡ .α {(ι ʻx∪ )^;Pcl}β .≡ .(α -ι ʻx)Pcl(β -ι ʻx)
PM-VERBATIM-END PM2:✱170·61 -/

/- PM-VERBATIM-BEGIN PM2:✱170·62
⊢ :. x∼∈ CʻP.∃̇ !P.x∈ α -β .⊃ : α (x⇷P)clβ .≡ .α ⊂ ι ʻx∪ CʻP.β ⊂ CʻP
PM-VERBATIM-END PM2:✱170·62 -/

/- PM-VERBATIM-BEGIN PM2:✱170·63
⊢ :. x∼∈ (α ∪ β ).⊃ :α (x⇷P)clβ .≡ .α Pclβ
PM-VERBATIM-END PM2:✱170·63 -/

/- PM-VERBATIM-BEGIN PM2:✱170·64
⊢ :x∼∈ CʻP.⊃ .(x⇷P)cl=(ι ʻx∪ )^;Pcl⤉Pcl
PM-VERBATIM-END PM2:✱170·64 -/

/- PM-VERBATIM-BEGIN PM2:✱170·65
⊢ :. ρ (P⤉Q)clσ .≡ :(∃ α ,β ,γ ,δ ):α ,β ∈ ClʻCʻP.γ ,δ ∈ ClʻCʻQ. ρ =α ∪ γ .σ =β ∪ δ :(∃ y).y∈ (α ∪ γ )-(β ∪ δ ).P⤉Q⃗ ʻy∩ (β ∪ δ )⊂ α ∪ γ
PM-VERBATIM-END PM2:✱170·65 -/

/- PM-VERBATIM-BEGIN PM2:✱170·651
⊢ :. CʻP∩ CʻQ=Λ .α ,β ∈ ClʻCʻP.γ ,δ ∈ ClʻCʻQ.y∈ α .⊃ : y∈ (α ∪ γ )-(β ∪ δ ).P⤉Q⃗ ʻy∩ (β ∪ δ )⊂ α ∪ γ .≡ .y∈ α -β .P⃗ʻy∩ β ⊂ α
PM-VERBATIM-END PM2:✱170·651 -/

/- PM-VERBATIM-BEGIN PM2:✱170·652
⊢ :. CʻP∩ CʻQ=Λ .α ,β ∈ ClʻCʻP.γ ,δ ∈ ClʻCʻQ.y∈ γ .⊃ : y∈ (α ∪ γ )-(β ∪ δ ).P⤉Q⃗ ʻy∩ (β ∪ δ )⊂ α ∪ γ .≡ . β ⊂ α .y∈ γ -δ .Q⃗ʻy∩ δ ⊂ γ
PM-VERBATIM-END PM2:✱170·652 -/

/- PM-VERBATIM-BEGIN PM2:✱170·653
⊢ :: CʻP∩ CʻQ =Λ .α ,β ∈ ClʻCʻP.γ ,δ ∈ ClʻCʻQ.⊃ :. (α ∪ γ )(P⤉Q)cl(β ∪ δ ).≡ :α Pclβ .∨.α =β .γ Qclδ
PM-VERBATIM-END PM2:✱170·653 -/

/- PM-VERBATIM-BEGIN PM2:✱170·66
⊢ :. ∃̇ !P.∃̇ !Q.CʻP∩ CʻQ=Λ .⊃ : ρ (P⤉Q)σ .≡ .(∃ α ,β ,γ ,δ ).(γ ↓ α )(Pcl× Qcl)(δ ↓ β ).ρ =α ∪ γ .σ =β ∪ δ
PM-VERBATIM-END PM2:✱170·66 -/

/- PM-VERBATIM-BEGIN PM2:✱170·67
⊢ :∃̇ !P.∃̇ !Q.CʻP∩ CʻQ=Λ .⊃ .(P⤉Q)cl=s^;C^;(Pcl× Qcl)
PM-VERBATIM-END PM2:✱170·67 -/

/- PM-VERBATIM-BEGIN PM2:✱170·68
⊢ :∃̇ !P.∃̇ !Q.CʻP ∩ CʻQ=Λ .⊃ . (s| C)↾ Cʻ(Pcl× Qcl)∈ (P⤉Q)cl smor̅ (Pcl× Qcl)
PM-VERBATIM-END PM2:✱170·68 -/

/- PM-VERBATIM-BEGIN PM2:✱170·69
⊢ :∃̇ !P.∃̇ !Q.CʻP∩ CʻQ=Λ .⊃ .(P⤉Q)cl smor (Pcl× Qcl) [*170·68]
PM-VERBATIM-END PM2:✱170·69 -/
