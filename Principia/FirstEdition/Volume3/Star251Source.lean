/-
  Source-only opening of PM III ✱251.  These are archival transcriptions,
  not Lean declarations, targets, or derivations.
-/

/- PM-VERBATIM-BEGIN PM3:STAR251-SUMMARY-P18
✱251.  ORDINAL NUMBERS.

Summary of ✱251.

The name “ordinal numbers” is commonly confined to the relation-numbers of
well-ordered series, and will be so confined in what follows.  The
relation-numbers of series in general are commonly called “order-types.” Thus
α is an order-type if α ∈ NrʻʻSer, and α is an ordinal number if α ∈ NrʻʻΩ.

We put

  NO = NrʻʻΩ  Df,

where “NO” stands for “ordinal number.”
PM-VERBATIM-END PM3:STAR251-SUMMARY-P18 -/

/- PM-VERBATIM-BEGIN PM3:✱251·61
✱251·61.  ⊢ :: P, Q ∈ Rel² excl . CʻP ⊂ Ω .⊃ : ∃! (P smor Q) ∩ Rlʻsmor .≡ . P smor smor Q
PM-VERBATIM-END PM3:✱251·61 -/

/- PM-VERBATIM-BEGIN PM3:✱251·621
✱251·621.  ⊢ : CʻP ⊂ Ω . ∃! (P smor Q) ∩ Rlʻsmor .⊃ . Σ NrʻP = Σ NrʻQ . Π NrʻP = Π NrʻQ
PM-VERBATIM-END PM3:✱251·621 -/

/- PM-VERBATIM-BEGIN PM3:✱251·65
✱251·65.  ⊢ : α ∈ NO − ιʻΛ . β ∈ NR . P ∈ β . CʻP ⊂ α .⊃ . Σ NrʻP = β × α . Π NrʻP = α expᵣ β
PM-VERBATIM-END PM3:✱251·65 -/

/- PM-VERBATIM-BEGIN PM3:✱251·01
✱251·01.  NO = NrʻʻΩ  Df
PM-VERBATIM-END PM3:✱251·01 -/

/- PM-VERBATIM-BEGIN PM3:✱251·1
✱251·1.  ⊢ : α ∈ NO .≡ . (∃P) . P ∈ Ω . α = NrʻP  [(*251·01)]
PM-VERBATIM-END PM3:✱251·1 -/

/- PM-VERBATIM-BEGIN PM3:✱251·11
✱251·11.  ⊢ : P ∈ Bord . P smor Q .⊃ . Q ∈ Bord
PM-VERBATIM-END PM3:✱251·11 -/

/- PM-VERBATIM-BEGIN PM3:✱251·111
✱251·111.  ⊢ : P ∈ Ω . P smor Q .⊃ . Q ∈ Ω  [✱251·11 . ✱204·21]
PM-VERBATIM-END PM3:✱251·111 -/

/- PM-VERBATIM-BEGIN PM3:✱251·12
✱251·12.  ⊢ : P ∈ Bord .⊃ . NrʻP ⊂ Bord  [✱251·11]
PM-VERBATIM-END PM3:✱251·12 -/

/- PM-VERBATIM-BEGIN PM3:✱251·121
✱251·121.  ⊢ : P ∈ Ω .⊃ . NrʻP ⊂ Ω  [✱251·111]
PM-VERBATIM-END PM3:✱251·121 -/

/- PM-VERBATIM-BEGIN PM3:✱251·122
✱251·122.  ⊢ : α ∈ NO .⊃ . α ⊂ Ω  [✱251·121·1]
PM-VERBATIM-END PM3:✱251·122 -/

/- PM-VERBATIM-BEGIN PM3:✱251·13
✱251·13.  ⊢ : P ∈ Bord . z ∼ ε CʻP .≡ . P ↦ z ∈ Bord
PM-VERBATIM-END PM3:✱251·13 -/

/- PM-VERBATIM-BEGIN PM3:✱251·131
✱251·131.  ⊢ : P ∈ Ω . z ∼ ε CʻP .≡ . P ↦ z ∈ Ω  [✱204·51 . ✱251·13]
PM-VERBATIM-END PM3:✱251·131 -/
/- PM-VERBATIM-BEGIN PM3:✱251·132
✱251·132.  ⊢ : α ∈ NO .≡ . α + i ∈ NO
PM-VERBATIM-END PM3:✱251·132 -/
/- PM-VERBATIM-BEGIN PM3:✱251·14
✱251·14.  ⊢ : P ∈ Bord . z ∼ ε CʻP .≡ . z ↤ P ∈ Bord
PM-VERBATIM-END PM3:✱251·14 -/
/- PM-VERBATIM-BEGIN PM3:✱251·141
✱251·141.  ⊢ : P ∈ Ω . z ∼ ε CʻP .≡ . z ↤ P ∈ Ω  [✱204·51 . ✱251·14]
PM-VERBATIM-END PM3:✱251·141 -/
/- PM-VERBATIM-BEGIN PM3:✱251·142
✱251·142.  ⊢ : α ∈ NO .≡ . i + α ∈ NO  [Proof as in ✱251·132]
PM-VERBATIM-END PM3:✱251·142 -/

/- PM-VERBATIM-BEGIN PM3:✱251·15
✱251·15.  ⊢ . 0ᵣ ∈ NO  [✱250·4 . ✱153·11]
PM-VERBATIM-END PM3:✱251·15 -/
/- PM-VERBATIM-BEGIN PM3:✱251·16
✱251·16.  ⊢ . 2ᵣ ∈ NO  [✱250·41 . ✱153·211]
PM-VERBATIM-END PM3:✱251·16 -/
/- PM-VERBATIM-BEGIN PM3:✱251·17
✱251·17.  ⊢ : x ≠ y . x ≠ z . y ≠ z .⊃ . x ↓ y ↦ z ∈ Ω  [✱251·131 . ✱250·41]
PM-VERBATIM-END PM3:✱251·17 -/
/- PM-VERBATIM-BEGIN PM3:✱251·171
✱251·171.  ⊢ . 2ᵣ + i ∈ NO  [✱251·16·132]
PM-VERBATIM-END PM3:✱251·171 -/
/- PM-VERBATIM-BEGIN PM3:✱251·2
✱251·2.  ⊢ : P ∈ Rel² excl ∩ Bord . CʻP ⊂ Bord .⊃ . ΣʻP ∈ Bord
PM-VERBATIM-END PM3:✱251·2 -/

/- PM-VERBATIM-BEGIN PM3:✱251·21
✱251·21.  ⊢ : P ∈ Rel² excl ∩ Ω . CʻP ⊂ Ω .⊃ . ΣʻP ∈ Ω  [✱204·52 . ✱251·2]
PM-VERBATIM-END PM3:✱251·21 -/
/- PM-VERBATIM-BEGIN PM3:✱251·211
✱251·211.  ⊢ : NrʻP ∈ NO . NrʻʻCʻP ⊂ NO .⊃ . Σ NrʻP ∈ NO
PM-VERBATIM-END PM3:✱251·211 -/
/- PM-VERBATIM-BEGIN PM3:✱251·22
✱251·22.  ⊢ : P, Q ∈ Bord . CʻP ∩ CʻQ = Λ .⊃ . P ↥ Q ∈ Bord
PM-VERBATIM-END PM3:✱251·22 -/
/- PM-VERBATIM-BEGIN PM3:✱251·23
✱251·23.  ⊢ : P, Q ∈ Ω . CʻP ∩ CʻQ = Λ .⊃ . P ↥ Q ∈ Ω  [✱204·5 . ✱251·22]
PM-VERBATIM-END PM3:✱251·23 -/
/- PM-VERBATIM-BEGIN PM3:✱251·24
✱251·24.  ⊢ : α, β ∈ NO .⊃ . α + β ∈ NO
PM-VERBATIM-END PM3:✱251·24 -/

/- PM-VERBATIM-BEGIN PM3:✱251·25
✱251·25.  ⊢ : P ↥ Q ∈ Ω .≡ . P, Q ∈ Ω . CʻP ∩ CʻQ = Λ
PM-VERBATIM-END PM3:✱251·25 -/
/- PM-VERBATIM-BEGIN PM3:✱251·26
✱251·26.  ⊢ : α, β ∈ NO − ιʻΛ .≡ . α + β ∈ NO − ιʻΛ  [✱251·25]
PM-VERBATIM-END PM3:✱251·26 -/
/- PM-VERBATIM-BEGIN PM3:✱251·3
✱251·3.  ⊢ : P ∈ Ω . CʻP ⊂ Ser .⊃ . ΠʻP ∈ Ser  [✱204·57 . ✱250·1]
PM-VERBATIM-END PM3:✱251·3 -/
/- PM-VERBATIM-BEGIN PM3:✱251·31
✱251·31.  ⊢ : E!! BʻʻCʻP .⊃ . B ▷ CʻP ∈ FₐʻCʻP
PM-VERBATIM-END PM3:✱251·31 -/
/- PM-VERBATIM-BEGIN PM3:✱251·32
✱251·32.  ⊢ : E!! BʻʻCʻP . ∃! P .⊃ . B ▷ CʻP = BʻΠʻP
PM-VERBATIM-END PM3:✱251·32 -/

/- PM-VERBATIM-BEGIN PM3:✱251·33
✱251·33.  ⊢ : CʻP ⊂ Ω − ιʻΛ . ∃! P .⊃ . ∃! ΠʻP . B ▷ CʻP = BʻΠʻP  [✱250·13 . ✱251·32]
PM-VERBATIM-END PM3:✱251·33 -/
/- PM-VERBATIM-BEGIN PM3:✱251·34
✱251·34.  ⊢ : P ∈ Rel² excl . CʻP ⊂ Ω − ιʻΛ .⊃ . ∃! εₐʻCʻʻCʻP
PM-VERBATIM-END PM3:✱251·34 -/
/- PM-VERBATIM-BEGIN PM3:✱251·35
✱251·35.  ⊢ :: P ∈ Ω .⊃ :: α Pcl β .≡ : α, β ∈ ClʻCʻP : (∃z) . z ∈ α − β . α ∩ P⃗ʻz = β ∩ P⃗ʻz
PM-VERBATIM-END PM3:✱251·35 -/
/- PM-VERBATIM-BEGIN PM3:✱251·351
✱251·351.  ⊢ :: P ∈ Ω .⊃ :: α Pcl β .≡ : α, β ∈ ClʻCʻP : (∃z) . z ∈ β − α . α ∩ P⃗ʻz = β ∩ P⃗ʻz
  [✱251·35 . ✱170·101]
PM-VERBATIM-END PM3:✱251·351 -/
/- PM-VERBATIM-BEGIN PM3:✱251·36
✱251·36.  ⊢ : P ∈ Ω .⊃ . Pcl ∈ Ser
PM-VERBATIM-END PM3:✱251·36 -/
