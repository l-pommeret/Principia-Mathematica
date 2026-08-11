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
