/-! # Source-critical transcription: *24, null and universal classes -/

/- PM-VERBATIM-BEGIN PM1:✱24·01
✱24·01. V = ẑx(x = x)  Df
PM-VERBATIM-END PM1:✱24·01 -/
/- PM-VERBATIM-BEGIN PM1:✱24·02
✱24·02. Λ = −V  Df
PM-VERBATIM-END PM1:✱24·02 -/
/- PM-VERBATIM-BEGIN PM1:✱24·03
✱24·03. ∃!α .= . (∃x) . x ε α  Df
PM-VERBATIM-END PM1:✱24·03 -/
/- PM-VERBATIM-BEGIN PM1:✱24·1
✱24·1. ⊢ . Λ ≠ V  [✱22·351.(✱24·02)]
PM-VERBATIM-END PM1:✱24·1 -/
/- PM-VERBATIM-BEGIN PM1:✱24·101
✱24·101. ⊢ . V = −Λ  [✱22·831.(✱24·02)]
PM-VERBATIM-END PM1:✱24·101 -/
/- PM-VERBATIM-BEGIN PM1:✱24·102
✱24·102. ⊢ : (x) . φx .≡ . ẑz(φz) = V
PM-VERBATIM-END PM1:✱24·102 -/
/- PM-VERBATIM-BEGIN PM1:✱24·103
✱24·103. ⊢ : (x) . ∼φx .≡ . ẑz(φz) = Λ
PM-VERBATIM-END PM1:✱24·103 -/
/- PM-VERBATIM-BEGIN PM1:✱24·104
✱24·104. ⊢ . (x) . x ε V
PM-VERBATIM-END PM1:✱24·104 -/
/- PM-VERBATIM-BEGIN PM1:✱24·105
✱24·105. ⊢ . (x) . x ∼ε Λ
PM-VERBATIM-END PM1:✱24·105 -/
/- PM-VERBATIM-BEGIN PM1:✱24·11
✱24·11. ⊢ . (α) . α ⊂ V
PM-VERBATIM-END PM1:✱24·11 -/
/- PM-VERBATIM-BEGIN PM1:✱24·12
✱24·12. ⊢ . (α) . Λ ⊂ α
PM-VERBATIM-END PM1:✱24·12 -/
/- PM-VERBATIM-BEGIN PM1:✱24·13
✱24·13. ⊢ : α = Λ .≡ . α ⊂ Λ
PM-VERBATIM-END PM1:✱24·13 -/
/- PM-VERBATIM-BEGIN PM1:✱24·14
✱24·14. ⊢ : (x) . x ε α .≡ . α = V
PM-VERBATIM-END PM1:✱24·14 -/
/- PM-VERBATIM-BEGIN PM1:✱24·141
✱24·141. ⊢ : V ⊂ α .≡ . V = α
PM-VERBATIM-END PM1:✱24·141 -/
/- PM-VERBATIM-BEGIN PM1:✱24·15
✱24·15. ⊢ : (x) . x ∼ε α .≡ . α = Λ
PM-VERBATIM-END PM1:✱24·15 -/
/- PM-VERBATIM-BEGIN PM1:✱24·17
✱24·17. ⊢ : α = V .≡ . −α = Λ  [✱22·83.(✱24·02)]
PM-VERBATIM-END PM1:✱24·17 -/
/- PM-VERBATIM-BEGIN PM1:✱24·21
✱24·21. ⊢ . α ∩ −α = V  [✱24·103.*22·89]
PM-VERBATIM-END PM1:✱24·21 -/
/- PM-VERBATIM-BEGIN PM1:✱24·22
✱24·22. ⊢ . α ∪ −α = V  [✱22·88.*24·102]
PM-VERBATIM-END PM1:✱24·22 -/
/- PM-VERBATIM-BEGIN PM1:✱24·23
✱24·23. ⊢ . α ∩ Λ = Λ  [✱24·12.*22·621]
PM-VERBATIM-END PM1:✱24·23 -/
/- PM-VERBATIM-BEGIN PM1:✱24·24
✱24·24. ⊢ . α ∪ Λ = α  [✱24·12.*22·62]
PM-VERBATIM-END PM1:✱24·24 -/
/- PM-VERBATIM-BEGIN PM1:✱24·26
✱24·26. ⊢ . α ∩ V = α  [✱22·621.*24·11]
PM-VERBATIM-END PM1:✱24·26 -/
/- PM-VERBATIM-BEGIN PM1:✱24·27
✱24·27. ⊢ . α ∪ V = V  [✱22·62.*24·11]
PM-VERBATIM-END PM1:✱24·27 -/
/- PM-VERBATIM-BEGIN PM1:✱24·3
✱24·3. ⊢ : α ⊂ β .≡ . α − β = Λ
PM-VERBATIM-END PM1:✱24·3 -/
/- PM-VERBATIM-BEGIN PM1:✱24·31
✱24·31. ⊢ : α ⊂ β .≡ . −α ∪ β = V
PM-VERBATIM-END PM1:✱24·31 -/
/- PM-VERBATIM-BEGIN PM1:✱24·311
✱24·311. ⊢ : α ⊂ −β .≡ . α ∩ β = Λ
PM-VERBATIM-END PM1:✱24·311 -/
/- PM-VERBATIM-BEGIN PM1:✱24·312
✱24·312. ⊢ : −α ⊂ β .≡ . α ∪ β = V
PM-VERBATIM-END PM1:✱24·312 -/
/- PM-VERBATIM-BEGIN PM1:✱24·313
✱24·313. ⊢ : α ∩ β = Λ .≡ . α = α − β  [✱24·311.*22·621]
PM-VERBATIM-END PM1:✱24·313 -/
/- PM-VERBATIM-BEGIN PM1:✱24·32
✱24·32. ⊢ : α ∪ β = Λ .≡ . α = Λ . β = Λ
PM-VERBATIM-END PM1:✱24·32 -/
/- PM-VERBATIM-BEGIN PM1:✱24·33
✱24·33. ⊢ : α = V .⊃ . α ∪ β = V
PM-VERBATIM-END PM1:✱24·33 -/
/- PM-VERBATIM-BEGIN PM1:✱24·34
✱24·34. ⊢ : α = Λ .⊃ . α ∩ β = Λ  [✱22·481.*24·23]
PM-VERBATIM-END PM1:✱24·34 -/
/- PM-VERBATIM-BEGIN PM1:✱24·35
✱24·35. ⊢ : α = V .⊃ . α ∩ β = β  [✱22·481.*24·26]
PM-VERBATIM-END PM1:✱24·35 -/
/- PM-VERBATIM-BEGIN PM1:✱24·36
✱24·36. ⊢ : α = Λ .⊃ . α ∪ β = β  [✱22·551.*24·24]
PM-VERBATIM-END PM1:✱24·36 -/
/- PM-VERBATIM-BEGIN PM1:✱24·37
✱24·37. ⊢ : α ∩ β = Λ .≡ : x ε α . y ε β .⊃ₓ,ᵧ . x ≠ y
PM-VERBATIM-END PM1:✱24·37 -/
/- PM-VERBATIM-BEGIN PM1:✱24·38
✱24·38. ⊢ : α ∩ β = Λ .⊃ : α ≠ β .∨ . α = Λ . β = Λ
PM-VERBATIM-END PM1:✱24·38 -/
/- PM-VERBATIM-BEGIN PM1:✱24·39
✱24·39. ⊢ : α ∩ β = Λ .≡ : x ε α .⊃ₓ . x ∼ε β  [✱24·311.*22·35]
PM-VERBATIM-END PM1:✱24·39 -/
/- PM-VERBATIM-BEGIN PM1:✱24·4
✱24·4. ⊢ : α ∩ β = Λ .≡ . (α ∪ β) − α = β .≡ . (α ∪ β) − β = α
PM-VERBATIM-END PM1:✱24·4 -/
/- PM-VERBATIM-BEGIN PM1:✱24·401
✱24·401. ⊢ : β ⊂ α .⊃ . (β ∪ γ) − α = γ − α
PM-VERBATIM-END PM1:✱24·401 -/
/- PM-VERBATIM-BEGIN PM1:✱24·402
✱24·402. ⊢ : α ∩ β = Λ . ξ ⊂ α . η ⊂ β .⊃ . ξ ∩ η = Λ
PM-VERBATIM-END PM1:✱24·402 -/
/- PM-VERBATIM-BEGIN PM1:✱24·41
✱24·41. ⊢ . α = (α ∩ β) ∪ (α − β)
PM-VERBATIM-END PM1:✱24·41 -/
/- PM-VERBATIM-BEGIN PM1:✱24·411
✱24·411. ⊢ : β ⊂ α .⊃ . α = β ∪ (α − β)
PM-VERBATIM-END PM1:✱24·411 -/
/- PM-VERBATIM-BEGIN PM1:✱24·412
✱24·412. ⊢ : β ⊂ α . γ ⊂ β .⊃ . (α − β) ∪ (β − γ) = α − γ
PM-VERBATIM-END PM1:✱24·412 -/
/- PM-VERBATIM-BEGIN PM1:✱24·42
✱24·42. ⊢ : α ∩ β ⊂ γ . α − β ⊂ γ .≡ . α ⊂ γ
PM-VERBATIM-END PM1:✱24·42 -/
/- PM-VERBATIM-BEGIN PM1:✱24·43
✱24·43. ⊢ : α − β ⊂ γ .≡ . α ⊂ β ∪ γ
PM-VERBATIM-END PM1:✱24·43 -/
/- PM-VERBATIM-BEGIN PM1:✱24·431
✱24·431. ⊢ . (α ∪ γ) ∩ (β ∪ −γ) = (α ∩ γ) ∪ (α − γ) ∪ (β ∩ γ)
PM-VERBATIM-END PM1:✱24·431 -/
/- PM-VERBATIM-BEGIN PM1:✱24·432
✱24·432. ⊢ . (α − γ) ∪ (β ∩ γ) = (α ∩ β) ∪ (α − γ) ∪ (β ∩ γ)
PM-VERBATIM-END PM1:✱24·432 -/
/- PM-VERBATIM-BEGIN PM1:✱24·44
✱24·44. ⊢ . (α ∪ γ) ∩ (β ∪ −γ) = (α ∩ −γ) ∪ (β ∩ γ)  [✱24·431·432]
PM-VERBATIM-END PM1:✱24·44 -/
/- PM-VERBATIM-BEGIN PM1:✱24·45
✱24·45. ⊢ : (α ∩ γ) ∪ (β − γ) = Λ .≡ . β ⊂ γ . γ ⊂ −α
PM-VERBATIM-END PM1:✱24·45 -/
/- PM-VERBATIM-BEGIN PM1:✱24·46
✱24·46. ⊢ : (α ∩ γ) ∪ (β − γ) = Λ .⊃ . α ∩ β = Λ
PM-VERBATIM-END PM1:✱24·46 -/
