/-
Copyright (c) Principia Mathematica formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Principia Mathematica formalization contributors
-/
/-! # Source-critical transcription: *22, calculus of classes -/

/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·01
✱22·01. α ⊂ β .=: x ε α .⊃ₓ. x ε β  Df
PM-VERBATIM-SUMMARY-END PM1:✱22·01 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·02
✱22·02. α ∩ β = ẑx(x ε α . x ε β)  Df
PM-VERBATIM-SUMMARY-END PM1:✱22·02 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·03
✱22·03. α ∪ β = ẑx(x ε α .∨. x ε β)  Df
PM-VERBATIM-SUMMARY-END PM1:✱22·03 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·04
✱22·04. −α = ẑx(x ∼ε α)  Df
PM-VERBATIM-SUMMARY-END PM1:✱22·04 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·05
✱22·05. α − β = α ∩ −β  Df
PM-VERBATIM-SUMMARY-END PM1:✱22·05 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·51
✱22·51. ⊢ . α ∩ β = β ∩ α
PM-VERBATIM-SUMMARY-END PM1:✱22·51 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·57
✱22·57. ⊢ . α ∪ β = β ∪ α
PM-VERBATIM-SUMMARY-END PM1:✱22·57 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·52
✱22·52. ⊢ . (α ∩ β) ∩ γ = α ∩ (β ∩ γ)
PM-VERBATIM-SUMMARY-END PM1:✱22·52 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·7
✱22·7. ⊢ . (α ∪ β) ∪ γ = α ∪ (β ∪ γ)
PM-VERBATIM-SUMMARY-END PM1:✱22·7 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·5
✱22·5. ⊢ . α ∩ α = α
PM-VERBATIM-SUMMARY-END PM1:✱22·5 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·56
✱22·56. ⊢ . α ∪ α = α
PM-VERBATIM-SUMMARY-END PM1:✱22·56 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·68
✱22·68. ⊢ . (α ∩ β) ∪ (α ∩ γ) = α ∩ (β ∪ γ)
PM-VERBATIM-SUMMARY-END PM1:✱22·68 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·69
✱22·69. ⊢ . (α ∪ β) ∩ (α ∪ γ) = α ∪ (β ∩ γ)
PM-VERBATIM-SUMMARY-END PM1:✱22·69 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·8
✱22·8. ⊢ . −(−α) = α
PM-VERBATIM-SUMMARY-END PM1:✱22·8 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·81
✱22·81. ⊢ : α ⊂ β .≡ . −β ⊂ −α
PM-VERBATIM-SUMMARY-END PM1:✱22·81 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·44
✱22·44. ⊢ : α ⊂ β . β ⊂ γ .⊃ . α ⊂ γ
PM-VERBATIM-SUMMARY-END PM1:✱22·44 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·441
✱22·441. ⊢ : α ⊂ β . x ε α .⊃ . x ε β
PM-VERBATIM-SUMMARY-END PM1:✱22·441 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·62
✱22·62. ⊢ : α ⊂ β .≡ . α ∪ β = β
PM-VERBATIM-SUMMARY-END PM1:✱22·62 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·621
✱22·621. ⊢ : α ⊂ β .≡ . α ∩ β = α
PM-VERBATIM-SUMMARY-END PM1:✱22·621 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱22·91
✱22·91. ⊢ . α ∪ β = α ∪ (β − α)
PM-VERBATIM-SUMMARY-END PM1:✱22·91 -/
/- PM-VERBATIM-BEGIN PM1:✱22·1
✱22·1. ⊢ : α ⊂ β .≡ : x ε α .⊃ₓ. x ε β  [✱4·2.(✱22·01)]
PM-VERBATIM-END PM1:✱22·1 -/
/- PM-VERBATIM-BEGIN PM1:✱22·2
✱22·2. ⊢ . α ∩ β = ẑx(x ε α . x ε β)  [✱20·2.(✱22·02)]
PM-VERBATIM-END PM1:✱22·2 -/
/- PM-VERBATIM-BEGIN PM1:✱22·3
✱22·3. ⊢ . α ∪ β = ẑx(x ε α .∨. x ε β)  [✱20·2.(✱22·03)]
PM-VERBATIM-END PM1:✱22·3 -/
/- PM-VERBATIM-BEGIN PM1:✱22·31
✱22·31. ⊢ . −α = ẑx(x ∼ε α)  [✱20·2.(✱22·04)]
PM-VERBATIM-END PM1:✱22·31 -/
/- PM-VERBATIM-BEGIN PM1:✱22·32
✱22·32. ⊢ . α − β = ẑx(x ε α . x ∼ε β)  [✱20·2.(✱22·05).*22·2.*20·32]
PM-VERBATIM-END PM1:✱22·32 -/
/- PM-VERBATIM-BEGIN PM1:✱22·33
✱22·33. ⊢ : x ε α ∩ β .≡ . x ε α . x ε β  [✱20·3.*22·2]
PM-VERBATIM-END PM1:✱22·33 -/
/- PM-VERBATIM-BEGIN PM1:✱22·34
✱22·34. ⊢ : x ε α ∪ β .≡ : x ε α .∨. x ε β  [✱20·3.*22·3]
PM-VERBATIM-END PM1:✱22·34 -/
/- PM-VERBATIM-BEGIN PM1:✱22·35
✱22·35. ⊢ : x ε −α .≡ . x ∼ε α  [✱20·3.*22·31]
PM-VERBATIM-END PM1:✱22·35 -/
/- PM-VERBATIM-BEGIN PM1:✱22·351
✱22·351. ⊢ . −α ≠ α
PM-VERBATIM-END PM1:✱22·351 -/
/- PM-VERBATIM-BEGIN PM1:✱22·36
✱22·36. ⊢ . α ∩ β ε Cls  [✱20·41]
PM-VERBATIM-END PM1:✱22·36 -/
/- PM-VERBATIM-BEGIN PM1:✱22·37
✱22·37. ⊢ . α ∪ β ε Cls  [✱20·41]
PM-VERBATIM-END PM1:✱22·37 -/
/- PM-VERBATIM-BEGIN PM1:✱22·38
✱22·38. ⊢ . −α ε Cls  [✱20·41]
PM-VERBATIM-END PM1:✱22·38 -/
/- PM-VERBATIM-BEGIN PM1:✱22·39
✱22·39. ⊢ . ẑz(φz) ∩ ẑz(ψz) = ẑz(φz . ψz)
PM-VERBATIM-END PM1:✱22·39 -/
/- PM-VERBATIM-BEGIN PM1:✱22·391
✱22·391. ⊢ . ẑz(φz) ∪ ẑz(ψz) = ẑz(φz ∨ ψz)  [Similar proof]
PM-VERBATIM-END PM1:✱22·391 -/
/- PM-VERBATIM-BEGIN PM1:✱22·392
✱22·392. ⊢ . −ẑz(φz) = ẑz(∼φz)  [Similar proof]
PM-VERBATIM-END PM1:✱22·392 -/
/- PM-VERBATIM-BEGIN PM1:✱22·4
✱22·4. ⊢ : α ⊂ β . β ⊂ α .≡ : x ε α .≡ₓ. x ε β
PM-VERBATIM-END PM1:✱22·4 -/
/- PM-VERBATIM-BEGIN PM1:✱22·41
✱22·41. ⊢ : α ⊂ β . β ⊂ α .≡ . α = β  [✱22·4.*20·43]
PM-VERBATIM-END PM1:✱22·41 -/
/- PM-VERBATIM-BEGIN PM1:✱22·42
✱22·42. ⊢ . α ⊂ α  [Id.*10·11]
PM-VERBATIM-END PM1:✱22·42 -/
/- PM-VERBATIM-BEGIN PM1:✱22·43
✱22·43. ⊢ : α ∩ β ⊂ α  [✱3·26.*10·11]
PM-VERBATIM-END PM1:✱22·43 -/
/- PM-VERBATIM-BEGIN PM1:✱22·45
✱22·45. ⊢ : α ⊂ β . α ⊂ γ .≡ . α ⊂ β ∩ γ
PM-VERBATIM-END PM1:✱22·45 -/
/- PM-VERBATIM-BEGIN PM1:✱22·46
✱22·46. ⊢ : x ε α . α ⊂ β .⊃ . x ε β  [✱22·441.Perm]
PM-VERBATIM-END PM1:✱22·46 -/
/- PM-VERBATIM-BEGIN PM1:✱22·47
✱22·47. ⊢ : α ⊂ γ .⊃ . α ∩ β ⊂ γ  [✱22·43·44]
PM-VERBATIM-END PM1:✱22·47 -/
/- PM-VERBATIM-BEGIN PM1:✱22·48
✱22·48. ⊢ : α ⊂ β .⊃ . α ∩ γ ⊂ β ∩ γ  [✱10·31]
PM-VERBATIM-END PM1:✱22·48 -/
/- PM-VERBATIM-BEGIN PM1:✱22·481
✱22·481. ⊢ : α = β .⊃ . α ∩ γ = β ∩ γ
PM-VERBATIM-END PM1:✱22·481 -/
/- PM-VERBATIM-BEGIN PM1:✱22·49
✱22·49. ⊢ : α ⊂ β . γ ⊂ δ .⊃ . α ∩ γ ⊂ β ∩ δ  [✱10·39]
PM-VERBATIM-END PM1:✱22·49 -/
/- PM-VERBATIM-BEGIN PM1:✱22·01
✱22·01. α ⊂ β .=: x ε α .⊃ₓ. x ε β  Df
PM-VERBATIM-END PM1:✱22·01 -/
/- PM-VERBATIM-BEGIN PM1:✱22·02
✱22·02. α ∩ β = ẑx(x ε α . x ε β)  Df
PM-VERBATIM-END PM1:✱22·02 -/
/- PM-VERBATIM-BEGIN PM1:✱22·03
✱22·03. α ∪ β = ẑx(x ε α .∨. x ε β)  Df
PM-VERBATIM-END PM1:✱22·03 -/
/- PM-VERBATIM-BEGIN PM1:✱22·04
✱22·04. −α = ẑx(x ∼ε α)  Df
PM-VERBATIM-END PM1:✱22·04 -/
/- PM-VERBATIM-BEGIN PM1:✱22·05
✱22·05. α − β = α ∩ −β  Df
PM-VERBATIM-END PM1:✱22·05 -/
/- PM-VERBATIM-BEGIN PM1:✱22·44
✱22·44. ⊢ : α ⊂ β . β ⊂ γ .⊃ . α ⊂ γ  [✱10·3]
PM-VERBATIM-END PM1:✱22·44 -/
/- PM-VERBATIM-BEGIN PM1:✱22·441
✱22·441. ⊢ : α ⊂ β . x ε α .⊃ . x ε β  [✱10·1.Imp]
PM-VERBATIM-END PM1:✱22·441 -/
/- PM-VERBATIM-BEGIN PM1:✱22·5
✱22·5. ⊢ . α ∩ α = α
PM-VERBATIM-END PM1:✱22·5 -/
/- PM-VERBATIM-BEGIN PM1:✱22·51
✱22·51. ⊢ . α ∩ β = β ∩ α  [✱22·33.*4·3.*10·11.*20·43]
PM-VERBATIM-END PM1:✱22·51 -/
/- PM-VERBATIM-BEGIN PM1:✱22·52
✱22·52. ⊢ . (α ∩ β) ∩ γ = α ∩ (β ∩ γ)  [✱22·33.*4·32.*10·11.*20·43]
PM-VERBATIM-END PM1:✱22·52 -/
/- PM-VERBATIM-BEGIN PM1:✱22·56
✱22·56. ⊢ . α ∪ α = α  [✱4·25.*10·11]
PM-VERBATIM-END PM1:✱22·56 -/
/- PM-VERBATIM-BEGIN PM1:✱22·57
✱22·57. ⊢ . α ∪ β = β ∪ α  [✱4·31.*10·11]
PM-VERBATIM-END PM1:✱22·57 -/
/- PM-VERBATIM-BEGIN PM1:✱22·7
✱22·7. ⊢ . (α ∪ β) ∪ γ = α ∪ (β ∪ γ)  [✱4·33]
PM-VERBATIM-END PM1:✱22·7 -/
/- PM-VERBATIM-BEGIN PM1:✱22·68
✱22·68. ⊢ . (α ∩ β) ∪ (α ∩ γ) = α ∩ (β ∪ γ)
PM-VERBATIM-END PM1:✱22·68 -/
/- PM-VERBATIM-BEGIN PM1:✱22·69
✱22·69. ⊢ . (α ∪ β) ∩ (α ∪ γ) = α ∪ (β ∩ γ)  [Similar proof, by ✱4·41]
PM-VERBATIM-END PM1:✱22·69 -/
/- PM-VERBATIM-BEGIN PM1:✱22·8
✱22·8. ⊢ . −(−α) = α  [✱4·13]
PM-VERBATIM-END PM1:✱22·8 -/
/- PM-VERBATIM-BEGIN PM1:✱22·81
✱22·81. ⊢ : α ⊂ β .≡ . −β ⊂ −α  [✱4·1]
PM-VERBATIM-END PM1:✱22·81 -/
/- PM-VERBATIM-BEGIN PM1:✱22·62
✱22·62. ⊢ : α ⊂ β .≡ . α ∪ β = β
PM-VERBATIM-END PM1:✱22·62 -/
/- PM-VERBATIM-BEGIN PM1:✱22·621
✱22·621. ⊢ : α ⊂ β .≡ . α ∩ β = α  [✱4·71]
PM-VERBATIM-END PM1:✱22·621 -/
/- PM-VERBATIM-BEGIN PM1:✱22·91
✱22·91. ⊢ . α ∪ β = α ∪ (β − α)
PM-VERBATIM-END PM1:✱22·91 -/
/- PM-VERBATIM-BEGIN PM1:✱22·53
✱22·53. α ∩ β ∩ γ = (α ∩ β) ∩ γ  Df
PM-VERBATIM-END PM1:✱22·53 -/
/- PM-VERBATIM-BEGIN PM1:✱22·54
✱22·54. ⊢ : α = β .⊃ : α ⊂ γ .≡ . β ⊂ γ  [✱20·18]
PM-VERBATIM-END PM1:✱22·54 -/
/- PM-VERBATIM-BEGIN PM1:✱22·55
✱22·55. ⊢ : α = β .⊃ : γ ⊂ α .≡ . γ ⊂ β  [✱20·18]
PM-VERBATIM-END PM1:✱22·55 -/
/- PM-VERBATIM-BEGIN PM1:✱22·551
✱22·551. ⊢ : α = β .⊃ . α ∪ γ = β ∪ γ  [✱10·411]
PM-VERBATIM-END PM1:✱22·551 -/
/- PM-VERBATIM-BEGIN PM1:✱22·58
✱22·58. ⊢ . α ⊂ α ∪ β . β ⊂ α ∪ β  [✱1·3.*2·2]
PM-VERBATIM-END PM1:✱22·58 -/
/- PM-VERBATIM-BEGIN PM1:✱22·59
✱22·59. ⊢ : α ⊂ γ . β ⊂ γ .≡ . α ∪ β ⊂ γ
PM-VERBATIM-END PM1:✱22·59 -/
/- PM-VERBATIM-BEGIN PM1:✱22·6
✱22·6. ⊢ : x ε α ∪ β .≡ : α ⊂ γ . β ⊂ γ .⊃ᵧ. x ε γ
PM-VERBATIM-END PM1:✱22·6 -/
/- PM-VERBATIM-BEGIN PM1:✱22·61
✱22·61. ⊢ : α ⊂ β .⊃ . α ⊂ β ∪ γ  [✱22·44·58]
PM-VERBATIM-END PM1:✱22·61 -/
/- PM-VERBATIM-BEGIN PM1:✱22·63
✱22·63. ⊢ . α ∪ (α ∩ β) = α  [✱4·44]
PM-VERBATIM-END PM1:✱22·63 -/
/- PM-VERBATIM-BEGIN PM1:✱22·631
✱22·631. ⊢ . α ∩ (α ∪ β) = α  [✱22·58·621]
PM-VERBATIM-END PM1:✱22·631 -/
/- PM-VERBATIM-BEGIN PM1:✱22·632
✱22·632. ⊢ : α = β .⊃ . α = α ∩ β  [✱22·42·621]
PM-VERBATIM-END PM1:✱22·632 -/
/- PM-VERBATIM-BEGIN PM1:✱22·633
✱22·633. ⊢ : α ⊂ β .⊃ . α ∪ γ = (α ∩ β) ∪ γ  [✱22·551·621]
PM-VERBATIM-END PM1:✱22·633 -/
/- PM-VERBATIM-BEGIN PM1:✱22·64
✱22·64. ⊢ : α ⊂ γ .∨ . β ⊂ γ .⊃ . α ∩ β ⊂ γ
PM-VERBATIM-END PM1:✱22·64 -/
/- PM-VERBATIM-BEGIN PM1:✱22·65
✱22·65. ⊢ : α ⊂ β .∨ . α ⊂ γ .⊃ . α ⊂ β ∪ γ  [✱22·61·57.*4·77]
PM-VERBATIM-END PM1:✱22·65 -/
/- PM-VERBATIM-BEGIN PM1:✱22·66
✱22·66. ⊢ : α ⊂ β .⊃ . α ∪ γ ⊂ β ∪ γ  [✱2·38]
PM-VERBATIM-END PM1:✱22·66 -/
/- PM-VERBATIM-BEGIN PM1:✱22·71
✱22·71. α ∪ β ∪ γ = (α ∪ β) ∪ γ  Df
PM-VERBATIM-END PM1:✱22·71 -/
/- PM-VERBATIM-BEGIN PM1:✱22·72
✱22·72. ⊢ : α ⊂ γ . β ⊂ δ .⊃ . α ∪ β ⊂ γ ∪ δ  [✱3·48]
PM-VERBATIM-END PM1:✱22·72 -/
/- PM-VERBATIM-BEGIN PM1:✱22·73
✱22·73. ⊢ : α = γ . β = δ .⊃ . α ∪ β = γ ∪ δ  [✱10·411]
PM-VERBATIM-END PM1:✱22·73 -/
/- PM-VERBATIM-BEGIN PM1:✱22·74
✱22·74. ⊢ : α ∩ β ⊂ γ . α ∩ γ ⊂ β .≡ . α ∩ β = α ∩ γ
PM-VERBATIM-END PM1:✱22·74 -/
/- PM-VERBATIM-BEGIN PM1:✱22·811
✱22·811. ⊢ : α ⊂ −β .≡ . β ⊂ −α  [✱4·1.*22·8]
PM-VERBATIM-END PM1:✱22·811 -/
/- PM-VERBATIM-BEGIN PM1:✱22·82
✱22·82. ⊢ : α ∩ β ⊂ γ .≡ . α − γ ⊂ −β  [✱4·14]
PM-VERBATIM-END PM1:✱22·82 -/
/- PM-VERBATIM-BEGIN PM1:✱22·83
✱22·83. ⊢ : α = β .≡ . −α = −β  [✱4·11]
PM-VERBATIM-END PM1:✱22·83 -/
/- PM-VERBATIM-BEGIN PM1:✱22·831
✱22·831. ⊢ : α = −β .≡ . β = −α  [✱4·12]
PM-VERBATIM-END PM1:✱22·831 -/
/- PM-VERBATIM-BEGIN PM1:✱22·84
✱22·84. ⊢ . −(α ∩ β) = −α ∪ −β  [✱4·51]
PM-VERBATIM-END PM1:✱22·84 -/
/- PM-VERBATIM-BEGIN PM1:✱22·85
✱22·85. ⊢ . α ∩ β = −(−α ∪ −β)  [✱22·84·831]
PM-VERBATIM-END PM1:✱22·85 -/
/- PM-VERBATIM-BEGIN PM1:✱22·86
✱22·86. ⊢ . −(−α ∩ −β) = α ∪ β  [✱4·57]
PM-VERBATIM-END PM1:✱22·86 -/
/- PM-VERBATIM-BEGIN PM1:✱22·87
✱22·87. ⊢ . −α ∩ −β = −(α ∪ β)  [✱22·86·831]
PM-VERBATIM-END PM1:✱22·87 -/
/- PM-VERBATIM-BEGIN PM1:✱22·88
✱22·88. ⊢ . (x) . x ε (α ∪ −α)  [✱2·11]
PM-VERBATIM-END PM1:✱22·88 -/
