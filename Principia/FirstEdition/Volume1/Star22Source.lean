/-
Copyright (c) Principia Mathematica formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Principia Mathematica formalization contributors
-/
/-! # Source-critical transcription: *22, calculus of classes -/

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
/- PM-VERBATIM-BEGIN PM1:✱22·51
✱22·51. ⊢ . α ∩ β = β ∩ α
PM-VERBATIM-END PM1:✱22·51 -/
/- PM-VERBATIM-BEGIN PM1:✱22·57
✱22·57. ⊢ . α ∪ β = β ∪ α
PM-VERBATIM-END PM1:✱22·57 -/
/- PM-VERBATIM-BEGIN PM1:✱22·52
✱22·52. ⊢ . (α ∩ β) ∩ γ = α ∩ (β ∩ γ)
PM-VERBATIM-END PM1:✱22·52 -/
/- PM-VERBATIM-BEGIN PM1:✱22·7
✱22·7. ⊢ . (α ∪ β) ∪ γ = α ∪ (β ∪ γ)
PM-VERBATIM-END PM1:✱22·7 -/
/- PM-VERBATIM-BEGIN PM1:✱22·5
✱22·5. ⊢ . α ∩ α = α
PM-VERBATIM-END PM1:✱22·5 -/
/- PM-VERBATIM-BEGIN PM1:✱22·56
✱22·56. ⊢ . α ∪ α = α
PM-VERBATIM-END PM1:✱22·56 -/
/- PM-VERBATIM-BEGIN PM1:✱22·68
✱22·68. ⊢ . (α ∩ β) ∪ (α ∩ γ) = α ∩ (β ∪ γ)
PM-VERBATIM-END PM1:✱22·68 -/
/- PM-VERBATIM-BEGIN PM1:✱22·69
✱22·69. ⊢ . (α ∪ β) ∩ (α ∪ γ) = α ∪ (β ∩ γ)
PM-VERBATIM-END PM1:✱22·69 -/
/- PM-VERBATIM-BEGIN PM1:✱22·8
✱22·8. ⊢ . −(−α) = α
PM-VERBATIM-END PM1:✱22·8 -/
/- PM-VERBATIM-BEGIN PM1:✱22·81
✱22·81. ⊢ : α ⊂ β .≡ . −β ⊂ −α
PM-VERBATIM-END PM1:✱22·81 -/
/- PM-VERBATIM-BEGIN PM1:✱22·44
✱22·44. ⊢ : α ⊂ β . β ⊂ γ .⊃ . α ⊂ γ
PM-VERBATIM-END PM1:✱22·44 -/
/- PM-VERBATIM-BEGIN PM1:✱22·441
✱22·441. ⊢ : α ⊂ β . x ε α .⊃ . x ε β
PM-VERBATIM-END PM1:✱22·441 -/
/- PM-VERBATIM-BEGIN PM1:✱22·62
✱22·62. ⊢ : α ⊂ β .≡ . α ∪ β = β
PM-VERBATIM-END PM1:✱22·62 -/
/- PM-VERBATIM-BEGIN PM1:✱22·621
✱22·621. ⊢ : α ⊂ β .≡ . α ∩ β = α
PM-VERBATIM-END PM1:✱22·621 -/
/- PM-VERBATIM-BEGIN PM1:✱22·91
✱22·91. ⊢ . α ∪ β = α ∪ (β − α)
PM-VERBATIM-END PM1:✱22·91 -/
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
