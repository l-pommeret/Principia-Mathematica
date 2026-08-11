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
