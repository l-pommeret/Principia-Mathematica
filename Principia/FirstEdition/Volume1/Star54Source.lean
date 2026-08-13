/- PM-VERBATIM-BEGIN PM1:✱54·01
✱54·01.  0 = ιʻΛ  Df
PM-VERBATIM-END PM1:✱54·01 -/
/- PM-VERBATIM-BEGIN PM1:✱54·02
✱54·02.  2 = α̂{(∃x,y). x ≠ y . α = ιʻx ∪ ιʻy}  Df
PM-VERBATIM-END PM1:✱54·02 -/
/- PM-VERBATIM-BEGIN PM1:✱54·1
✱54·1.  ⊢ . 0 = ιʻΛ  [(✱54·01)]
PM-VERBATIM-END PM1:✱54·1 -/
/- PM-VERBATIM-BEGIN PM1:✱54·101
✱54·101.  ⊢ : α ε 2 .≡ .(∃x,y). x ≠ y . α = ιʻx ∪ ιʻy  [(✱54·02)]
PM-VERBATIM-END PM1:✱54·101 -/
/- PM-VERBATIM-BEGIN PM1:✱54·102
✱54·102.  ⊢ : α ε 0 .≡ . α = Λ  [✱54·1]
PM-VERBATIM-END PM1:✱54·102 -/
/- PM-VERBATIM-BEGIN PM1:✱54·21
✱54·21.  ⊢ : ιʻx ∪ ιʻy = ιʻx ∪ ιʻz .≡ . y = z  [✱51·41]
PM-VERBATIM-END PM1:✱54·21 -/
/- PM-VERBATIM-BEGIN PM1:✱54·22
✱54·22.  ⊢ : ιʻx ∪ ιʻy = ιʻz ∪ ιʻw .⊃ : x = z . y = w .∨. x = w . y = z  [✱51·43]
PM-VERBATIM-END PM1:✱54·22 -/
/- PM-VERBATIM-BEGIN PM1:✱54·25
✱54·25.  ⊢ : ιʻx ∪ ιʻy ε 1 .≡ . x = y
PM-VERBATIM-END PM1:✱54·25 -/
/- PM-VERBATIM-BEGIN PM1:✱54·26
✱54·26.  ⊢ : ιʻx ∪ ιʻy ε 2 .≡ . x ≠ y
PM-VERBATIM-END PM1:✱54·26 -/
/- PM-VERBATIM-BEGIN PM1:✱54·27
✱54·27.  ⊢ . ιʻx ∪ ιʻy ε 1 ∪ 2  [✱54·25·26]
PM-VERBATIM-END PM1:✱54·27 -/
/- PM-VERBATIM-BEGIN PM1:✱54·271
✱54·271.  ⊢ . 1 ∪ 2 = α̂{(∃x,y). α = ιʻx ∪ ιʻy}
PM-VERBATIM-END PM1:✱54·271 -/
/- PM-VERBATIM-BEGIN PM1:✱54·3
✱54·3.  ⊢ . 2 = α̂{(∃x). x ε α . α − ιʻx ε 1}
PM-VERBATIM-END PM1:✱54·3 -/
/- PM-VERBATIM-BEGIN PM1:✱54·4
✱54·4.  ⊢ : β ⊂ ιʻx ∪ ιʻy .≡ : β = Λ .∨. β = ιʻx .∨. β = ιʻy .∨. β = ιʻx ∪ ιʻy
PM-VERBATIM-END PM1:✱54·4 -/
/- PM-VERBATIM-BEGIN PM1:✱54·41
✱54·41.  ⊢ : α ε 2 .⊃ : β ⊂ α .⊃ : β = Λ .∨. β ε 1 .∨. β ε 2
PM-VERBATIM-END PM1:✱54·41 -/
/- PM-VERBATIM-BEGIN PM1:✱54·411
✱54·411.  ⊢ : α ε 2 . β ⊂ α .⊃ . β ε 0 ∪ 1 ∪ 2
PM-VERBATIM-END PM1:✱54·411 -/
/- PM-VERBATIM-BEGIN PM1:✱54·42
✱54·42.  ⊢ : α ε 2 .⊃ : β ⊂ α . β ≠ Λ .⊃ . β ε 1 ∪ 2
PM-VERBATIM-END PM1:✱54·42 -/
/- PM-VERBATIM-BEGIN PM1:✱54·43
✱54·43.  ⊢ : α,β ε 1 .⊃ : α ∩ β = Λ .≡ . α ∪ β ε 2
PM-VERBATIM-END PM1:✱54·43 -/
/- PM-VERBATIM-BEGIN PM1:✱54·44
✱54·44.  ⊢ : x,z,w ε ιʻx ∪ ιʻy . z ≠ w .⊃ : φ(z,w) .≡ . φ(x,y) .∨. φ(y,x) .∨. φ(y,y)
PM-VERBATIM-END PM1:✱54·44 -/
/- PM-VERBATIM-BEGIN PM1:✱54·441
✱54·441.  ⊢ : x,z,w ε ιʻx ∪ ιʻy . z ≠ w .⊃ : φ(z,w) .⊃ . φ(x,y) .∨. φ(y,x)
PM-VERBATIM-END PM1:✱54·441 -/
/- PM-VERBATIM-BEGIN PM1:✱54·442
✱54·442.  ⊢ : x ≠ y .⊃ : z,w ε ιʻx ∪ ιʻy . z ≠ w .⊃ : φ(z,w) .≡ . φ(x,y) .∨. φ(y,x)
PM-VERBATIM-END PM1:✱54·442 -/
/- PM-VERBATIM-BEGIN PM1:✱54·443
✱54·443.  ⊢ : x ≠ y . φ(x,y) ≠ φ(y,x) .⊃ : z,w ε ιʻx ∪ ιʻy . z ≠ w . φ(z,w) = φ(x,y)
PM-VERBATIM-END PM1:✱54·443 -/
/- PM-VERBATIM-BEGIN PM1:✱54·45
✱54·45.  ⊢ : (z,w). z,w ε ιʻx ∪ ιʻy .⊃ . φ(z,w) .≡ . φ(x,x) . φ(x,y) . φ(y,x) . φ(y,y)
PM-VERBATIM-END PM1:✱54·45 -/
/- PM-VERBATIM-BEGIN PM1:✱54·451
✱54·451.  ⊢ : φ(x,x) . φ(y,y) . φ(x,y) ≡ φ(y,x) .⊃ : (z,w). z,w ε ιʻx ∪ ιʻy .⊃ . φ(z,w) .≡ . φ(x,y) .∨. φ(y,x)
PM-VERBATIM-END PM1:✱54·451 -/
/- PM-VERBATIM-BEGIN PM1:✱54·452
✱54·452.  ⊢ : φ(x,x) . φ(y,y) . φ(x,y) ≡ φ(y,x) .⊃ : (z,w). z,w ε ιʻx ∪ ιʻy .⊃ . φ(z,w) .≡ . φ(x,y)
PM-VERBATIM-END PM1:✱54·452 -/
/- PM-VERBATIM-BEGIN PM1:✱54·46
✱54·46.  ⊢ : (z,w). z,w ε ιʻx ∪ ιʻy . z ≠ w .⊃ . x ≠ y
PM-VERBATIM-END PM1:✱54·46 -/
/- PM-VERBATIM-BEGIN PM1:✱54·5
✱54·5.  ⊢ : α ε 2 .⊃ : α ⊂ ιʻz ∪ ιʻw .≡ . α = ιʻz ∪ ιʻw
PM-VERBATIM-END PM1:✱54·5 -/
/- PM-VERBATIM-BEGIN PM1:✱54·51
✱54·51.  ⊢ : α ε 2 . β ε 1 ∪ 2 .⊃ : α ⊂ β .≡ . α = β
PM-VERBATIM-END PM1:✱54·51 -/
/- PM-VERBATIM-BEGIN PM1:✱54·52
✱54·52.  ⊢ : α,β ε 2 .⊃ : α ⊂ β .≡ . α = β .≡ . β ⊂ α
PM-VERBATIM-END PM1:✱54·52 -/
/- PM-VERBATIM-BEGIN PM1:✱54·53
✱54·53.  ⊢ : α ε 2 . z,y ε α . z ≠ y .⊃ . α = ιʻz ∪ ιʻy
PM-VERBATIM-END PM1:✱54·53 -/
/- PM-VERBATIM-BEGIN PM1:✱54·531
✱54·531.  ⊢ : α ε 2 .⊃ : z,y ε α . z ≠ y .⊃ . α = ιʻz ∪ ιʻy
PM-VERBATIM-END PM1:✱54·531 -/
/- PM-VERBATIM-BEGIN PM1:✱54·54
✱54·54.  ⊢ : α ε 2 .⊃ : (∃x,y). x,y ε α . x ≠ y . α = ιʻx ∪ ιʻy
PM-VERBATIM-END PM1:✱54·54 -/
/- PM-VERBATIM-BEGIN PM1:✱54·55
✱54·55.  ⊢ . 0 ∪ 1 ∪ 2 = α̂{(∃x,y). x ≠ y . α = ιʻx ∪ ιʻy} ∪ 0 ∪ 1
PM-VERBATIM-END PM1:✱54·55 -/
/- PM-VERBATIM-BEGIN PM1:✱54·56
✱54·56.  ⊢ : α ∉ 0 ∪ 1 ∪ 2 .≡ : (∃x,y,z). x,y,z ε α . x ≠ y . x ≠ z . y ≠ z
PM-VERBATIM-END PM1:✱54·56 -/
/- PM-VERBATIM-BEGIN PM1:✱54·6
✱54·6.  ⊢ : α ∩ β = Λ . x,y ε α . z,w ε β .⊃ : ιʻx ∪ ιʻz = ιʻy ∪ ιʻw .≡ . x = y . z = w
PM-VERBATIM-END PM1:✱54·6 -/
