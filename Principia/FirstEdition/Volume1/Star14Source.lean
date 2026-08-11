/- Source-only continuation of ✱14; no DescriptionSyntax target is claimed. -/
/- PM-VERBATIM-BEGIN PM1:✱14·02
✱14·02. E!(℩x)(φx) .=: (∃b) : φx .≡ₓ. x = b  Df
PM-VERBATIM-END PM1:✱14·02 -/
/- PM-VERBATIM-BEGIN PM1:✱14·03
✱14·03. [(℩x)(φx), (℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .=: [(℩x)(φx)] : [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)}  Df
PM-VERBATIM-END PM1:✱14·03 -/
/- PM-VERBATIM-BEGIN PM1:✱14·04
✱14·04. [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .=. [(℩x)(ψx), (℩x)(φx)] . f{(℩x)(φx), (℩x)(ψx)}  Df
PM-VERBATIM-END PM1:✱14·04 -/
/- PM-VERBATIM-BEGIN PM1:✱14·18
✱14·18. ⊢ :: E!(℩x)(φx) .⊃ : (x) . ψx .⊃ . ψ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·18 -/
/- PM-VERBATIM-BEGIN PM1:✱14·21
✱14·21. ⊢ : ψ(℩x)(φx) .⊃ . E!(℩x)(φx)
PM-VERBATIM-END PM1:✱14·21 -/
/- PM-VERBATIM-BEGIN PM1:✱14·202
✱14·202. ⊢ : φx .≡ₓ. x = b : ≡ : (℩x)(φx) = b : ≡ : φx .≡ₓ. b = x : ≡ : b = (℩x)(φx)
PM-VERBATIM-END PM1:✱14·202 -/
/- PM-VERBATIM-BEGIN PM1:✱14·204
✱14·204. ⊢ : E!(℩x)(φx) .≡ . (∃b). (℩x)(φx) = b
PM-VERBATIM-END PM1:✱14·204 -/
/- PM-VERBATIM-BEGIN PM1:✱14·205
✱14·205. ⊢ : ψ(℩x)(φx) .≡ . (∃b). b = (℩x)(φx) . ψb
PM-VERBATIM-END PM1:✱14·205 -/
/- PM-VERBATIM-BEGIN PM1:✱14·28
✱14·28. ⊢ : E!(℩x)(φx) .≡ . (℩x)(φx) = (℩x)(φx)
PM-VERBATIM-END PM1:✱14·28 -/
/- PM-VERBATIM-BEGIN PM1:✱14·13
✱14·13. ⊢ : a = (℩x)(φx) .≡ . (℩x)(φx) = a
PM-VERBATIM-END PM1:✱14·13 -/
/- PM-VERBATIM-BEGIN PM1:✱14·1
✱14·1. ⊢ : [(℩x)(φx)] . ψ(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b : ψb  [✱4·2.(*14·01)]
PM-VERBATIM-END PM1:✱14·1 -/
/- PM-VERBATIM-BEGIN PM1:✱14·101
✱14·101. ⊢ : ψ(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b : ψb  [✱14·1]
PM-VERBATIM-END PM1:✱14·101 -/
/- PM-VERBATIM-BEGIN PM1:✱14·11
✱14·11. ⊢ : E!(℩x)(φx) .≡ : (∃b) : φx .≡ₓ. x = b  [✱4·2.(*14·02)]
PM-VERBATIM-END PM1:✱14·11 -/
/- PM-VERBATIM-BEGIN PM1:✱14·111
✱14·111. ⊢ : [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .≡ : (∃b,c) : φx .≡ₓ. x = b : ψx .≡ₓ. x = c : f(b,c)
PM-VERBATIM-END PM1:✱14·111 -/
/- PM-VERBATIM-BEGIN PM1:✱14·112
✱14·112. ⊢ : f{(℩x)(φx), (℩x)(ψx)} .≡ : (∃b,c) : φx .≡ₓ. x = b : ψx .≡ₓ. x = c : f(b,c)
PM-VERBATIM-END PM1:✱14·112 -/
/- PM-VERBATIM-BEGIN PM1:✱14·113
✱14·113. ⊢ : [(℩x)(ψx)] . f{(℩x)(φx), (℩x)(ψx)} .≡ . f{(℩x)(φx), (℩x)(ψx)}  [✱14·111·112]
PM-VERBATIM-END PM1:✱14·113 -/
/- PM-VERBATIM-BEGIN PM1:✱14·12
✱14·12. ⊢ : E!(℩x)(φx) .⊃ : φx . φy .⊃ₓ,ᵧ. x = y
PM-VERBATIM-END PM1:✱14·12 -/
/- PM-VERBATIM-BEGIN PM1:✱14·121
✱14·121. ⊢ : φx .≡ₓ. x = b : φx .≡ₓ. x = c : ⊃ . b = c
PM-VERBATIM-END PM1:✱14·121 -/
/- PM-VERBATIM-BEGIN PM1:✱14·122
✱14·122. ⊢ : φx .≡ₓ. x = b : ≡ : φx .⊃ₓ. x = b : φb : ≡ : φx .⊃ₓ. x = b : (∃x). φx
PM-VERBATIM-END PM1:✱14·122 -/
/- PM-VERBATIM-BEGIN PM1:✱14·123
✱14·123. ⊢ : φ(z,w) .≡_{z,w}. z = x . w = y : ≡ : φ(z,w) .⊃_{z,w}. z = x . w = y : φ(x,y) : ≡ : φ(z,w) .⊃_{z,w}. z = x . w = y : (∃z,w). φ(z,w)
PM-VERBATIM-END PM1:✱14·123 -/
/- PM-VERBATIM-BEGIN PM1:✱14·124
✱14·124. ⊢ : (∃x,y) : φ(z,w) .≡_{z,w}. z = x . w = y : ≡ : (∃x,y). φ(x,y) : φ(z,w) . φ(u,v) .⊃_{z,w,u,v}. z = u . w = v
PM-VERBATIM-END PM1:✱14·124 -/
/- PM-VERBATIM-BEGIN PM1:✱14·131
✱14·131. ⊢ : (℩x)(φx) = (℩x)(ψx) .≡ . (℩x)(ψx) = (℩x)(φx)
PM-VERBATIM-END PM1:✱14·131 -/
/- PM-VERBATIM-BEGIN PM1:✱14·14
✱14·14. ⊢ : a = b . b = (℩x)(φx) .⊃ . a = (℩x)(φx)  [✱13·13]
PM-VERBATIM-END PM1:✱14·14 -/
/- PM-VERBATIM-BEGIN PM1:✱14·142
✱14·142. ⊢ : a = (℩x)(φx) . (℩x)(φx) = (℩x)(ψx) .⊃ . a = (℩x)(ψx)
PM-VERBATIM-END PM1:✱14·142 -/
/- PM-VERBATIM-BEGIN PM1:✱14·144
✱14·144. ⊢ : (℩x)(φx) = (℩x)(ψx) . (℩x)(ψx) = (℩x)(χx) .⊃ . (℩x)(φx) = (℩x)(χx)
PM-VERBATIM-END PM1:✱14·144 -/
/- PM-VERBATIM-BEGIN PM1:✱14·145
✱14·145. ⊢ : a = (℩x)(φx) . a = (℩x)(ψx) .⊃ . (℩x)(φx) = (℩x)(ψx)
PM-VERBATIM-END PM1:✱14·145 -/
/- PM-VERBATIM-BEGIN PM1:✱14·15
✱14·15. ⊢ : (℩x)(φx) = b .⊃ : ψ{(℩x)(φx)} .≡ . ψb
PM-VERBATIM-END PM1:✱14·15 -/
/- PM-VERBATIM-BEGIN PM1:✱14·16
✱14·16. ⊢ : (℩x)(φx) = (℩x)(ψx) .⊃ : χ{(℩x)(φx)} .≡ . χ{(℩x)(ψx)}
PM-VERBATIM-END PM1:✱14·16 -/
/- PM-VERBATIM-BEGIN PM1:✱14·17
✱14·17. ⊢ : (℩x)(φx) = b .≡ : ψ!(℩x)(φx) .≡_ψ . ψ!b
PM-VERBATIM-END PM1:✱14·17 -/
/- PM-VERBATIM-BEGIN PM1:✱14·171
✱14·171. ⊢ : (℩x)(φx) = b .≡ : ψ!b .⊃_ψ . ψ!(℩x)(φx)
PM-VERBATIM-END PM1:✱14·171 -/
/- PM-VERBATIM-BEGIN PM1:✱14·2
✱14·2. ⊢ . (℩x)(x = a) = a
PM-VERBATIM-END PM1:✱14·2 -/
/- PM-VERBATIM-BEGIN PM1:✱14·201
✱14·201. ⊢ : E!(℩x)(φx) .⊃ . (∃x). φx
PM-VERBATIM-END PM1:✱14·201 -/
/- PM-VERBATIM-BEGIN PM1:✱14·203
✱14·203. ⊢ : E!(℩x)(φx) .≡ : (∃x). φx : φx . φy .⊃ₓ,ᵧ. x = y
PM-VERBATIM-END PM1:✱14·203 -/
/- PM-VERBATIM-BEGIN PM1:✱14·22
✱14·22. ⊢ : E!(℩x)(φx) .≡ . φ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·22 -/
/- PM-VERBATIM-BEGIN PM1:✱14·23
✱14·23. ⊢ : E!(℩x)(φx . ψx) .≡ . φ{(℩x)(φx . ψx)}
PM-VERBATIM-END PM1:✱14·23 -/
/- PM-VERBATIM-BEGIN PM1:✱14·24
✱14·24. ⊢ : E!(℩x)(φx) .≡ : [(℩x)(φx)] : φy .≡ᵧ. y = (℩x)(φx)
PM-VERBATIM-END PM1:✱14·24 -/
/- PM-VERBATIM-BEGIN PM1:✱14·241
✱14·241. ⊢ : E!(℩x)(φx) .⊃ : φy .≡ᵧ. y = (℩x)(φx)
PM-VERBATIM-END PM1:✱14·241 -/
/- PM-VERBATIM-BEGIN PM1:✱14·242
✱14·242. ⊢ : φx .≡ₓ. x = b : ⊃ : ψb .≡ . ψ(℩x)(φx)  [✱14·202·15]
PM-VERBATIM-END PM1:✱14·242 -/
/- PM-VERBATIM-BEGIN PM1:✱14·25
✱14·25. ⊢ : E!(℩x)(φx) .⊃ : φx ⊃ₓ ψx .≡ . ψ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·25 -/
/- PM-VERBATIM-BEGIN PM1:✱14·26
✱14·26. ⊢ : E!(℩x)(φx) .⊃ : (∃x). φx . ψx .≡ . ψ{(℩x)(φx)} .≡ . φx ⊃ₓ ψx
PM-VERBATIM-END PM1:✱14·26 -/
/- PM-VERBATIM-BEGIN PM1:✱14·27
✱14·27. ⊢ : E!(℩x)(φx) .⊃ : φx ≡ₓ ψx .≡ . (℩x)(φx) = (℩x)(ψx)
PM-VERBATIM-END PM1:✱14·27 -/
/- PM-VERBATIM-BEGIN PM1:✱14·271
✱14·271. ⊢ : φx .≡ₓ. ψx .⊃ : E!(℩x)(φx) .≡ . E!(℩x)(ψx)
PM-VERBATIM-END PM1:✱14·271 -/
/- PM-VERBATIM-BEGIN PM1:✱14·272
✱14·272. ⊢ : φx .≡ₓ. ψx .⊃ : χ(℩x)(φx) .≡ . χ(℩x)(ψx)
PM-VERBATIM-END PM1:✱14·272 -/
/- PM-VERBATIM-BEGIN PM1:✱14·3
✱14·3. ⊢ : p ≡ q .⊃ₚ,ᵩ. f(p) ≡ f(q) : E!(℩x)(φx) .⊃ : f{[(℩x)(φx)] . χ(℩x)(φx)} .≡ . [(℩x)(φx)] . f{χ(℩x)(φx)}
PM-VERBATIM-END PM1:✱14·3 -/
/- PM-VERBATIM-BEGIN PM1:✱14·31
✱14·31. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ∨ χ(℩x)(φx) .≡ : p ∨ [(℩x)(φx)] . χ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·31 -/
/- PM-VERBATIM-BEGIN PM1:✱14·32
✱14·32. ⊢ : E!(℩x)(φx) .≡ : [(℩x)(φx)] . ∼χ(℩x)(φx) .≡ . ∼[(℩x)(φx)] . χ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·32 -/
/- PM-VERBATIM-BEGIN PM1:✱14·33
✱14·33. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ⊃ χ(℩x)(φx) .≡ : p .⊃ . [(℩x)(φx)] . χ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·33 -/
/- PM-VERBATIM-BEGIN PM1:✱14·331
✱14·331. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . χ(℩x)(φx) ⊃ p .≡ : [(℩x)(φx)] . χ(℩x)(φx) .⊃ . p
PM-VERBATIM-END PM1:✱14·331 -/
/- PM-VERBATIM-BEGIN PM1:✱14·332
✱14·332. ⊢ : E!(℩x)(φx) .⊃ : [(℩x)(φx)] . p ≡ χ(℩x)(φx) .≡ : p .≡ . [(℩x)(φx)] . χ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·332 -/
/- PM-VERBATIM-BEGIN PM1:✱14·34
✱14·34. ⊢ : p : [(℩x)(φx)] . χ(℩x)(φx) .≡ : [(℩x)(φx)] : p . χ(℩x)(φx)
PM-VERBATIM-END PM1:✱14·34 -/
/- PM-VERBATIM-BEGIN PM1:✱20·01
✱20·01. f{ẑ(ψz)} .=: (∃φ) : φ!x .≡ₓ. ψx : f{φ!ẑ}  Df
PM-VERBATIM-END PM1:✱20·01 -/
/- PM-VERBATIM-BEGIN PM1:✱20·02
✱20·02. x ε (φ!ẑ) .= . φ!x  Df
PM-VERBATIM-END PM1:✱20·02 -/
/- PM-VERBATIM-BEGIN PM1:✱20·03
✱20·03. Cls = ẑ((∃φ). α = ẑ(φ!z))  Df
PM-VERBATIM-END PM1:✱20·03 -/
/- PM-VERBATIM-BEGIN PM1:✱20·15
✱20·15. ⊢ : ψx .≡ₓ. χx : ≡ : ẑ(ψz) = ẑ(χz)
PM-VERBATIM-END PM1:✱20·15 -/
/- PM-VERBATIM-BEGIN PM1:✱20·31
✱20·31. ⊢ : ẑ(ψz) = ẑ(χz) .≡ : x ε ẑ(ψz) .≡ₓ. x ε ẑ(χz)
PM-VERBATIM-END PM1:✱20·31 -/
