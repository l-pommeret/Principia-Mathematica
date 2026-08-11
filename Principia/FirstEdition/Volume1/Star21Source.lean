/- PM-VERBATIM-BEGIN PM1:✱21·01
✱21·01. f{ẑxẑyψ(x,y)} .=: (∃φ) : φ!(x,y) .≡₍x,y₎. ψ(x,y) : f{φ!(ẑu,ẑv)}  Df
PM-VERBATIM-END PM1:✱21·01 -/

/- PM-VERBATIM-BEGIN PM1:✱21·02
✱21·02. a{φ!(ẑx,ẑy)}b .= . φ!(a,b)  Df
PM-VERBATIM-END PM1:✱21·02 -/

/- PM-VERBATIM-BEGIN PM1:✱21·03
✱21·03. Rel = ẑR{(∃φ). R = ẑxẑyφ!(x,y)}  Df
PM-VERBATIM-END PM1:✱21·03 -/

/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱21·15
✱21·15. ⊢ : ψ(x,y) .≡₍x,y₎. χ(x,y) : ≡ . ẑxẑyψ(x,y) = ẑxẑyχ(x,y)
PM-VERBATIM-SUMMARY-END PM1:✱21·15 -/

/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱21·31
✱21·31. ⊢ : ẑxẑyψ(x,y) = ẑxẑyχ(x,y) .≡ : x{ẑxẑyψ(x,y)}y .≡₍x,y₎. x{ẑxẑyχ(x,y)}y
PM-VERBATIM-SUMMARY-END PM1:✱21·31 -/

/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱21·43
✱21·43. ⊢ : R = S .≡ : xRy .≡₍x,y₎. xSy
PM-VERBATIM-SUMMARY-END PM1:✱21·43 -/

/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱21·3
✱21·3. ⊢ : x{ẑxẑyψ(x,y)}y .≡ . ψ(x,y)
PM-VERBATIM-SUMMARY-END PM1:✱21·3 -/

/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱21·151
✱21·151. ⊢ . (∃φ) . ẑxẑyψ(x,y) = ẑxẑyφ!(x,y)
PM-VERBATIM-SUMMARY-END PM1:✱21·151 -/

/- PM-VERBATIM-BEGIN PM1:✱21·07
✱21·07. (R). fR .= . (φ). f{ẑxẑyφ!(x,y)}  Df
PM-VERBATIM-END PM1:✱21·07 -/

/- PM-VERBATIM-BEGIN PM1:✱21·071
✱21·071. (∃R). fR .= . (∃φ). f{ẑxẑyφ!(x,y)}  Df
PM-VERBATIM-END PM1:✱21·071 -/

/- PM-VERBATIM-BEGIN PM1:✱21·072
✱21·072. [(℩R)(φR)]. f(℩R)(φR) .=: (∃S) : φR .≡ᴿ. R = S : fS  Df
PM-VERBATIM-END PM1:✱21·072 -/

/- PM-VERBATIM-BEGIN PM1:✱21·08
✱21·08. f{ẑRẑSψ(R,S)} .=: (∃φ) : ψ(R,S) .≡₍R,S₎. φ!(R,S) : f{φ!(ẑR,ẑS)}  Df
PM-VERBATIM-END PM1:✱21·08 -/

/- PM-VERBATIM-BEGIN PM1:✱21·081
✱21·081. P{φ!(ẑR,ẑS)}Q .= . φ!(P,Q)  Df
PM-VERBATIM-END PM1:✱21·081 -/

/- PM-VERBATIM-BEGIN PM1:✱21·082
✱21·082. f{ẑR(ψR)} .=: (∃φ) : ψR .≡ᴿ. φ!R : f(φ!ẑR)  Df
PM-VERBATIM-END PM1:✱21·082 -/

/- PM-VERBATIM-BEGIN PM1:✱21·083
✱21·083. R ε φ!ẑR .= . φ!R  Df
PM-VERBATIM-END PM1:✱21·083 -/

/- PM-VERBATIM-BEGIN PM1:✱21·1
✱21·1. ⊢ : f{ẑxẑyψ(x,y)} .≡ : (∃φ) : φ!(x,y) .≡₍x,y₎. ψ(x,y) : f{φ!(ẑu,ẑv)}  [✱4·2.(✱21·01)]
PM-VERBATIM-END PM1:✱21·1 -/

/- PM-VERBATIM-BEGIN PM1:✱21·11
✱21·11. ⊢ : ψ(x,y) .≡₍x,y₎. χ(x,y) .⊃ : f{ẑxẑyψ(x,y)} .≡ . f{ẑxẑyχ(x,y)}  [✱4·86·36.*10·281.*21·1]
PM-VERBATIM-END PM1:✱21·11 -/

/- PM-VERBATIM-BEGIN PM1:✱21·111
✱21·111. ⊢ : f{φ!(ẑx,ẑy)} .≡ᵠ. g{φ!(x,y)} .⊃ : f{ẑxẑyφ!(x,y)} .≡ᵠ. g{ẑxẑyφ!(x,y)}
PM-VERBATIM-END PM1:✱21·111 -/

/- PM-VERBATIM-BEGIN PM1:✱21·112
✱21·112. ⊢ : (∃g) : f{ẑxẑyφ!(x,y)} .≡ᵠ. g!{ẑxẑyφ!(x,y)}  [✱12·1.*21·111]
PM-VERBATIM-END PM1:✱21·112 -/

/- PM-VERBATIM-BEGIN PM1:✱21·12
✱21·12. ⊢ : (∃φ) : φ!(x,y) .≡₍x,y₎. ψ(x,y) : f{ẑxẑyψ(x,y)} .≡ . f{ẑxẑyφ!(x,y)}  [✱21·11.*12·11]
PM-VERBATIM-END PM1:✱21·12 -/

/- PM-VERBATIM-BEGIN PM1:✱21·13
✱21·13. ⊢ : ψ(x,y) .≡₍x,y₎. χ(x,y) .⊃ . ẑxẑyψ(x,y) = ẑxẑyχ(x,y)  [✱21·1.*12·11.*13·195]
PM-VERBATIM-END PM1:✱21·13 -/
/- PM-VERBATIM-BEGIN PM1:✱21·14
✱21·14. ⊢ : ẑxẑyψ(x,y) = ẑxẑyχ(x,y) .⊃ : ψ(x,y) .≡₍x,y₎. χ(x,y)
PM-VERBATIM-END PM1:✱21·14 -/
/- PM-VERBATIM-BEGIN PM1:✱21·15
✱21·15. ⊢ : ψ(x,y) .≡₍x,y₎. χ(x,y) : ≡ . ẑxẑyψ(x,y) = ẑxẑyχ(x,y)
PM-VERBATIM-END PM1:✱21·15 -/
/- PM-VERBATIM-BEGIN PM1:✱21·151
✱21·151. ⊢ . (∃φ) . ẑxẑyψ(x,y) = ẑxẑyφ!(x,y)
PM-VERBATIM-END PM1:✱21·151 -/
/- PM-VERBATIM-BEGIN PM1:✱21·16
✱21·16. ⊢ : (∃φ) : f{ẑxẑyψ(x,y)} .≡ . f{ẑxẑyφ!(x,y)}
PM-VERBATIM-END PM1:✱21·16 -/
/- PM-VERBATIM-BEGIN PM1:✱21·17
✱21·17. ⊢ : (φ). f{ẑxẑyφ!(x,y)} .⊃ . f{ẑxẑyψ(x,y)}
PM-VERBATIM-END PM1:✱21·17 -/
/- PM-VERBATIM-BEGIN PM1:✱21·2
✱21·2. ⊢ . ẑxẑyφ(x,y) = ẑxẑyφ(x,y)
PM-VERBATIM-END PM1:✱21·2 -/
/- PM-VERBATIM-BEGIN PM1:✱21·21
✱21·21. ⊢ : ẑxẑyφ(x,y) = ẑxẑyψ(x,y) .≡ . ẑxẑyψ(x,y) = ẑxẑyφ(x,y)
PM-VERBATIM-END PM1:✱21·21 -/
/- PM-VERBATIM-BEGIN PM1:✱21·22
✱21·22. ⊢ : ẑxẑyφ(x,y) = ẑxẑyψ(x,y) . ẑxẑyψ(x,y) = ẑxẑyχ(x,y) .⊃ . ẑxẑyφ(x,y) = ẑxẑyχ(x,y)
PM-VERBATIM-END PM1:✱21·22 -/
/- PM-VERBATIM-BEGIN PM1:✱21·23
✱21·23. ⊢ : ẑxẑyφ(x,y) = ẑxẑyψ(x,y) . ẑxẑyφ(x,y) = ẑxẑyχ(x,y) .⊃ . ẑxẑyψ(x,y) = ẑxẑyχ(x,y)
PM-VERBATIM-END PM1:✱21·23 -/
/- PM-VERBATIM-BEGIN PM1:✱21·24
✱21·24. ⊢ : ẑxẑyψ(x,y) = ẑxẑyφ(x,y) . ẑxẑyχ(x,y) = ẑxẑyφ(x,y) .⊃ . ẑxẑyψ(x,y) = ẑxẑyχ(x,y)
PM-VERBATIM-END PM1:✱21·24 -/
/- PM-VERBATIM-BEGIN PM1:✱21·32
✱21·32. ⊢ . ẑxẑy[x{ẑxẑyφ(x,y)}y] = ẑxẑyφ(x,y)
PM-VERBATIM-END PM1:✱21·32 -/
/- PM-VERBATIM-BEGIN PM1:✱21·33
✱21·33. ⊢ : R = ẑxẑyφ(x,y) .≡ : xRy .≡₍x,y₎. φ(x,y)
PM-VERBATIM-END PM1:✱21·33 -/
/- PM-VERBATIM-BEGIN PM1:✱21·4
✱21·4. ⊢ : R ε Rel .≡ . (∃φ). R = ẑxẑyφ!(x,y)
PM-VERBATIM-END PM1:✱21·4 -/
/- PM-VERBATIM-BEGIN PM1:✱21·41
✱21·41. ⊢ . ẑxẑyφ(x,y) ε Rel
PM-VERBATIM-END PM1:✱21·41 -/
/- PM-VERBATIM-BEGIN PM1:✱21·42
✱21·42. ⊢ . ẑxẑy(xRy) = R
PM-VERBATIM-END PM1:✱21·42 -/
/- PM-VERBATIM-BEGIN PM1:✱21·53
✱21·53. ⊢ : S = R .⊃ₛ. φS : ≡ . φR
PM-VERBATIM-END PM1:✱21·53 -/
/- PM-VERBATIM-BEGIN PM1:✱21·54
✱21·54. ⊢ : (∃S). S = R . φS .≡ . φR
PM-VERBATIM-END PM1:✱21·54 -/
/- PM-VERBATIM-BEGIN PM1:✱21·55
✱21·55. ⊢ . ẑxẑyφ(x,y) = (℩R){xRy .≡₍x,y₎. φ(x,y)}
PM-VERBATIM-END PM1:✱21·55 -/
/- PM-VERBATIM-BEGIN PM1:✱21·56
✱21·56. ⊢ . E!(℩R){xRy .≡₍x,y₎. φ(x,y)}
PM-VERBATIM-END PM1:✱21·56 -/
/- PM-VERBATIM-BEGIN PM1:✱21·57
✱21·57. ⊢ : ẑxẑyφ(x,y) = (℩R)(fR) .⊃ : g{ẑxẑyφ(x,y)} .≡ . g{(℩R)(fR)}
PM-VERBATIM-END PM1:✱21·57 -/
