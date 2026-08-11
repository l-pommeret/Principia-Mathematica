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
