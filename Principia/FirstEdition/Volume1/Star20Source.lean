/- PM-VERBATIM-BEGIN PM1:✱20·07
✱20·07. (α). fα .= . (φ). f{ẑ(φ!z)}  Df
PM-VERBATIM-END PM1:✱20·07 -/
/- PM-VERBATIM-BEGIN PM1:✱20·071
✱20·071. (∃α). fα .= . (∃φ). f{ẑ(φ!z)}  Df
PM-VERBATIM-END PM1:✱20·071 -/
/- PM-VERBATIM-BEGIN PM1:✱20·072
✱20·072. [(ια)(φα)] . f(ια)(φα) .=: (∃γ) : φα .≡ₐ. α = γ : fγ  Df
PM-VERBATIM-END PM1:✱20·072 -/
/- PM-VERBATIM-BEGIN PM1:✱20·08
✱20·08. f{α(ψα)} .=: (∃φ) : ψα .≡ₐ. φ!α : f{φ!α}  Df
PM-VERBATIM-END PM1:✱20·08 -/
/- PM-VERBATIM-BEGIN PM1:✱20·081
✱20·081. α ε ψ!â .= . ψ!α  Df
PM-VERBATIM-END PM1:✱20·081 -/
/- PM-VERBATIM-BEGIN PM1:✱20·04
x, y ∈ α .= . x ∈ α . y ∈ α
PM-VERBATIM-END PM1:✱20·04 -/
/- PM-VERBATIM-BEGIN PM1:✱20·05
x, y, z ∈ α .= . x, y ∈ α . z ∈ α
PM-VERBATIM-END PM1:✱20·05 -/
/- PM-VERBATIM-BEGIN PM1:✱20·06
x ∼∈ α .= . ∼(x ∈ α)
PM-VERBATIM-END PM1:✱20·06 -/
/- PM-VERBATIM-BEGIN PM1:✱20·1
⊢ : f{ẑ(ψz)} .≡ : (∃φ) : φ!x .≡ₓ. ψx : f{φ!ẑ}
PM-VERBATIM-END PM1:✱20·1 -/
/- PM-VERBATIM-BEGIN PM1:✱20·11
⊢ : ψx .≡ₓ. χx : ⊃ : f{ẑ(ψz)} .≡ . f{ẑ(χz)}
PM-VERBATIM-END PM1:✱20·11 -/
/- PM-VERBATIM-BEGIN PM1:✱20·111
⊢ : f(φ!ẑ) .≡_φ. g(φ!ẑ) : ⊃ : f{ẑ(φ!z)} .≡_φ. g{ẑ(φ!z)}
PM-VERBATIM-END PM1:✱20·111 -/
/- PM-VERBATIM-BEGIN PM1:✱20·112
⊢ : (∃g) : f{ẑ(φ!z)} .≡_φ. g!{ẑ(φ!z)}
PM-VERBATIM-END PM1:✱20·112 -/
/- PM-VERBATIM-BEGIN PM1:✱20·12
✱20·12. ⊢ : (∃φ) : φ!x .≡ₓ. ψx : f{ẑ(ψz)} .≡ . f{ẑ(φ!z)}  [✱20·11.*12·1]
PM-VERBATIM-END PM1:✱20·12 -/
/- PM-VERBATIM-BEGIN PM1:✱20·13
✱20·13. ⊢ : ψx .≡ₓ. χx .⊃ . ẑ(ψz) = ẑ(χz)
Dem.
⊢.✱20·1. ⊃⊢:: ẑ(ψ z)=ẑ(χ z).≡:. (∃ φ):ψ x.≡ₓ.φ!x:φ!ẑ=ẑ(χ z):.
[✱20·1] ≡:. (∃ φ,θ):. ψ x.≡ₓ.φ!x:χ x.≡ₓ.θ!x:φ!ẑ=θ!ẑ (1)
⊢.✱12·1.✱10·321. ⊃
⊢:: Hp.⊃:. (∃ φ):ψ x.≡ₓ.φ!x:χ x.≡ₓ.φ!x:.
[✱13·195] ⊃:. (∃ φ,θ):. ψ x.≡ₓ.φ!x:χ x.≡ₓ.θ!x:φ!ẑ=θ!ẑ (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·13 -/
/- PM-VERBATIM-BEGIN PM1:✱20·14
✱20·14. ⊢ : ẑ(ψz) = ẑ(χz) .⊃ : ψx .≡ₓ. χx
Dem.
⊢.✱20·1. ⊃⊢:: ẑ(ψ z)=ẑ(χ z).≡:. (∃ φ):ψ x.≡ₓ.φ!x:φ!ẑ=ẑ(χ z):.
[✱20·1] ≡:. (∃ φ,θ):. ψ x.≡ₓ.φ!x:χ x.≡ₓ.θ!x:φ!ẑ=θ!ẑ:.
[✱13·195] ≡:. (∃ φ):. ψ x.≡ₓ.φ!x:χ x.≡ₓ.φ!x:.
[✱10·322] ⊃:. ψ x.≡ₓ.χ x:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·14 -/
/- PM-VERBATIM-BEGIN PM1:✱20·15
✱20·15. ⊢ : ψx .≡ₓ. χx : ≡ : ẑ(ψz) = ẑ(χz)  [✱20·13·14]
PM-VERBATIM-END PM1:✱20·15 -/
/- PM-VERBATIM-BEGIN PM1:✱20·151
✱20·151. ⊢ . (∃φ) . ẑ(ψz) = ẑ(φ!z)
Dem.
⊢.✱20·15. ⊃⊢:. ψ x.≡ₓ.φ!x:⊃.ẑ(ψ z)=ẑ(φ!z):.
[✱10·11·28] ⊃⊢:. (∃ φ):ψ x.≡ₓ.φ!x:⊃.(∃ φ).ẑ(ψ z)=ẑ(φ!z) (1)
⊢.(1).✱12·1. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·151 -/
/- PM-VERBATIM-BEGIN PM1:✱20·16
✱20·16. ⊢ : (∃φ) : φ!x .≡ₓ. ψx : f{ẑ(ψz)} .≡ . f{ẑ(φ!z)}  [✱20·12]
PM-VERBATIM-END PM1:✱20·16 -/
/- PM-VERBATIM-BEGIN PM1:✱20·17
✱20·17. ⊢ : (φ). f{ẑ(φ!z)} .⊃ . f{ẑ(ψz)}  [✱20·16.*10·11]
PM-VERBATIM-END PM1:✱20·17 -/
/- PM-VERBATIM-BEGIN PM1:✱20·18
✱20·18. ⊢ : ẑ(φz) = ẑ(ψz) .⊃ : f{ẑ(φz)} .≡ . f{ẑ(ψz)}  [✱20·11·15]
PM-VERBATIM-END PM1:✱20·18 -/
/- PM-VERBATIM-BEGIN PM1:✱20·19
✱20·19. ⊢ : ẑ(ψz) = ẑ(χz) .≡ : (f) : f!ẑ(ψz) .⊃ . f!ẑ(χz)
Dem.
⊢.✱20·18.✱10·11·21. ⊃⊢:. ẑ(ψ z)=ẑ(χ z).⊃:
(f):f!ẑ(ψ z).⊃.f!ẑ(χ z) (1)
⊢.✱20·18·15. ⊃⊢:: φ!x.≡ₓ.ψ x:θ!x.≡ₓ.χ x:f!ẑ(ψ z).⊃.f!ẑ(χ z):⊃:
f!ẑ(φ!z).⊃.f!ẑ(θ!z) (2)
⊢.(2).✱10·11·27·33. ⊃
⊢:: φ!x.≡ₓ.ψ x:θ!x.≡ₓ.χ x:. (f):f!ẑ(ψ z).⊃.f!ẑ(χ z):. ⊃:. (f):f!ẑ(φ!z).⊃.f!ẑ(θ!z):.
[✱20·112.✱10·1] ⊃:. φ!x.≡ₓ.φ!x:⊃:φ!x.≡ₓ.θ!x:.
[✱4·2] ⊃:. φ!x.≡ₓ.θ!x:.
[✱10·301·32.Hp] ⊃:. ψ x.≡ₓ.χ x:.
[✱20·15] ⊃:. ẑ(ψ z)=ẑ(χ z) (3)
⊢.(3).✱10·11·23·35. ⊃
⊢:: (∃ φ,θ):φ!x.≡ₓ.ψ x:θ!x.≡ₓ.χ x:. (f):f!ẑ(ψ z).⊃.f!ẑ(χ z):.
⊃.ẑ(ψ z)=ẑ(χ z) (4)
⊢.(4).✱12·1. ⊃⊢:. (f):f!ẑ(ψ z).⊃.f!ẑ(χ z):⊃.ẑ(ψ z)=ẑ(χ z) (5)
⊢.(1).(5). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·19 -/
/- PM-VERBATIM-BEGIN PM1:✱20·191
✱20·191. ⊢ : ẑ(ψz) = ẑ(χz) .≡ : (f) : f!ẑ(ψz) .≡ . f!ẑ(χz)
PM-VERBATIM-END PM1:✱20·191 -/
/- PM-VERBATIM-BEGIN PM1:✱20·2
⊢ . ẑ(φz) = ẑ(φz)
PM-VERBATIM-END PM1:✱20·2 -/
/- PM-VERBATIM-BEGIN PM1:✱20·21
⊢ : ẑ(φz) = ẑ(ψz) .≡ . ẑ(ψz) = ẑ(φz)
PM-VERBATIM-END PM1:✱20·21 -/
/- PM-VERBATIM-BEGIN PM1:✱20·22
⊢ : ẑ(φz) = ẑ(ψz) . ẑ(ψz) = ẑ(χz) .⊃ . ẑ(φz) = ẑ(χz)
PM-VERBATIM-END PM1:✱20·22 -/
/- PM-VERBATIM-BEGIN PM1:✱20·23
✱20·23. ⊢ : ẑ(φz) = ẑ(ψz) . ẑ(φz) = ẑ(χz) .⊃ . ẑ(ψz) = ẑ(χz)
PM-VERBATIM-END PM1:✱20·23 -/
/- PM-VERBATIM-BEGIN PM1:✱20·24
✱20·24. ⊢ : ẑ(ψz) = ẑ(φz) . ẑ(χz) = ẑ(φz) .⊃ . ẑ(ψz) = ẑ(χz)
PM-VERBATIM-END PM1:✱20·24 -/
/- PM-VERBATIM-BEGIN PM1:✱20·25
✱20·25. ⊢ : α = ẑ(φz) .≡ₐ. α = ẑ(ψz) : ≡ . ẑ(φz) = ẑ(ψz)
Dem.
⊢.✱10·1. ⊃⊢:. α=ẑ(φ z).≡_α.α=ẑ(ψ z):⊃:
ẑ(φ z)=ẑ(φ z).≡.ẑ(φ z)=ẑ(ψ z):
[✱20·2] ⊃:ẑ(φ z)=ẑ(ψ z) (1)
⊢.✱20·22. ⊃⊢:α=ẑ(φ z).ẑ(φ z)=ẑ(ψ z).⊃.α=ẑ(ψ z):
[Exp.Comm] ⊃⊢:. ẑ(φ z)=ẑ(ψ z).⊃:α=ẑ(φ z).⊃.α=ẑ(ψ z) (2)
⊢.✱20·24. ⊃⊢:. ẑ(φ z)=ẑ(ψ z).α=ẑ(ψ z).⊃.α=ẑ(φ z):.
[Exp] ⊃⊢:. ẑ(φ z)=ẑ(ψ z).⊃:α=ẑ(ψ z).⊃.α=ẑ(φ z) (3)
⊢.(2).(3). ⊃⊢:. ẑ(φ z)=ẑ(ψ z).⊃:α=ẑ(φ z).≡.α=ẑ(ψ z):.
[✱10·11·21] ⊃⊢:. ẑ(φ z)=ẑ(ψ z).⊃:α=ẑ(φ z).≡_α.α=ẑ(ψ z) (4)
⊢.(1).(4). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·25 -/
/- PM-VERBATIM-BEGIN PM1:✱20·3
✱20·3. ⊢ : x ε ẑ(ψz) .≡ . ψx
Dem.
⊢.✱20·1.⊃
⊢:: x∈ ẑ(ψ z). ≡:. (∃ φ):. ψ y.≡y.φ!y:x∈ (φ!ẑ):.
[(✱20·02)] ≡:. (∃ φ):. ψ y.≡y.φ!y:φ!x:.
[✱10·43] ≡:. (∃ φ):. ψ y.≡y.φ!y:ψ x:.
[✱10·35] ≡:. (∃ φ):ψ y.≡y.φ!y:. ψ x:.
[✱12·1] ≡:. ψ x:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·3 -/
/- PM-VERBATIM-BEGIN PM1:✱20·31
✱20·31. ⊢ : ẑ(ψz) = ẑ(χz) .≡ : x ε ẑ(ψz) .≡ₓ. x ε ẑ(χz)  [✱20·15·3]
PM-VERBATIM-END PM1:✱20·31 -/
/- PM-VERBATIM-BEGIN PM1:✱20·32
⊢ . x̂{x ∈ ẑ(φz)} = ẑ(φz)
PM-VERBATIM-END PM1:✱20·32 -/
/- PM-VERBATIM-BEGIN PM1:✱20·33
⊢ : α = ẑ(φz) .≡ : x ∈ α .≡ₓ. φx
PM-VERBATIM-END PM1:✱20·33 -/
/- PM-VERBATIM-BEGIN PM1:✱20·34
⊢ : x = y .≡ : x ∈ α .⊃ₐ. y ∈ α
PM-VERBATIM-END PM1:✱20·34 -/
/- PM-VERBATIM-BEGIN PM1:✱20·35
✱20·35. ⊢ : x = y .≡ : x ε α .≡ₐ. y ε α
PM-VERBATIM-END PM1:✱20·35 -/
/- PM-VERBATIM-BEGIN PM1:✱20·4
✱20·4. ⊢ : α ε Cls .≡ . (∃φ) . α = ẑ(φ!z)
PM-VERBATIM-END PM1:✱20·4 -/
/- PM-VERBATIM-BEGIN PM1:✱20·41
✱20·41. ⊢ . ẑ(ψz) ε Cls
PM-VERBATIM-END PM1:✱20·41 -/
/- PM-VERBATIM-BEGIN PM1:✱20·42
✱20·42. ⊢ . ẑ(z ε α) = α
Dem.
⊢.✱20·3.✱10·11. ⊃⊢:x∈ ẑ(ψ z).≡ₓ.ψ x:
[✱20·15] ⊃⊢.x̂{x∈ ẑ(ψ z)}=x̂(ψ x).⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·42 -/
/- PM-VERBATIM-BEGIN PM1:✱20·5
✱20·5. ⊢ : (℩x)(φx) ε ẑ(ψz) .≡ . ψ{(℩x)(φx)}
Dem.
⊢.✱14·1. ⊃⊢:: (℩x)(φ x)∈ ẑ(ψ z). ≡:. (∃ c):φ x.≡ₓ.x=c:c∈ ẑ(ψ z):.
[✱20·3] ≡:. (∃ c):φ x.≡ₓ.x=c:ψ c:.
[✱14·1] ≡:. ψ{(℩x)(φ x)}:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·5 -/
/- PM-VERBATIM-BEGIN PM1:✱20·51
⊢ : (℩x)(φx) = b .≡ : (℩x)(φx) ∈ α .≡ₐ. b ∈ α
PM-VERBATIM-END PM1:✱20·51 -/
/- PM-VERBATIM-BEGIN PM1:✱20·52
⊢ : E!(℩x)(φx) .≡ : (∃b) : (℩x)(φx) ∈ α .≡ₐ. b ∈ α
PM-VERBATIM-END PM1:✱20·52 -/
/- PM-VERBATIM-BEGIN PM1:✱20·53
⊢ : β = α .⊃_β. φβ : ≡ . φα
PM-VERBATIM-END PM1:✱20·53 -/
/- PM-VERBATIM-BEGIN PM1:✱20·54
✱20·54. ⊢ : (∃β) . β = α . φβ .≡ . φα
Dem.
⊢.✱20·18.✱10·11. ⊃⊢:β=α.φβ.⊃_β.φα:
[✱10·23] ⊃⊢:(∃ β).β=α.φβ.⊃.φα (1)
⊢.✱20·2.✱3·2. ⊃⊢:φα.⊃.α=α.φα.
[✱10·24] ⊃.(∃ β).β=α.φβ (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·54 -/
/- PM-VERBATIM-BEGIN PM1:✱20·55
✱20·55. ⊢ . ẑ(φz) = (ια)(x ε α .≡ₓ. φx)
Dem.
⊢.✱20·33. ⊃⊢:. x∈ α.≡ₓ.φ x:≡_α.α=ẑ(φ z):.
[✱20·54] ⊃⊢:. (∃ β):. x∈ α.≡ₓ.φ x:≡_α.α=β:. ẑ(φ z)=β:.
[✱14·1] ⊃⊢.ẑ(φ z)=(℩α)(x∈ α.≡ₓ.φ x).⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·55 -/
/- PM-VERBATIM-BEGIN PM1:✱20·56
✱20·56. ⊢ . E!(ια)(x ε α .≡ₓ. φx)
PM-VERBATIM-END PM1:✱20·56 -/
/- PM-VERBATIM-BEGIN PM1:✱20·57
✱20·57. ⊢ : ẑ(φz) = (ια)(fα) .⊃ : g{ẑ(φz)} .≡ . g{(ια)(fα)}
Dem.
⊢.✱14·1. ⊃⊢:: Hp. ≡:. (∃ β):fα.≡_α.α=β:ẑ(φ z)=β:.
[✱20·54] ≡:. fα.≡_α.α=ẑ(φ z) (1)
⊢.✱14·1. ⊃⊢:. g{(℩α)(fα)}. ≡:(∃ β):fα.≡_α.α=β:gβ (2)
⊢.(1).(2).⊃⊢:: Hp.⊃:. g{(℩α)(fα)}. ≡:(∃ β):α=ẑ(φ z).≡_α.α=β:gβ:
[✱13·183] ≡:(∃ β).ẑ(φ z)=β.gβ:
[✱20·54] ≡:g{ẑ(φ z)}:: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·57 -/
/- PM-VERBATIM-BEGIN PM1:✱20·58
✱20·58. ⊢ . ẑ(φz) = (ια){α = ẑ(φz)}
Dem.
⊢.✱4·2.✱10·11. ⊃⊢:α=ẑ(φ z).≡_α.α=ẑ(φ z):
[✱20·54] ⊃⊢:. (∃ β):. α=ẑ(φ z).≡_α.α=β:ẑ(φ z)=β:.
[✱14·1] ⊃⊢.ẑ(φ z)=(℩α)α=ẑ(φ z).⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·58 -/
/- PM-VERBATIM-BEGIN PM1:✱20·59
✱20·59. ⊢ : ẑ(φz) = (ια)(fα) .≡ . (ια)(fα) = ẑ(φz)
Dem.
⊢.✱20·1.⊃⊢:. ẑ(φ z)=(℩α)(fα) .≡:(∃ ψ):φ x.≡ₓ.ψ!x:ψ!ẑ=(℩α)(fα):
[✱14·13] ≡:(∃ ψ):φ x.≡ₓ.ψ!x:(℩α)(fα)=ψ!ẑ:
[✱20·1] ≡:(℩α)(fα)=ẑ(φ z):. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·59 -/
/- PM-VERBATIM-BEGIN PM1:✱20·6
✱20·6. ⊢ : (∃α) . fα .≡ . ∼{(α) . ∼fα}
Dem.
⊢.✱4·2.(✱20·071).⊃
⊢:(∃ α).fα. ≡.(∃ φ).f{ẑ(φ!z)}.
[(✱10·01)] ≡.∼[(φ).∼f{ẑ(φ!z)}].
[(✱20·07)] ≡.∼{(α).∼fα}:⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·6 -/
/- PM-VERBATIM-BEGIN PM1:✱20·61
✱20·61. ⊢ : (α) . fα .⊃ . fβ
Dem.
⊢.✱10·1.(✱20·07).⊃⊢:(α).fα.⊃.f{ẑ(φ!z)}:⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·61 -/
/- PM-VERBATIM-BEGIN PM1:✱20·01
✱20·01. f{ẑ(ψz)} .=: (∃φ) : φ!x .≡ₓ. ψx : f{φ!ẑ}  Df
PM-VERBATIM-END PM1:✱20·01 -/
/- PM-VERBATIM-BEGIN PM1:✱20·02
✱20·02. x ε (φ!ẑ) .= . φ!x  Df
PM-VERBATIM-END PM1:✱20·02 -/
/- PM-VERBATIM-BEGIN PM1:✱20·03
✱20·03. Cls = ẑ((∃φ). α = ẑ(φ!z))  Df
PM-VERBATIM-END PM1:✱20·03 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱20·15
✱20·15. ⊢ : ψx .≡ₓ. χx : ≡ : ẑ(ψz) = ẑ(χz)
PM-VERBATIM-SUMMARY-END PM1:✱20·15 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱20·31
✱20·31. ⊢ : ẑ(ψz) = ẑ(χz) .≡ : x ε ẑ(ψz) .≡ₓ. x ε ẑ(χz)
PM-VERBATIM-SUMMARY-END PM1:✱20·31 -/
/- PM-VERBATIM-BEGIN PM1:✱20·43
✱20·43. ⊢ : α = β .≡ : x ε α .≡ₓ. x ε β
PM-VERBATIM-END PM1:✱20·43 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱20·18
✱20·18. ⊢ : ẑ(φz) = ẑ(ψz) .⊃ : f{ẑ(φz)} .≡ . f{ẑ(ψz)}
PM-VERBATIM-SUMMARY-END PM1:✱20·18 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱20·3
✱20·3. ⊢ : x ε ẑ(ψz) .≡ . ψx
PM-VERBATIM-SUMMARY-END PM1:✱20·3 -/

/- PM-VERBATIM-BEGIN PM1:✱20·62
✱20·62. When fβ is true, whatever possible argument of the form ẑ(φ!z) β may be, then (α). fα is true.
Dem.
⊢.✱10·11.⊃. when f{ẑ(φ!z)}
is true, whatever possible argument φ may be, then
( φ).f{ẑ(φ!z)} is true, i.e. (by ✱20·07),
( α).fα is true.
PM-VERBATIM-END PM1:✱20·62 -/

/- PM-VERBATIM-BEGIN PM1:✱20·63
✱20·63. ⊢ : (α). p ∨ fα .⊃ : p .∨ . (α). fα  [analogue of ✱10·12]
Dem.
⊢.✱4·2.(✱20·07).⊃
⊢:. (α).p.∨ fα. ≡ :(φ).p∨ f{ẑ(φ!z)}:
[✱10·12] ≡ :p.∨ .(φ).f{ẑ(φ!z)}:
[(✱20·07)] ≡ :p.∨ .(α).fα:. ⊃ ⊢.Prop
PM-VERBATIM-END PM1:✱20·63 -/

/- PM-VERBATIM-BEGIN PM1:✱20·631
✱20·631. If "fα" is significant, then if β is of the same type as α, "fβ" is significant, and vice versa.
Dem.
By ✱20·151, α is of the form ẑ(φ!z) , and
therefore, by ✱20·01, fα is a function of φ!ẑ .
Similarly β is of the form ẑ(ψ!z) , and fβ
is a function of ψ!ẑ . Hence by applying ✱10·121 to
φ!ẑ and ψ!ẑ the result follows.
PM-VERBATIM-END PM1:✱20·631 -/

/- PM-VERBATIM-BEGIN PM1:✱20·632
✱20·632. If, for some α, there is a proposition fα, then there is a function fα̂, and vice versa.
Dem.
By the definition in ✱20·01, f{ẑ(ψ!z)} is a function of
ψ!ẑ . Hence the proposition follows from ✱10·122.
PM-VERBATIM-END PM1:✱20·632 -/

/- PM-VERBATIM-BEGIN PM1:✱20·633
✱20·633. "Whatever possible class α may be, f(α,β) is true whatever possible class β may be" implies the corresponding statement with α and β interchanged except in "f(α,β)".
PM-VERBATIM-END PM1:✱20·633 -/

/- PM-VERBATIM-BEGIN PM1:✱20·64
✱20·64. ⊢ : (α). fα : (α). gα .⊃ . fβ . gβ
Dem.
⊢.✱4·2.(✱20·07). ⊃
⊢:. (α).fα:(α).gα: ≡ :(φ).f{ẑ(φ!z)}:(φ).g{ẑ(φ!z)}:
[✱10·14] ⊃ :f{ẑ(ψ!z)}.g{ẑ(ψ!z)}:. ⊃ ⊢.Prop
PM-VERBATIM-END PM1:✱20·64 -/

/- PM-VERBATIM-BEGIN PM1:✱20·7
✱20·7. ⊢ : (∃g) : fα .≡ₐ. g!α  [✱20·112]
PM-VERBATIM-END PM1:✱20·7 -/

/- PM-VERBATIM-BEGIN PM1:✱20·701
✱20·701. ⊢ : (∃g) : f{ẑ(φ!z), x} .≡_{φ,x}. g!{ẑ(φ!z), x}
[The proof proceeds as in ✱20·112, using ✱12·11 instead of ✱12·1.]
PM-VERBATIM-END PM1:✱20·701 -/

/- PM-VERBATIM-BEGIN PM1:✱20·702
✱20·702. ⊢ : (∃g) : f{x, ẑ(φ!z)} .≡_{φ,x}. g!{x, ẑ(φ!z)}
[Proof as in ✱20·701.]
PM-VERBATIM-END PM1:✱20·702 -/

/- PM-VERBATIM-BEGIN PM1:✱20·703
✱20·703. ⊢ : (∃g) : f{ẑ(φ!z), ẑ(ψ!z)} .≡_{φ,ψ}. g!{ẑ(φ!z), ẑ(ψ!z)}
Dem.
⊢.✱10·311. ⊃⊢:. f{χ!ẑ,θ!ẑ}.≡_χ,θ.g!{χ!ẑ,θ!ẑ}:⊃:
φ!x≡ₓχ!x.ψ!x≡ₓθ!x.f{χ!ẑ,θ!ẑ}.≡_χ,θ.
φ!x≡ₓχ!x.ψ!x≡ₓθ!x.g!{χ!ẑ,θ!ẑ} (1)
⊢.(1).✱11·11·3·341. ⊃
⊢:. Hp(1). ⊃:(∃ χ,θ).φ!x≡ₓχ!x.ψ!x≡ₓθ!x.f{χ!ẑ,θ!ẑ}.≡_φ,ψ.
(∃ χ,θ).φ!x≡ ₓχ!x.ψ!x≡ ₓθ!x.g!{χ!ẑ,θ!ẑ}:
[✱20·1.✱10·35] ⊃:f{ẑ(φ!z),ẑ(ψ!z)}.≡_φ,ψ.g!{φ!ẑ,ψ!ẑ} (2)
⊢.(2).✱10·11·281. ⊃
⊢:. (∃ g):f{χ!ẑ,θ!ẑ}.≡_χ,θ.g!{χ!ẑ,θ!ẑ}:⊃:
(∃ g):f{ẑ(φ!z),ẑ(ψ!z)}.≡_φ,ψ.g!{ẑ(φ!z),ẑ(ψ!z)} (3)
⊢.(3).✱12·11. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·703 -/

/- PM-VERBATIM-BEGIN PM1:✱20·71
✱20·71. ⊢ : α = β .≡ : g!α .⊃₍g₎. g!β  [✱20·19]
PM-VERBATIM-END PM1:✱20·71 -/

/- PM-VERBATIM-BEGIN PM1:✱20·8
✱20·8. ⊢ : φa ∨ ∼φa .⊃ . ẑ(φx ∨ ∼φx) = ẑ(x = a ∨ x ≠ a)
Dem.
⊢.✱13·3.✱10·11·21.⊃
⊢:: Hp.⊃:. φ x ∨ ∼ φ x.≡ₓ:x=a.∨.x ≠ a:.
[✱20·15]⊃:. x̂(φ x ∨ ∼ φ x)=x̂(x=a.∨.x ≠ a):: ⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·8 -/

/- PM-VERBATIM-BEGIN PM1:✱20·81
✱20·81. ⊢ : φa ∨ ∼φa . ψa ∨ ∼ψa .⊃ . ẑ(φx ∨ ∼φx) = ẑ(ψx ∨ ∼ψx)
Dem.
⊢.✱20·8.⊃⊢:Hp.⊃.x̂(φ x ∨ ∼ φ x)=x̂(x=a.∨.x ≠ a) (1)
⊢.✱20·8.⊃⊢:Hp.⊃.x̂(ψ x ∨ ∼ ψ x)=x̂(x=a.∨.x ≠ a) (2)
⊢.(1).(2).✱10·121·13.Comp.⊃
⊢:Hp.⊃.x̂(φ x ∨ ∼ φ x)=x̂(x=a.∨.x ≠ a).x̂(ψ x ∨ ∼ ψ x)=x̂(x=a.∨.x ≠ a).
[✱20·24]⊃.x̂(φ x ∨ ∼ φ x)=x̂(ψ x ∨ ∼ ψ x):⊃⊢.Prop
PM-VERBATIM-END PM1:✱20·81 -/
