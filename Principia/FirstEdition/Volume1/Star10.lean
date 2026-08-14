/- Diplomatic source record for PM I, ✱10. Lean integration is architecture-blocked. -/
/- PM-VERBATIM-BEGIN PM1:✱10·01
✱10·01.  (∃x).φx .=. ∼(x).∼φx  Df
PM-VERBATIM-END PM1:✱10·01 -/
/- PM-VERBATIM-BEGIN PM1:✱10·02
✱10·02.  φx ⊃ₓ ψx .=. (x).φx ⊃ ψx  Df
PM-VERBATIM-END PM1:✱10·02 -/
/- PM-VERBATIM-BEGIN PM1:✱10·03
✱10·03.  φx ≡ₓ ψx .=. (x).φx ≡ ψx  Df
PM-VERBATIM-END PM1:✱10·03 -/
/- PM-VERBATIM-BEGIN PM1:✱10·1
✱10·1.  ⊢ : (x).φx .⊃ .φy
PM-VERBATIM-END PM1:✱10·1 -/
/- PM-VERBATIM-BEGIN PM1:✱10·11
✱10·11.  If φy is true whatever possible argument y may be, then (x).φx is true.
PM-VERBATIM-END PM1:✱10·11 -/
/- PM-VERBATIM-BEGIN PM1:✱10·27
✱10·27.  ⊢ : .(z).φz ⊃ ψz .⊃ : (z).φz .⊃ .(z).ψz
Dem.
⊢.✱10·14. ⊃⊢:. (z).φ z⊃ψ z:(z).φ z:⊃.φ y⊃ψ y.φ y.
[Ass] ⊃.ψ y:.
[✱10·1] ⊃⊢:. (y):. (z).φ z⊃ψ z:(z).φ z:⊃.ψ y:.
[✱10·21] ⊃⊢:. (z).φ z⊃ψ z:(z).φ z:⊃.(y).ψ y (1)
⊢.(1).Exp.⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·27 -/
/- PM-VERBATIM-BEGIN PM1:✱10·271
✱10·271.  ⊢ : .(z).φz ≡ ψz .⊃ : (z).φz .≡.(z).ψz
Dem.
⊢.✱10·22. ⊃⊢:. Hp.⊃:(z).φ z⊃ψ z:
[✱10·27] ⊃:(z).φ z.⊃.(z).ψ z (1)
⊢.✱10·22. ⊃⊢:. Hp.⊃:(z).ψ z⊃φ z:
[✱10·27] ⊃:(z).ψ z.⊃.(z).φ z (2)
⊢.(1).(2).Comp. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·271 -/
/- PM-VERBATIM-BEGIN PM1:✱10·28
✱10·28.  ⊢ : .(x).φx ⊃ ψx .⊃ : (∃x).φx .⊃ .(∃x).ψx
Dem.
⊢.✱10·1. ⊃⊢:. (x).φ x⊃ψ x.⊃.φ y⊃ψ y.
[Transp] ⊃.∼ψ y⊃∼φ y:.
[✱10·11·21] ⊃⊢:. (x).φ x⊃ψ x.⊃:(y).∼ψ y⊃∼φ y:
[✱10·27] ⊃:(y).∼ψ y.⊃.(y).∼φ y:
[Transp] ⊃:(∃ y).φ y.⊃.(∃ y).ψ y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·28 -/
/- PM-VERBATIM-BEGIN PM1:✱10·281
✱10·281.  ⊢ : .(x).φx ≡ ψx .⊃ : (∃x).φx .≡.(∃x).ψx
PM-VERBATIM-END PM1:✱10·281 -/
/- PM-VERBATIM-BEGIN PM1:✱10·35
✱10·35.  ⊢ : .(∃x).p .φx .≡ : p : (∃x).φx
Dem.
⊢.✱3·26. ⊃⊢:p.φ x.⊃.p:
[✱10·11] ⊃⊢:(x):p.φ x.⊃.p:
[✱10·23] ⊃⊢:(∃ x).p.φ x.⊃.p (1)
⊢.✱3·27. ⊃⊢:p.φ x.⊃.φ x:
[✱10·11] ⊃⊢:(x):p.φ x.⊃.φ x:
[✱10·28] ⊃⊢:(∃ x).p.φ x.⊃.(∃ x).φ x (2)
⊢.✱3·2. ⊃⊢:. p.⊃:φ x.⊃.p.φ x.
[✱10·11·21] ⊃⊢:. p. ⊃:(x):φ x.⊃.p.φ x:
[✱10·28] ⊃:(∃ x).φ x.⊃.(∃ x).p.φ x (3)
⊢.(1).(2).(3).Imp.⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·35 -/
/- PM-VERBATIM-BEGIN PM1:✱10·12
✱10·12.  ⊢ : .(x).p ∨ φx .⊃ : p .∨ .(x).φx  [✱9·25]
PM-VERBATIM-END PM1:✱10·12 -/
/- PM-VERBATIM-BEGIN PM1:✱10·121
✱10·121.  If “φx” is significant, then if a is of the same type as x, “φa” is
significant, and vice versa.  [✱9·14]
PM-VERBATIM-END PM1:✱10·121 -/
/- PM-VERBATIM-BEGIN PM1:✱10·122
✱10·122.  If, for some a, there is a proposition φa, then there is a function
φx̂, and vice versa.  [✱9·15]
PM-VERBATIM-END PM1:✱10·122 -/
/- PM-VERBATIM-BEGIN PM1:✱10·13
✱10·13.  If φx̂ and ψx̂ take arguments of the same type, and we have “⊢.φx”
and “⊢.ψx,” we shall have “⊢.φx.ψx.”
Dem.  By repeated use of 9·61·62·63·131 (3), there is a function ∼φx̂∨∼ψx̂.
Hence by ✱2·11 and ✱3·01,
⊢ : ∼φx∨∼ψx .∨ .φx .ψx  (1)
⊢ . (1) . ✱2·32 . (✱1·01) . ⊃ ⊢ : .φx .⊃ : ψx .⊃ .φx .ψx  (2)
⊢ . (2) . ✱9·12 . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱10·13 -/
/- PM-VERBATIM-BEGIN PM1:✱10·14
✱10·14.  ⊢ : .(x).φx : (x).ψx : ⊃ .φy .ψy
Dem.
⊢.✱10·1. ⊃⊢:(x).φ x.⊃.φ y (1)
⊢.✱10·1. ⊃⊢:(x).ψ x.⊃.ψ y (2)
⊢.(1).(2).✱10·13. ⊃⊢:(x).φ x.⊃.φ y:(x).ψ x.⊃.ψ y:
[✱3·47] ⊃⊢:. (x).φ x:(x).ψ x:⊃.φ y.ψ y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·14 -/
/- PM-VERBATIM-BEGIN PM1:✱10·2
✱10·2.  ⊢ : .(x).p∨φx .≡ : p .∨ .(x).φx
Dem.
⊢.✱10·1.✱1·6. ⊃⊢:. p.∨ .(x).φ x:⊃.p∨ φ y:.
[✱10·11] ⊃⊢:. (y):. p.∨ .(x).φ x:⊃.p∨ φ y:.
[✱10·12] ⊃⊢:. p.∨ .(x).φ x:⊃.(y).p∨ φ y (1)
⊢.✱10·12. ⊃⊢:. (y).p∨ φ y.⊃:p.∨ .(x).φ x (2)
⊢.(1).(2). ⊃⊢.Prop.
PM-VERBATIM-END PM1:✱10·2 -/
/- PM-VERBATIM-BEGIN PM1:✱10·21
✱10·21.  ⊢ : .(x).p⊃φx .≡ : p .⊃ .(x).φx  [✱10·2  ∼p/p]
PM-VERBATIM-END PM1:✱10·21 -/
/- PM-VERBATIM-BEGIN PM1:✱10·22
✱10·22.  ⊢ : .(x).φx .ψx .≡ : (x).φx : (x).ψx
Dem.
⊢.✱10·1. ⊃⊢:(x).φ x.ψ x.⊃.φ y.ψ y. (1)
[✱3·26] ⊃.φ y:
[✱10·11] ⊃⊢:. (y):(x).φ x.ψ x.⊃.φ y:.
[✱10·21] ⊃⊢:. (x).φ x.ψ x.⊃.(y).φ y (2)
⊢.(1).✱3·27. ⊃⊢:. (x).φ x.ψ x.⊃.ψ z:.
[✱10·11] ⊃⊢:. (z):(x).φ x.ψ x.⊃.ψ z:.
[✱10·21] ⊃⊢:. (x).φ x.ψ x.⊃.(z).ψ z (3)
⊢.(2).(3).Comp. ⊃⊢:. (x).φ x.ψ x.⊃:(y).φ y:(z).ψ z (4)
⊢.✱10·14·11. ⊃⊢:. (y):. (x).φ x:(x).ψ x:⊃.φ y.ψ y:.
[✱10·21] ⊃⊢:. (x).φ x:(x).ψ x:⊃.(y).φ y.ψ y (5)
⊢.(4).(5). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·22 -/
/- PM-VERBATIM-BEGIN PM1:✱10·221
✱10·221.  If φx contains a constituent χ(x, y, z, ...) and ψx contains a
constituent χ(x, u, v, ...), where χ is an elementary function and y, z, ...,
u, v, ... are either constants or apparent variables, then φx̂ and ψx̂ take
arguments of the same type.
PM-VERBATIM-END PM1:✱10·221 -/
/- PM-VERBATIM-BEGIN PM1:✱10·23
✱10·23.  ⊢ : .(x).φx⊃p .≡ : (∃x).φx .⊃ .p
Dem.
⊢.✱4·2.(✱9·03).⊃⊢:. (x).∼φ x ∨ p. ≡:(x).∼φ x. ∨ .p:
[(✱9·02)] ≡.(∃ x).φ x.⊃.p (1)
⊢.(1).(✱1·01).⊃⊢.Prop
Dem.
⊢.Transp.(✱10·01). ⊃⊢:. (∃ x).φ x.⊃.p:≡:∼p.⊃.(x).∼φ x:
[✱10·21] ≡:(x):∼p.⊃.∼φ x: (1)
[✱10·1] ⊃:∼p.⊃.∼φ x
[Transp] ⊃:φ x.⊃.p:.
[✱10·11] ⊃⊢:. (x):. (∃ x).φ x.⊃.p:⊃:φ x.⊃.p:.
[✱10·21] ⊃⊢:. (∃ x).φ x.⊃.p:⊃:(x):φ x.⊃.p (2)
⊢.✱10·1. ⊃⊢:. (x):φ x.⊃.p:⊃:φ x⊃ p:
[Transp] ⊃:∼p.⊃.∼φ x:.
[✱10·11·21] ⊃⊢:. (x):φ x.⊃.p:⊃:(x):∼p.⊃.∼φ x:
[(1)] ⊃ :(∃ x).φ x.⊃.p (3)
⊢.(2).(3). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·23 -/
/- PM-VERBATIM-BEGIN PM1:✱10·24
✱10·24.  ⊢ : φy .⊃ .(∃x).φx
Dem.
⊢.✱10·1. ⊃⊢:(x).∼φ x.⊃.∼φ y:
[Transp] ⊃⊢:φ y.⊃.∼(x).∼φ x:
[(✱10·01)] ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·24 -/
/- PM-VERBATIM-BEGIN PM1:✱10·25
✱10·25.  ⊢ : (x).φx .⊃ .(∃x).φx  [✱10·1·24]
PM-VERBATIM-END PM1:✱10·25 -/
/- PM-VERBATIM-BEGIN PM1:✱10·26
✱10·26. ⊢:. (z).φ z⊃ψ z:φ x:⊃.ψ x [*10·1. Imp]
PM-VERBATIM-END PM1:✱10·26 -/
/- PM-VERBATIM-BEGIN PM1:✱10·251
✱10·251.  ⊢ : (x).∼φx .⊃ .∼{(x).φx}  [✱10·25 . Transp]
PM-VERBATIM-END PM1:✱10·251 -/
/- PM-VERBATIM-BEGIN PM1:✱10·252
✱10·252.  ⊢ : ∼{(∃x).φx} .≡ .(x).∼φx  [✱4·2 . (✱9·02)]
Alternative method: [✱4·13 . (✱10·01)].
PM-VERBATIM-END PM1:✱10·252 -/
/- PM-VERBATIM-BEGIN PM1:✱10·253
✱10·253.  ⊢ : ∼{(x).φx} .≡ .(∃x).∼φx  [✱4·2 . (✱9·01)]
Dem.
⊢.✱10·1. ⊃⊢:(x).φ x.⊃.φ y.
[✱2·12] ⊃.∼(∼φ y):
[✱10·11·21] ⊃⊢:(x).φ x.⊃.(y).∼(∼φ y):
[Transp] ⊃⊢:∼{(y).∼(∼φ y)}.⊃.∼{(x).φ x}:
[(✱10·01)] ⊃⊢:(∃ y).∼φ y. ⊃.∼{(x).φ x} (1)
⊢.✱10·1. ⊃⊢:(y).∼(∼φ y). ⊃.∼(∼φ x).
[✱2·14] ⊃.φ x:
[✱10·11·21] ⊃⊢:(y).∼(∼φ y). ⊃.(x).φ x:
[Transp] ⊃⊢:∼{(x).φ x}. ⊃.∼{(y).∼(∼φ y)}.
[(✱10·01)] ⊃.(∃ y).∼φ y (2)
⊢.(1).(2) ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·253 -/
/- PM-VERBATIM-BEGIN PM1:✱10·29
✱10·29.  ⊢ : .(x).φx⊃ψx : (x).φx⊃χx : ⊃ .(x).φx⊃χx
Dem.
⊢.✱10·22. ⊃⊢:. (x).φ x⊃ψ x:(x).φ x⊃χ x:
≡:(x):φ x⊃ψ x.φ x⊃χ x (1)
⊢.✱4·76. ⊃⊢:. φ x⊃ψ x.φ x⊃χ x.≡:φ x.⊃.ψ x.χ x:.
[✱10·11] ⊃⊢:. (x):. φ x⊃ψ x.φ x⊃χ x.≡:φ x.⊃.ψ x.χ x:.
[✱10·271] ⊃⊢:. (x):φ x⊃ψ x.φ x⊃χ x:≡:(x):φ x.⊃.ψ x.χ x (2)
⊢.(1).(2). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·29 -/
/- PM-VERBATIM-BEGIN PM1:✱10·3
✱10·3.  ⊢ : .(x).φx⊃ψx : (x).ψx⊃χx : ⊃ .(x).φx⊃χx
Dem. ⊢.✱10·22·221.⊃⊢:Hp. ⊃.(x).φ x⊃ψ x.ψ x⊃χ x.
[Syll.✱10·27] ⊃.(x).φ x⊃χ x:⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·3 -/
/- PM-VERBATIM-BEGIN PM1:✱10·301
✱10·301.  ⊢ : .(x).φx≡ψx : (x).ψx≡χx : ⊃ .(x).φx≡χx
Dem.
⊢.✱10·22·221.⊃⊢:. Hp. ⊃:(x).φ x≡ψ x.ψ x≡χ x:
[✱4·22.✱10·27] ⊃:(x).φ x≡χ x:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·301 -/
/- PM-VERBATIM-BEGIN PM1:✱10·31
✱10·31.  ⊢ : .(x).φx⊃ψx .⊃ : (x) : φx .χx .⊃ .ψx .χx
Dem.
⊢.Fact.✱10·11. ⊃⊢:. (x):. φ x⊃ψ x.⊃:φ x.χ x.⊃.ψ x.χ x (1)
⊢.(1).✱10·27. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·31 -/
/- PM-VERBATIM-BEGIN PM1:✱10·311
✱10·311.  ⊢ : .(x).φx≡ψx .⊃ : (x) : φx .χx .≡ .ψx .χx
Dem.
⊢.✱4·36.✱10·11. ⊃⊢:. (x):. φ x≡ψ x.⊃:φ x.χ x.≡.ψ x.χ x (1)
⊢.(1).✱10·27. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·311 -/
/- PM-VERBATIM-BEGIN PM1:✱10·32
✱10·32. ⊢:φ x≡ₓψ x.≡.ψ x≡ₓφ x
PM-VERBATIM-END PM1:✱10·32 -/
/- PM-VERBATIM-BEGIN PM1:✱10·321
✱10·321. ⊢:φ x≡ₓψ x.φ x≡ₓχ x.⊃.ψ x≡ₓχ x
PM-VERBATIM-END PM1:✱10·321 -/
/- PM-VERBATIM-BEGIN PM1:✱10·322
✱10·322. ⊢:ψ x≡ₓφ x.χ x≡ₓφ x.⊃.ψ x≡ₓχ x
PM-VERBATIM-END PM1:✱10·322 -/
/- PM-VERBATIM-BEGIN PM1:✱10·33
✱10·33.  ⊢ : .(x) : φx .p .≡ : (x).φx : p
Dem.
⊢.✱10·1. ⊃⊢:. (x):φ x.p:⊃.φ y.p. (1)
[✱3·27] ⊃.p (2)
⊢.(1).✱3·26. ⊃⊢:. (x):φ x.p:⊃.φ y:
[✱10·11·21] ⊃⊢:. (x):φ x.p:⊃.(y).φ y (3)
⊢.(2).(3). ⊃⊢:. (x):φ x.p:⊃:(y).φ y:p (4)
⊢.✱10·1. ⊃⊢:. (y).φ y. ⊃.φ x:.
[Fact] ⊃⊢:. (y).φ y:p:⊃.φ x.p:.
[✱10·11·21] ⊃⊢:. (y).φ y:p:⊃:(x):φ x.p (5)
⊢.(4).(5). ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·33 -/
/- PM-VERBATIM-BEGIN PM1:✱10·34
✱10·34.  ⊢ : .(∃x).φx⊃p .≡ : (x).φx .⊃ .p
Dem.
⊢.✱4·2.(✱10·01).⊃
⊢:. (∃ x).φ x⊃ p. ≡:∼{(x).∼(φ x⊃ p)}:
[✱4·61.✱10·271] ≡:∼{(x):φ x.∼p}:
[✱10·33] ≡:∼{(x).φ x:∼p}:
[✱4·53] ≡:∼{(x).φ x}.∨ .p:
[✱4·6] ≡:(x).φ x.⊃.p
PM-VERBATIM-END PM1:✱10·34 -/
/- PM-VERBATIM-BEGIN PM1:✱10·36
✱10·36.  ⊢ : .(∃x).φx∨p .≡ : (∃x).φx .∨ .p
Dem.
⊢.✱4·64 ⊃⊢:φ x∨ p.≡.∼φ x⊃ p:
[✱10·11] ⊃⊢:(x):φ x∨ p.≡.∼φ x⊃ p:
[✱10·281] ⊃⊢:. (∃ x).φ x∨ p. ≡:(∃ x).∼φ x⊃ p:
[✱10·34] ≡:(x).∼φ x.⊃.p:
[✱4·6.(✱10·01)] ≡:(∃ x).φ x.∨ .p:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·36 -/
/- PM-VERBATIM-BEGIN PM1:✱10·37
✱10·37.  ⊢ : .(∃x).p⊃φx .≡ : p .⊃ .(∃x).φx  [✱10·36  ∼p/p]
PM-VERBATIM-END PM1:✱10·37 -/
/- PM-VERBATIM-BEGIN PM1:✱10·39
✱10·39.  ⊢ : φx⊃ₓχx .ψx⊃ₓθx .⊃ : φx .ψx .⊃ₓ .χx .θx
Dem.
⊢.✱10·22. ⊃⊢:. Hp.⊃:(x):φ x⊃χ x.ψ x⊃θ x:
[✱3·47.✱10·27] ⊃:(x):φ x.ψ x.⊃.χ x.θ x:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·39 -/
/- PM-VERBATIM-BEGIN PM1:✱10·4
✱10·4.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx .ψx .≡ₓ .χx .θx
Dem.
⊢.✱10·22. ⊃⊢:. Hp.⊃:φ x⊃ₓχ x.ψ x⊃ₓθ x:
[✱10·39] ⊃:φ x.ψ x.⊃ₓ.χ x.θ x (1)
Similarly ⊢:. Hp.⊃:χ x.θ x.⊃ₓ.φ x.ψ x (2)
⊢.(1).(2).Comp. ⊃⊢:. Hp.⊃:φ x.ψ x.⊃ₓ.χ x.θ x:χ x.θ x.⊃ₓ.φ x.ψ x:
[✱10·22] ⊃:φ x.ψ x.≡ₓ.χ x.θ x:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·4 -/
/- PM-VERBATIM-BEGIN PM1:✱10·41
✱10·41.  ⊢ : .(x).φx .∨ .(x).ψx .⊃ .(x).φx∨ψx
Dem.
⊢.✱10·1. ⊃⊢:(x).φ x.⊃.φ y.
[✱2·2] ⊃.φ y∨ ψ y (1)
⊢.✱10·1. ⊃⊢:(x).ψ x.⊃.ψ y.
[✱1·3] ⊃.φ y∨ ψ y (2)
⊢.(1).(2).✱10·13. ⊃⊢:. (x).φ x.⊃.φ y∨ ψ y:(x).ψ x.⊃.φ y∨ ψ y:.
[✱3·44] ⊃⊢:. (x).φ x.∨ .(x).ψ x:⊃.φ y∨ ψ y
[✱10·11·21] ⊃⊢:. (x).φ x.∨ .(x).ψ x:⊃.(y).φ y∨ ψ y:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·41 -/
/- PM-VERBATIM-BEGIN PM1:✱10·411
✱10·411.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx∨ψx .≡ₓ .χx∨θx
Dem.
⊢.✱10·14. ⊃⊢:. Hp. ⊃:φ x≡χ x.ψ x≡θ x:
[✱4·39] ⊃:φ x∨ ψ x.≡.χ x∨ θ x (1)
⊢.(1).✱10·11·21.⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·411 -/
/- PM-VERBATIM-BEGIN PM1:✱10·412
✱10·412.  ⊢ : φx≡ₓψx .≡ .∼φx≡ₓ∼ψx  [✱4·11 . ✱10·11·271]
PM-VERBATIM-END PM1:✱10·412 -/
/- PM-VERBATIM-BEGIN PM1:✱10·413
✱10·413.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx⊃ψx .≡ₓ .χx⊃θx
Dem.
⊢.✱10·411·412.⊃⊢:. Hp. ⊃:∼φ x∨ ψ x.≡ₓ.∼χ x∨ θ x
[(✱1·01)] ⊃:φ x⊃ψ x.≡ₓ.χ x⊃θ x:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·413 -/
/- PM-VERBATIM-BEGIN PM1:✱10·414
✱10·414.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx≡ψx .≡ₓ .χx≡θx
Dem.
⊢.✱10·413 ψ, φ, θ, χ/φ, ψ, χ, θ.✱10·32. ⊃⊢:. Hp.⊃:ψ x⊃φ x.≡ₓ.θ x⊃χ x (1)
⊢.✱10·413.(1).✱10·4. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·414 -/
/- PM-VERBATIM-BEGIN PM1:✱10·42
✱10·42.  ⊢ : .(∃x).φx .∨ .(∃x).ψx .≡ .(∃x).φx∨ψx
Dem.
⊢.✱10·22. ⊃⊢:. (x).∼φ x:(x).∼ψ x:≡.(x).∼φ x.∼ψ x:.
[✱4·11] ⊃⊢:. ∼{(x).∼φ x:(x).∼ψ x}.≡.∼{(x).∼φ x.∼ψ x}:.
[✱4·51·56.✱10·271] ⊃⊢:. ∼{(x).∼φ x}.∨ .∼{(x).∼ψ x}:
≡.∼{(x).∼(φ x∨ ψ x)}:.
[✱10·253] ⊃⊢:. (∃ x).φ x.∨ .(∃ x).ψ x:≡.(∃ x).φ x∨ ψ x:. ⊃⊢.Prop
PM-VERBATIM-END PM1:✱10·42 -/
/- PM-VERBATIM-BEGIN PM1:✱10·43
✱10·43.  ⊢ : φx≡ₓψz .φx .≡ .φz≡ₓψz
Dem.
⊢ .✱10·1. ⊃ ⊢ : φ z ≡z ψ z . ⊃ . φ x ≡ ψ x (1)
⊢ .(1) . ✱5·32. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱10·43 -/
/- PM-VERBATIM-BEGIN PM1:✱10·5
✱10·5.  ⊢ : .(∃x).φx .ψx .⊃ : (∃x).φx : (∃x).ψx
Dem.
⊢ .✱3·26 . ✱10·11. ⊃ ⊢ : (x) : φ x . ψ x . ⊃ . φ x:
[✱10·28] ⊃ ⊢ : (∃ x) . φ x . ψ x . ⊃ . (∃ x) . φ x (1)
⊢ .✱3·27 . ✱10·11. ⊃ :. (x) : φ x . ψ x . ⊃ . ψ x :
[✱10·28] ⊃ ⊢ : (∃ x) . φ x . ψ x . ⊃ . (∃ x) . ψ x (2)
⊢ .(1).(2).Comp. ⊃ ⊢ :. Prop
PM-VERBATIM-END PM1:✱10·5 -/
/- PM-VERBATIM-BEGIN PM1:✱10·51
✱10·51.  ⊢ : ∼{(∃x).φx .ψx} .≡ : φx .⊃ₓ .∼ψx
Dem.
⊢ .✱10·252. ⊃ ⊢ :. ∼{(∃ x) . φ x . ψ x} . ≡ : (x) . ∼(φ x . ψ x) :
[✱4·51·62.✱10·271] ≡ : (x) : φ x . ⊃ . ∼ψ x :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱10·51 -/
/- PM-VERBATIM-BEGIN PM1:✱10·52
✱10·52.  ⊢ : .(∃x).φx .⊃ : (x).φx⊃p .⊃ .p
Dem.
⊢ .✱5·5. ⊃ ⊢ :: Hp . ⊃ :. p . ≡ : (∃ x) . φ x . ⊃ . p :
[✱10·23] ≡ : (x) . φ x ⊃ p :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱10·52 -/
/- PM-VERBATIM-BEGIN PM1:✱10·53
✱10·53.  ⊢ : ∼(∃x).φx .⊃ : φx .⊃ₓ .ψx
Dem.
⊢ .✱2·21 . ✱10·11. ⊃
⊢ :. (x) :. ∼φ x . ⊃ : φ x . ⊃ . ψ x :.
[✱10·27] ⊃ ⊢ :. (x) . ∼φ x . ⊃ : (x) : φ x . ⊃ . ψ x :.
[✱10·252] ⊃ ⊢ :. ∼(∃ x) . φ x . ⊃ : (x) : φ x . ⊃ . ψ x :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱10·53 -/
/- PM-VERBATIM-BEGIN PM1:✱10·541
✱10·541.  ⊢ : φy .⊃ᵧ .p∨ψy .≡ : p .∨ .φy⊃ᵧψy
Dem.
⊢ .✱4·2 . (✱1·01). ⊃ ⊢ :. φ y . ⊃y . p ∨ ψ y : ≡ : (y) . ∼φ y ∨ p ∨ ψ y :
[Assoc.✱10·271] ≡ : (y) . p ∨ ∼φ y ∨ ψ y :
[✱10·2] ≡ : p . ∨ . (y) . ∼φ y ∨ ψ y :
[(✱1·01)] ≡ : p . ∨ . φ y ⊃y ψ y :. ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱10·541 -/
/- PM-VERBATIM-BEGIN PM1:✱10·542
✱10·542.  ⊢ : φy .⊃ᵧ .p⊃ψy .≡ : p .⊃ .φy⊃ᵧψy  [✱10·541  ∼p/p]
PM-VERBATIM-END PM1:✱10·542 -/
/- PM-VERBATIM-BEGIN PM1:✱10·55
✱10·55. ⊢:. (∃ x).φ x.ψ x:φ x⊃ₓψ x:≡:(∃ x).φ x:φ x⊃ₓψ x
PM-VERBATIM-END PM1:✱10·55 -/

/- PM-VERBATIM-BEGIN PM1:✱10·56
✱10·56. ⊢:. φ x⊃ₓ.ψ x:(∃ x).φ x.χ x:⊃.(∃ x).ψ x.χ x
PM-VERBATIM-END PM1:✱10·56 -/
/- PM-VERBATIM-BEGIN PM1:✱10·57
✱10·57. ⊢:. φ x.⊃ₓ.ψ x∨ χ x:⊃:φ x⊃ₓψ x.∨ .(∃ x).φ x.χ x
PM-VERBATIM-END PM1:✱10·57 -/
