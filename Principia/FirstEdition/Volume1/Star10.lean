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
PM-VERBATIM-END PM1:✱10·27 -/
/- PM-VERBATIM-BEGIN PM1:✱10·271
✱10·271.  ⊢ : .(z).φz ≡ ψz .⊃ : (z).φz .≡.(z).ψz
PM-VERBATIM-END PM1:✱10·271 -/
/- PM-VERBATIM-BEGIN PM1:✱10·28
✱10·28.  ⊢ : .(x).φx ⊃ ψx .⊃ : (∃x).φx .⊃ .(∃x).ψx
PM-VERBATIM-END PM1:✱10·28 -/
/- PM-VERBATIM-BEGIN PM1:✱10·281
✱10·281.  ⊢ : .(x).φx ≡ ψx .⊃ : (∃x).φx .≡.(∃x).ψx
PM-VERBATIM-END PM1:✱10·281 -/
/- PM-VERBATIM-BEGIN PM1:✱10·35
✱10·35.  ⊢ : .(∃x).p .φx .≡ : p : (∃x).φx
Dem.  By ✱3·26, ✱10·11, ✱10·23, ✱3·27, ✱10·28, ✱3·2, and ✱10·11·21,
⊢ . Prop.
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
Dem.  ⊢ . ✱10·1 . ⊃ ⊢ : (x).φx .⊃ .φy  (1)
⊢ . ✱10·1 . ⊃ ⊢ : (x).ψx .⊃ .ψy  (2)
⊢ . (1) . (2) . ✱10·13 . ⊃ ⊢ : (x).φx : (x).ψx : ⊃ .φy .ψy
PM-VERBATIM-END PM1:✱10·14 -/
/- PM-VERBATIM-BEGIN PM1:✱10·2
✱10·2.  ⊢ : .(x).p∨φx .≡ : p .∨ .(x).φx
Dem.  ⊢ . ✱10·1 . ✱1·6 . ⊃ ⊢ : p .∨ .(x).φx : ⊃ .p∨φy :
[✱10·11] ⊃ ⊢ : (y) : p .∨ .(x).φx : ⊃ .p∨φy :
[✱10·12] ⊃ ⊢ : p .∨ .(x).φx : ⊃ .(y).p∨φy  (1)
⊢ . ✱10·12 . ⊃ ⊢ : (y).p∨φy .⊃ : p .∨ .(x).φx  (2)
⊢ . (1) . (2) . ⊃ ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·2 -/
/- PM-VERBATIM-BEGIN PM1:✱10·21
✱10·21.  ⊢ : .(x).p⊃φx .≡ : p .⊃ .(x).φx  [✱10·2  ∼p/p]
PM-VERBATIM-END PM1:✱10·21 -/
/- PM-VERBATIM-BEGIN PM1:✱10·22
✱10·22.  ⊢ : .(x).φx .ψx .≡ : (x).φx : (x).ψx
Dem.  By ✱10·1, ✱3·26, ✱10·11, ✱10·21, ✱3·27, Comp, and ✱10·14·11,
⊢ . Prop.
PM-VERBATIM-END PM1:✱10·22 -/
/- PM-VERBATIM-BEGIN PM1:✱10·221
✱10·221.  If φx contains a constituent χ(x, y, z, ...) and ψx contains a
constituent χ(x, u, v, ...), where χ is an elementary function and y, z, ...,
u, v, ... are either constants or apparent variables, then φx̂ and ψx̂ take
arguments of the same type.
PM-VERBATIM-END PM1:✱10·221 -/
/- PM-VERBATIM-BEGIN PM1:✱10·23
✱10·23.  ⊢ : .(x).φx⊃p .≡ : (∃x).φx .⊃ .p
Dem.  By ✱4·2, ✱9·03, ✱9·02, and ✱1·01, ⊢ . Prop.
In the alternative method, by Transp, ✱10·01, ✱10·21, ✱10·1,
✱10·11, and ✱10·11·21, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·23 -/
/- PM-VERBATIM-BEGIN PM1:✱10·24
✱10·24.  ⊢ : φy .⊃ .(∃x).φx
Dem.  In the alternative method: ✱10·1, Transp, and ✱10·01, yielding ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·24 -/
/- PM-VERBATIM-BEGIN PM1:✱10·25
✱10·25.  ⊢ : (x).φx .⊃ .(∃x).φx  [✱10·1·24]
PM-VERBATIM-END PM1:✱10·25 -/
/- PM-VERBATIM-BEGIN PM1:✱10·251
✱10·251.  ⊢ : (x).∼φx .⊃ .∼{(x).φx}  [✱10·25 . Transp]
PM-VERBATIM-END PM1:✱10·251 -/
/- PM-VERBATIM-BEGIN PM1:✱10·252
✱10·252.  ⊢ : ∼{(∃x).φx} .≡ .(x).∼φx  [✱4·2 . (✱9·02)]
Alternative method: [✱4·13 . (✱10·01)].
PM-VERBATIM-END PM1:✱10·252 -/
/- PM-VERBATIM-BEGIN PM1:✱10·253
✱10·253.  ⊢ : ∼{(x).φx} .≡ .(∃x).∼φx  [✱4·2 . (✱9·01)]
Alternative method: by ✱10·1, ✱2·12, ✱10·11·21, Transp, ✱2·14, and ✱10·01,
⊢ . Prop.
PM-VERBATIM-END PM1:✱10·253 -/
/- PM-VERBATIM-BEGIN PM1:✱10·29
✱10·29.  ⊢ : .(x).φx⊃ψx : (x).φx⊃χx : ⊃ .(x).φx⊃χx
Dem.  By ✱10·22, ✱4·76, ✱10·11, and ✱10·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·29 -/
/- PM-VERBATIM-BEGIN PM1:✱10·3
✱10·3.  ⊢ : .(x).φx⊃ψx : (x).ψx⊃χx : ⊃ .(x).φx⊃χx
Dem.  By ✱10·22·221, Syll., and ✱10·27, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·3 -/
/- PM-VERBATIM-BEGIN PM1:✱10·301
✱10·301.  ⊢ : .(x).φx≡ψx : (x).ψx≡χx : ⊃ .(x).φx≡χx
Dem.  By ✱10·22·221, ✱4·22, and ✱10·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·301 -/
/- PM-VERBATIM-BEGIN PM1:✱10·31
✱10·31.  ⊢ : .(x).φx⊃ψx .⊃ : (x) : φx .χx .⊃ .ψx .χx
Dem.  By Fact, ✱10·11, and ✱10·27, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·31 -/
/- PM-VERBATIM-BEGIN PM1:✱10·311
✱10·311.  ⊢ : .(x).φx≡ψx .⊃ : (x) : φx .χx .≡ .ψx .χx
Dem.  By ✱4·36, ✱10·11, and ✱10·27, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·311 -/
/- PM-VERBATIM-BEGIN PM1:✱10·33
✱10·33.  ⊢ : .(x) : φx .p .≡ : (x).φx : p
Dem.  By ✱10·1, ✱3·27, ✱3·26, and ✱10·11·21, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·33 -/
/- PM-VERBATIM-BEGIN PM1:✱10·34
✱10·34.  ⊢ : .(∃x).φx⊃p .≡ : (x).φx .⊃ .p
Dem.  By ✱4·2, ✱10·01, ✱4·61, ✱10·271, ✱10·33, ✱4·53, and ✱4·6,
⊢ . Prop.
PM-VERBATIM-END PM1:✱10·34 -/
/- PM-VERBATIM-BEGIN PM1:✱10·36
✱10·36.  ⊢ : .(∃x).φx∨p .≡ : (∃x).φx .∨ .p
Dem.  By ✱4·64, ✱10·11, ✱10·281, ✱10·34, ✱4·6, and ✱10·01,
⊢ . Prop.
PM-VERBATIM-END PM1:✱10·36 -/
/- PM-VERBATIM-BEGIN PM1:✱10·37
✱10·37.  ⊢ : .(∃x).p⊃φx .≡ : p .⊃ .(∃x).φx  [✱10·36  ∼p/p]
PM-VERBATIM-END PM1:✱10·37 -/
/- PM-VERBATIM-BEGIN PM1:✱10·39
✱10·39.  ⊢ : φx⊃ₓχx .ψx⊃ₓθx .⊃ : φx .ψx .⊃ₓ .χx .θx
Dem.  By ✱10·22, ✱3·47, and ✱10·27, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·39 -/
/- PM-VERBATIM-BEGIN PM1:✱10·4
✱10·4.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx .ψx .≡ₓ .χx .θx
Dem.  By ✱10·22, ✱10·39, Comp, and ✱10·22, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·4 -/
/- PM-VERBATIM-BEGIN PM1:✱10·41
✱10·41.  ⊢ : .(x).φx .∨ .(x).ψx .⊃ .(x).φx∨ψx
Dem.  By ✱10·1, ✱2·2, ✱1·3, ✱10·13, ✱3·44, and ✱10·11·21,
⊢ . Prop.
PM-VERBATIM-END PM1:✱10·41 -/
/- PM-VERBATIM-BEGIN PM1:✱10·411
✱10·411.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx∨ψx .≡ₓ .χx∨θx
Dem.  By ✱10·14, ✱4·39, and ✱10·11·21, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·411 -/
/- PM-VERBATIM-BEGIN PM1:✱10·412
✱10·412.  ⊢ : φx≡ₓψx .≡ .∼φx≡ₓ∼ψx  [✱4·11 . ✱10·11·271]
PM-VERBATIM-END PM1:✱10·412 -/
/- PM-VERBATIM-BEGIN PM1:✱10·413
✱10·413.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx⊃ψx .≡ₓ .χx⊃θx
Dem.  By ✱10·411·412 and ✱1·01, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·413 -/
/- PM-VERBATIM-BEGIN PM1:✱10·414
✱10·414.  ⊢ : φx≡ₓχx .ψx≡ₓθx .⊃ : φx≡ψx .≡ₓ .χx≡θx
Dem.  By ✱10·413, permutation, ✱10·32, and ✱10·4, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·414 -/
/- PM-VERBATIM-BEGIN PM1:✱10·42
✱10·42.  ⊢ : .(∃x).φx .∨ .(∃x).ψx .≡ .(∃x).φx∨ψx
Dem.  By ✱10·22, ✱4·11, ✱4·51·56, ✱10·271, and ✱10·253,
⊢ . Prop.
PM-VERBATIM-END PM1:✱10·42 -/
/- PM-VERBATIM-BEGIN PM1:✱10·43
✱10·43.  ⊢ : φx≡ₓψz .φx .≡ .φz≡ₓψz
Dem.  By ✱10·1 and ✱5·32, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·43 -/
/- PM-VERBATIM-BEGIN PM1:✱10·5
✱10·5.  ⊢ : .(∃x).φx .ψx .⊃ : (∃x).φx : (∃x).ψx
Dem.  By ✱3·26, ✱10·11, ✱10·28, ✱3·27, and Comp, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·5 -/
/- PM-VERBATIM-BEGIN PM1:✱10·51
✱10·51.  ⊢ : ∼{(∃x).φx .ψx} .≡ : φx .⊃ₓ .∼ψx
Dem.  By ✱10·252 and ✱4·51·62·✱10·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·51 -/
/- PM-VERBATIM-BEGIN PM1:✱10·52
✱10·52.  ⊢ : .(∃x).φx .⊃ : (x).φx⊃p .⊃ .p
Dem.  By ✱5·5 and ✱10·23, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·52 -/
/- PM-VERBATIM-BEGIN PM1:✱10·53
✱10·53.  ⊢ : ∼(∃x).φx .⊃ : φx .⊃ₓ .ψx
Dem.  By ✱2·21, ✱10·11, ✱10·27, and ✱10·252, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·53 -/
/- PM-VERBATIM-BEGIN PM1:✱10·541
✱10·541.  ⊢ : φy .⊃ᵧ .p∨ψy .≡ : p .∨ .φy⊃ᵧψy
Dem.  By ✱4·2, ✱1·01, Assoc, ✱10·271, and ✱10·2, ⊢ . Prop.
PM-VERBATIM-END PM1:✱10·541 -/
/- PM-VERBATIM-BEGIN PM1:✱10·542
✱10·542.  ⊢ : φy .⊃ᵧ .p⊃ψy .≡ : p .⊃ .φy⊃ᵧψy  [✱10·541  ∼p/p]
PM-VERBATIM-END PM1:✱10·542 -/
