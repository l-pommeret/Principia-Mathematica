/- Diplomatic source record for PM I, ✱11. Lean integration is architecture-blocked. -/
/- PM-VERBATIM-BEGIN PM1:✱11·01
✱11·01.  (x, y).φ(x, y) .= : (x) : (y).φ(x, y)  Df
PM-VERBATIM-END PM1:✱11·01 -/
/- PM-VERBATIM-BEGIN PM1:✱11·02
✱11·02.  (x, y, z).φ(x, y, z) .= : (x) : (y, z).φ(x, y, z)  Df
PM-VERBATIM-END PM1:✱11·02 -/
/- PM-VERBATIM-BEGIN PM1:✱11·03
✱11·03.  (∃x, y).φ(x, y) .= : (∃x) : (∃y).φ(x, y)  Df
PM-VERBATIM-END PM1:✱11·03 -/
/- PM-VERBATIM-BEGIN PM1:✱11·04
✱11·04.  (∃x, y, z).φ(x, y, z) .= : (∃x) : (∃y, z).φ(x, y, z)  Df
PM-VERBATIM-END PM1:✱11·04 -/
/- PM-VERBATIM-BEGIN PM1:✱11·05
✱11·05.  φ(x, y) .⊃ₓ,ᵧ. ψ(x, y) .= : (x, y) : φ(x, y) .⊃ .ψ(x, y)  Df
PM-VERBATIM-END PM1:✱11·05 -/
/- PM-VERBATIM-BEGIN PM1:✱11·06
✱11·06.  φ(x, y) .≡ₓ,ᵧ. ψ(x, y) .= : (x, y) : φ(x, y) .≡ .ψ(x, y)  Df
PM-VERBATIM-END PM1:✱11·06 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱11·1
✱11·1.  ⊢ : (x, y).φ(x, y) .⊃ .φ(z, w)
PM-VERBATIM-SUMMARY-END PM1:✱11·1 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱11·11
✱11·11.  If φ(z, w) is true whatever possible arguments z and w may be,
then (x, y).φ(x, y) is true.
PM-VERBATIM-SUMMARY-END PM1:✱11·11 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱11·2
✱11·2.  ⊢ : (x, y).φ(x, y) .≡ .(y, x).φ(x, y)
PM-VERBATIM-SUMMARY-END PM1:✱11·2 -/
/- PM-VERBATIM-SUMMARY-BEGIN PM1:✱11·3
✱11·3.  ⊢ : .p .⊃ .(x, y).φ(x, y) .≡ : (x, y) : p .⊃ .φ(x, y)
PM-VERBATIM-SUMMARY-END PM1:✱11·3 -/
/- PM-VERBATIM-BEGIN PM1:✱11·07
✱11·07.  “Whatever possible argument x may be, φ(x, y) is true whatever
possible argument y may be” implies the corresponding statement with x and y
interchanged.  Pp.
PM-VERBATIM-END PM1:✱11·07 -/
/- PM-VERBATIM-BEGIN PM1:✱11·1
✱11·1.  ⊢ : (x, y).φ(x, y) .⊃ .φ(z, w)
Dem.  ⊢ . ✱10·1 . ⊃ ⊢ : Hp .⊃ .(y).φ(z, y).
[✱10·1] ⊃ .φ(z, w) .⊃ ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·1 -/
/- PM-VERBATIM-BEGIN PM1:✱11·11
✱11·11.  If φ(z, w) is true whatever possible arguments z and w may be,
then (x, y).φ(x, y) is true.
Dem.  By ✱10·11, the hypothesis implies that (y).φ(z, y) is true whatever
possible argument z may be; and this, by ✱10·11, implies (x, y).φ(x, y).
PM-VERBATIM-END PM1:✱11·11 -/
/- PM-VERBATIM-BEGIN PM1:✱11·12
✱11·12.  ⊢ : .(x, y).p∨φ(x, y) .⊃ : p .∨ .(x, y).φ(x, y)
Dem.  By ✱10·12, ✱10·11·27, and ✱10·12, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·12 -/
/- PM-VERBATIM-BEGIN PM1:✱11·13
✱11·13.  If φ(x̂, ŷ), ψ(x̂, ŷ) take their first and second arguments respectively
of the same type, and we have “⊢.φ(x, y)” and “⊢.ψ(x, y),” we shall have
“⊢.φ(x, y).ψ(x, y).”  [Proof as in ✱10·13]
PM-VERBATIM-END PM1:✱11·13 -/
/- PM-VERBATIM-BEGIN PM1:✱11·14
✱11·14.  ⊢ : .(x, y).φ(x, y) : (x, y).ψ(x, y) .⊃ .φ(z, w).ψ(z, w)
Dem.  By two uses of ✱10·14, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·14 -/
/- PM-VERBATIM-BEGIN PM1:✱11·2
✱11·2.  ⊢ : (x, y).φ(x, y) .≡ .(y, x).φ(x, y)
Dem.  By ✱11·1, ✱11·07·11, and ✱11·12, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·2 -/
/- PM-VERBATIM-BEGIN PM1:✱11·21
✱11·21.  ⊢ : (x, y, z).φ(x, y, z) .≡ .(y, z, x).φ(x, y, z)
Dem.  By ✱11·01·02, ✱11·2, and ✱10·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·21 -/
/- PM-VERBATIM-BEGIN PM1:✱11·22
✱11·22.  ⊢ : (∃x, y).φ(x, y) .≡ .∼{(x, y).∼φ(x, y)}
Dem.  By ✱10·252, Transp, and ✱11·03, ✱10·252·271, ✱11·01,
⊢ . Prop.
PM-VERBATIM-END PM1:✱11·22 -/
/- PM-VERBATIM-BEGIN PM1:✱11·23
✱11·23.  ⊢ : (∃x, y).φ(x, y) .≡ .(∃y, x).φ(x, y)
Dem.  By ✱11·22, ✱11·2.Transp, and ✱11·22, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·23 -/
/- PM-VERBATIM-BEGIN PM1:✱11·24
✱11·24.  ⊢ : (∃x, y, z).φ(x, y, z) .≡ .(∃y, z, x).φ(x, y, z)
Dem.  By ✱11·03·04, ✱11·23, and ✱10·281, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·24 -/
/- PM-VERBATIM-BEGIN PM1:✱11·25
✱11·25.  ⊢ : ∼{(∃x, y).φ(x, y)} .≡ .(x, y).∼φ(x, y)  [✱11·22.Transp]
PM-VERBATIM-END PM1:✱11·25 -/
/- PM-VERBATIM-BEGIN PM1:✱11·26
✱11·26.  ⊢ : .(∃x) : (y).φ(x, y) .⊃ : (y) : (∃x).φ(x, y)
Dem.  By ✱10·1·28 and ✱10·11·21, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·26 -/
/- PM-VERBATIM-BEGIN PM1:✱11·27
✱11·27.  ⊢ : .(∃x, y) : (∃z).φ(x, y, z) .≡ : (∃x) : (∃y, z).φ(x, y, z)
≡ : (∃x, y, z).φ(x, y, z)
Dem.  By ✱4·2, ✱11·03, ✱10·11·281, and ✱11·04, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·27 -/
/- PM-VERBATIM-BEGIN PM1:✱11·3
✱11·3.  ⊢ : .p .⊃ .(x, y).φ(x, y) .≡ : (x, y) : p .⊃ .φ(x, y)
Dem.  By ✱10·21 and ✱10·21·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·3 -/
/- PM-VERBATIM-BEGIN PM1:✱11·31
✱11·31.  ⊢ : .(x, y).φ(x, y) : (x̂, ŷ).ψ(x, y) .≡ : (x, y) φ(x, y).ψ(x, y)
Dem.  By ✱10·22 and ✱10·22·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·31 -/
/- PM-VERBATIM-BEGIN PM1:✱11·311
✱11·311.  If φ(x̂, ŷ), ψ(x̂, ŷ) take arguments of the same type, and we have
“⊢.φ(x, y)” and “⊢.ψ(x, y),” we shall have “⊢.φ(x, y).ψ(x, y).”
[Proof as in ✱10·13.]
PM-VERBATIM-END PM1:✱11·311 -/
/- PM-VERBATIM-BEGIN PM1:✱11·32
✱11·32.  ⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : ⊃ :
(x, y).φ(x, y) .⊃ .(x, y).ψ(x, y)  [✱10·27]
PM-VERBATIM-END PM1:✱11·32 -/
/- PM-VERBATIM-BEGIN PM1:✱11·33
✱11·33.  ⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : ⊃ :
(x, y).φ(x, y) .≡ .(x, y).ψ(x, y)  [✱10·271]
PM-VERBATIM-END PM1:✱11·33 -/
/- PM-VERBATIM-BEGIN PM1:✱11·34
✱11·34.  ⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : ⊃ :
(∃x, y).φ(x, y) .⊃ .(∃x, y).ψ(x, y)  [✱10·27·28]
PM-VERBATIM-END PM1:✱11·34 -/
/- PM-VERBATIM-BEGIN PM1:✱11·341
✱11·341.  ⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : ⊃ :
(∃x, y).φ(x, y) .≡ .(∃x, y).ψ(x, y)  [✱10·271·281]
PM-VERBATIM-END PM1:✱11·341 -/
/- PM-VERBATIM-BEGIN PM1:✱11·35
✱11·35.  ⊢ : .(x, y) : φ(x, y) .⊃ .p : ≡ :
(∃x, y).φ(x, y) .⊃ .p  [✱10·23·271]
PM-VERBATIM-END PM1:✱11·35 -/
/- PM-VERBATIM-BEGIN PM1:✱11·36
✱11·36.  ⊢ : φ(z, w) .⊃ .(∃x, y).φ(x, y)
Dem.  ⊢ . ✱11·1 . ⊃ ⊢ : (x, y).∼φ(x, y) .⊃ .∼φ(z, w);
then (1).Transp, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·36 -/
/- PM-VERBATIM-BEGIN PM1:✱11·37
✱11·37.  ⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : .(x, y) :
ψ(x, y) .⊃ .χ(x, y) :. ⊃ : (x, y) : φ(x, y) .⊃ .χ(x, y)
Dem.  By ✱11·31, Syll. ✱11·11, ✱11·32, and ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·37 -/
/- PM-VERBATIM-BEGIN PM1:✱11·371
✱11·371.  ⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : .(x, y) :
ψ(x, y) .≡ .χ(x, y) :. ⊃ : (x, y) : φ(x, y) .≡ .χ(x, y)
[✱11·31·11·33]
PM-VERBATIM-END PM1:✱11·371 -/
/- PM-VERBATIM-BEGIN PM1:✱11·38
✱11·38.  ⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) :. ⊃ :
(x, y) : φ(x, y).χ(x, y) .⊃ .ψ(x, y).χ(x, y)  [Fact. ✱11·11·32]
PM-VERBATIM-END PM1:✱11·38 -/
/- PM-VERBATIM-BEGIN PM1:✱11·39
✱11·39.  ⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : .(x, y) :
χ(x, y) .⊃ .θ(x, y) :. ⊃ : (x, y) : φ(x, y).χ(x, y) .⊃ .ψ(x, y).θ(x, y)
[✱3·47. ✱11·11·32]
PM-VERBATIM-END PM1:✱11·39 -/
/- PM-VERBATIM-BEGIN PM1:✱11·391
✱11·391.  ⊢ :: (x, y) : φ(x, y) .⊃ .ψ(x, y) : .(x, y) :
φ(x, y) .⊃ .χ(x, y) :. ≡ : (x, y) : φ(x, y) .⊃ .ψ(x, y).χ(x, y)
Dem.  By ✱4·76, ✱11·11·33, and ✱11·31, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·391 -/
/- PM-VERBATIM-BEGIN PM1:✱11·4
✱11·4.  ⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : .(x, y) :
χ(x, y) .≡ .θ(x, y) :. ⊃ : (x, y) : φ(x, y).χ(x, y) .≡ .ψ(x, y).θ(x, y)
Dem.  By ✱11·31, ✱4·38, ✱11·11·32, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·4 -/
/- PM-VERBATIM-BEGIN PM1:✱11·401
✱11·401.  ⊢ :: (x, y) : φ(x, y) .≡ .ψ(x, y) : ⊃ :
(x, y) : φ(x, y).χ(x, y) .≡ .ψ(x, y).χ(x, y)  [✱11·4 χ/θ .Id]
PM-VERBATIM-END PM1:✱11·401 -/
/- PM-VERBATIM-BEGIN PM1:✱11·41
✱11·41.  ⊢ : .(∃x, y).φ(x, y) :∨: (∃x, y).ψ(x, y) :
≡ : (∃x, y) : φ(x, y) .∨ .ψ(x, y)  [✱10·42·281]
PM-VERBATIM-END PM1:✱11·41 -/
/- PM-VERBATIM-BEGIN PM1:✱11·42
✱11·42.  ⊢ : .(∃x, y).φ(x, y).ψ(x, y) .⊃ :
(∃x, y).φ(x, y) : (∃x, y).ψ(x, y)  [✱10·5]
PM-VERBATIM-END PM1:✱11·42 -/
/- PM-VERBATIM-BEGIN PM1:✱11·421
✱11·421.  ⊢ : .(x, y).φ(x, y) .∨ .(x, y).ψ(x, y) .⊃ :
(x, y) : φ(x, y) .∨ .ψ(x, y)
[✱11·42 ∼φ, ∼ψ / φ, ψ .Transp. ✱4·56]
PM-VERBATIM-END PM1:✱11·421 -/
/- PM-VERBATIM-BEGIN PM1:✱11·43
✱11·43.  ⊢ : .(∃x, y) : φ(x, y) .⊃ .p : ≡ :
(x, y).φ(x, y) .⊃ .p  [✱10·34·281]
PM-VERBATIM-END PM1:✱11·43 -/
/- PM-VERBATIM-BEGIN PM1:✱11·44
✱11·44.  ⊢ : .(x, y) : φ(x, y) .∨ .p : ≡ :
(x, y).φ(x, y) .∨ .p  [✱10·2·271]
PM-VERBATIM-END PM1:✱11·44 -/
/- PM-VERBATIM-BEGIN PM1:✱11·45
✱11·45.  ⊢ : .(∃x, y) : p .φ(x, y) : ≡ :
p : (∃x, y).φ(x, y)  [✱10·35·281]
PM-VERBATIM-END PM1:✱11·45 -/
/- PM-VERBATIM-BEGIN PM1:✱11·46
✱11·46.  ⊢ : .(∃x, y) : p .⊃ .φ(x, y) : ≡ :
p .⊃ .(∃x, y).φ(x, y)  [✱10·37·281]
PM-VERBATIM-END PM1:✱11·46 -/
/- PM-VERBATIM-BEGIN PM1:✱11·47
✱11·47.  ⊢ : .(x, y) : p .φ(x, y) : ≡ :
p : (x, y).φ(x, y)  [✱10·33·271]
PM-VERBATIM-END PM1:✱11·47 -/
/- PM-VERBATIM-BEGIN PM1:✱11·5
✱11·5.  ⊢ : .(∃x) : ∼{(y).φ(x, y)} : ≡ :
∼{(x, y).φ(x, y)} : ≡ : (∃x, y).∼φ(x, y)
Dem.  By ✱10·253, ✱11·01, ✱10·11·281, and ✱11·03, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·5 -/
/- PM-VERBATIM-BEGIN PM1:✱11·51
✱11·51.  ⊢ : .(∃x) : (y).φ(x, y) : ≡ :
∼{(x) : (∃y).∼φ(x, y)}
Dem.  By ✱10·252, Transp, ✱10·253, and ✱10·11·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·51 -/
/- PM-VERBATIM-BEGIN PM1:✱11·52
✱11·52.  ⊢ : .(∃x, y).φ(x, y).ψ(x, y) .≡ :
∼{(x, y) : φ(x, y) .⊃ .∼ψ(x, y)}
Dem.  By ✱4·51·62, ✱11·11·33, and ✱11·22, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·52 -/
/- PM-VERBATIM-BEGIN PM1:✱11·521
✱11·521.  ⊢ : .∼(∃x, y).φ(x, y).∼ψ(x, y) .≡ :
(x, y) : φ(x, y) .⊃ .ψ(x, y)
[✱11·52.Transp. ∼φ, ∼ψ / φ, ψ]
PM-VERBATIM-END PM1:✱11·521 -/
/- PM-VERBATIM-BEGIN PM1:✱11·53
✱11·53.  ⊢ : .(x, y).φx ⊃ ψy .≡ :
(∃x).φx .⊃ .(y).ψy
Dem.  By ✱10·21·271, ✱10·23, ✱11·57, ✱3·47, ✱11·32, and ✱11·1,
⊢ . Prop.
PM-VERBATIM-END PM1:✱11·53 -/
/- PM-VERBATIM-BEGIN PM1:✱11·54
✱11·54.  ⊢ : .(∃x, y).φx.ψy .≡ :
(∃x).φx : (∃y).ψy
Dem.  By ✱10·35, ✱10·11·281, and ✱10·35, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·54 -/
/- PM-VERBATIM-BEGIN PM1:✱11·55
✱11·55.  ⊢ : .(∃x, y).φx.ψ(x, y) .≡ :
(∃x) : φx : (∃y).ψ(x, y)
Dem.  By ✱10·35, ✱10·11, and ✱10·281, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·55 -/
/- PM-VERBATIM-BEGIN PM1:✱11·56
✱11·56.  ⊢ : .(x).φx : (y).ψy .≡ :
(x, y).φx.ψy
Dem.  By ✱10·33, ✱10·11, ✱10·271, and ✱11·01, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·56 -/
/- PM-VERBATIM-BEGIN PM1:✱11·57
✱11·57.  ⊢ : (x).φx .≡ .(x, y).φx.φy  [✱11·56. ✱4·24]
PM-VERBATIM-END PM1:✱11·57 -/
/- PM-VERBATIM-BEGIN PM1:✱11·58
✱11·58.  ⊢ : (∃x).φx .≡ .(∃x, y).φx.φy  [✱11·54. ✱4·24]
PM-VERBATIM-END PM1:✱11·58 -/
/- PM-VERBATIM-BEGIN PM1:✱11·59
✱11·59.  ⊢ : .φx .⊃ₓ .ψx : ≡ :
φx.φy .⊃ₓ,ᵧ .ψx.ψy
Dem.  By ✱11·57, ✱3·47, ✱11·32, ✱11·1, and ✱10·11·21, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·59 -/
/- PM-VERBATIM-BEGIN PM1:✱11·6
✱11·6.  ⊢ :: (∃x) :: (∃y).φ(x, y).ψy:χx :: ≡ ::
(∃y) :: (∃x).φ(x, y).χx:ψy
Dem.  By ✱10·35, ✱10·11·281, ✱11·23, ✱11·341.Perm, and ✱10·35·281,
⊢ . Prop.
PM-VERBATIM-END PM1:✱11·6 -/
/- PM-VERBATIM-BEGIN PM1:✱11·61
✱11·61.  ⊢ :: (∃y) : φx .⊃ₓ .ψ(x, y) : ⊃ :
φx .⊃ₓ .(∃y).ψ(x, y)
Dem.  By ✱11·26, ✱10·37, and ✱10·11·27, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·61 -/
/- PM-VERBATIM-BEGIN PM1:✱11·62
✱11·62.  ⊢ :: φx.ψ(x, y) .⊃ₓ,ᵧ .χ(x, y) .≡ :
φx .⊃ₓ .ψ(x, y) .⊃ᵧ .χ(x, y)
Dem.  By ✱4·87, ✱11·11·33, and ✱10·21·11·271, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·62 -/
/- PM-VERBATIM-BEGIN PM1:✱11·63
✱11·63.  ⊢ :: ∼(∃x, y).φ(x, y) .⊃ :
φ(x, y) .⊃ₓ,ᵧ .ψ(x, y)
Dem.  By ✱2·21, ✱11·11, ✱11·32, and ✱11·25, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·63 -/
/- PM-VERBATIM-BEGIN PM1:✱11·7
✱11·7.  ⊢ :: (∃x, y) : φ(x, y) .∨ .φ(y, x) .≡ .(∃x, y).φ(x, y)
Dem.  By ✱11·41, ✱11·23, and ✱4·25, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·7 -/
/- PM-VERBATIM-BEGIN PM1:✱11·71
✱11·71.  ⊢ :: (∃z).φz : (∃w).χw : ⊃ :
φz .⊃z .ψz : χw .⊃w .θw : ≡ : φz.χw .⊃z,w .ψz.θw
Dem.  By ✱10·1, ✱3·47, ✱11·11·3, ✱10·28, ✱10·35,
✱10·11·21, and ✱3·47.Comp, ⊢ . Prop.
PM-VERBATIM-END PM1:✱11·71 -/
