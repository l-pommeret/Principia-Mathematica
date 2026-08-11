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
/- PM-VERBATIM-BEGIN PM1:✱11·1
✱11·1.  ⊢ : (x, y).φ(x, y) .⊃ .φ(z, w)
PM-VERBATIM-END PM1:✱11·1 -/
/- PM-VERBATIM-BEGIN PM1:✱11·11
✱11·11.  If φ(z, w) is true whatever possible arguments z and w may be,
then (x, y).φ(x, y) is true.
PM-VERBATIM-END PM1:✱11·11 -/
/- PM-VERBATIM-BEGIN PM1:✱11·2
✱11·2.  ⊢ : (x, y).φ(x, y) .≡ .(y, x).φ(x, y)
PM-VERBATIM-END PM1:✱11·2 -/
/- PM-VERBATIM-BEGIN PM1:✱11·3
✱11·3.  ⊢ : .p .⊃ .(x, y).φ(x, y) .≡ : (x, y) : p .⊃ .φ(x, y)
PM-VERBATIM-END PM1:✱11·3 -/
/- PM-VERBATIM-BEGIN PM1:✱11·07
✱11·07.  “Whatever possible argument x may be, φ(x, y) is true whatever
possible argument y may be” implies the corresponding statement with x and y
interchanged.  Pp.
PM-VERBATIM-END PM1:✱11·07 -/
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
