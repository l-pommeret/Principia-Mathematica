/- Diplomatic source record for PM I, ✱13. Lean integration is architecture-blocked. -/
/- PM-VERBATIM-BEGIN PM1:✱13·01
✱13·01.  x = y .=: (φ) : φ!x .⊃ . φ!y  Df
PM-VERBATIM-END PM1:✱13·01 -/
/- PM-VERBATIM-BEGIN PM1:✱13·02
✱13·02.  x ≠ y .=. ∼(x = y)  Df
PM-VERBATIM-END PM1:✱13·02 -/
/- PM-VERBATIM-BEGIN PM1:✱13·03
✱13·03.  x = y = z .=. x = y . y = z  Df
PM-VERBATIM-END PM1:✱13·03 -/
/- PM-VERBATIM-BEGIN PM1:✱13·1
✱13·1.  ⊢ :: x = y .≡ : φ!x .⊃φ . φ!y
[✱4·2.(✱13·01).(✱10·02)]
PM-VERBATIM-END PM1:✱13·1 -/
/- PM-VERBATIM-BEGIN PM1:✱13·101
✱13·101.  ⊢ : x = y .⊃ . ψx .⊃ . ψy
Dem.
⊢ . ✱12·1 . ⊃ ⊢ :: (∃φ) :: ψx .≡ .φ!x : ψy .≡ .φ!y  (1)
⊢ . ✱13·1 . ⊃ ⊢ :: Hp .⊃ :: φ!x .⊃φ .φ!y ::
[✱4·84·85.✱10·27] ⊃ :: ψx .≡ .φ!x : ψy .≡ .φ!y : ⊃φ : ψx .⊃ .ψy ::
[✱10·23] ⊃ :: (∃φ) : ψx .≡ .φ!x : ψy .≡ .φ!y : ⊃ : ψx .⊃ .ψy  (2)
⊢ . (1).(2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·101 -/
/- PM-VERBATIM-BEGIN PM1:✱13·11
✱13·11.  ⊢ :: x = y .≡ : φ!x .≡φ . φ!y
PM-VERBATIM-END PM1:✱13·11 -/
/- PM-VERBATIM-BEGIN PM1:✱13·12
✱13·12.  ⊢ : x = y .⊃ . ψx .≡ . ψy
PM-VERBATIM-END PM1:✱13·12 -/
/- PM-VERBATIM-BEGIN PM1:✱13·13
✱13·13.  ⊢ : ψx . x = y .⊃ . ψy
PM-VERBATIM-END PM1:✱13·13 -/
/- PM-VERBATIM-BEGIN PM1:✱13·14
✱13·14.  ⊢ : ψx . ∼ψy .⊃ . x ≠ y
PM-VERBATIM-END PM1:✱13·14 -/
/- PM-VERBATIM-BEGIN PM1:✱13·15
✱13·15.  ⊢ . x = x
PM-VERBATIM-END PM1:✱13·15 -/
/- PM-VERBATIM-BEGIN PM1:✱13·16
✱13·16.  ⊢ : x = y .≡ . y = x
PM-VERBATIM-END PM1:✱13·16 -/
/- PM-VERBATIM-BEGIN PM1:✱13·17
✱13·17.  ⊢ : x = y . y = z .⊃ . x = z
PM-VERBATIM-END PM1:✱13·17 -/
/- PM-VERBATIM-BEGIN PM1:✱13·171
✱13·171.  ⊢ : x = y . x = z .⊃ . y = z
PM-VERBATIM-END PM1:✱13·171 -/
/- PM-VERBATIM-BEGIN PM1:✱13·172
✱13·172.  ⊢ : y = x . z = x .⊃ . y = z
PM-VERBATIM-END PM1:✱13·172 -/
/- PM-VERBATIM-BEGIN PM1:✱13·18
✱13·18.  ⊢ : x = y . x ≠ z .⊃ . y ≠ z
PM-VERBATIM-END PM1:✱13·18 -/
/- PM-VERBATIM-BEGIN PM1:✱13·181
✱13·181.  ⊢ : x = y . y ≠ z .⊃ . x ≠ z
PM-VERBATIM-END PM1:✱13·181 -/
/- PM-VERBATIM-BEGIN PM1:✱13·182
✱13·182.  ⊢ :: x = y .⊃ : z = x .≡ . z = y
PM-VERBATIM-END PM1:✱13·182 -/
/- PM-VERBATIM-BEGIN PM1:✱13·183
✱13·183.  ⊢ :: x = y .≡ : z = x .≡z . z = y
PM-VERBATIM-END PM1:✱13·183 -/
/- PM-VERBATIM-BEGIN PM1:✱13·19
✱13·19.  ⊢ . (∃y). y = x
PM-VERBATIM-END PM1:✱13·19 -/
/- PM-VERBATIM-BEGIN PM1:✱13·191
✱13·191.  ⊢ :: y = x .⊃y . φy : ≡ . φx
PM-VERBATIM-END PM1:✱13·191 -/
/- PM-VERBATIM-BEGIN PM1:✱13·192
✱13·192.  ⊢ :: (∃c) : x = b .≡x . x = c : ψc : ≡ . ψb
PM-VERBATIM-END PM1:✱13·192 -/
/- PM-VERBATIM-BEGIN PM1:✱13·193
✱13·193.  ⊢ : φx . x = y .≡ . φy . x = y
PM-VERBATIM-END PM1:✱13·193 -/
/- PM-VERBATIM-BEGIN PM1:✱13·194
✱13·194.  ⊢ : φx . x = y .≡ . φx . φy . x = y
PM-VERBATIM-END PM1:✱13·194 -/
/- PM-VERBATIM-BEGIN PM1:✱13·195
✱13·195.  ⊢ : (∃y). y = x . φy .≡ . φx
PM-VERBATIM-END PM1:✱13·195 -/
/- PM-VERBATIM-BEGIN PM1:✱13·196
✱13·196.  ⊢ :: ∼φx .≡ : φy .⊃y . y ≠ x
PM-VERBATIM-END PM1:✱13·196 -/
