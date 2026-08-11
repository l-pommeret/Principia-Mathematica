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
