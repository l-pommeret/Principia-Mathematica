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
Dem.
⊢ . ✱10·22 . ⊃ ⊢ :: φ!x .≡φ . φ!y : ⊃ : φ!x .⊃φ . φ!y :
[✱13·1] ⊃ : x = y  (1)
⊢ . ✱13·101 . ⊃ ⊢ :: x = y .⊃ . φ!x .⊃ . φ!y  (2)
⊢ . ✱13·101 . ✱1·7 . ⊃ ⊢ :: x = y .⊃ . ∼φ!x .⊃ . ∼φ!y .
[Transp] ⊃ . φ!y .⊃ . φ!x  (3)
⊢ . (2).(3).Comp . ⊃ ⊢ : x = y .⊃ . φ!x .≡ . φ!y :
[✱10·11·21] ⊃ ⊢ :: x = y .⊃ : φ!x .≡φ . φ!y  (4)
⊢ . (1).(4) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·11 -/
/- PM-VERBATIM-BEGIN PM1:✱13·12
✱13·12.  ⊢ : x = y .⊃ . ψx .≡ . ψy
Dem.
⊢ . ✱13·101 . Comp . ⊃ ⊢ : x = y .⊃ . ψx .⊃ . ψy . ∼ψx .⊃ . ∼ψy .
[Transp] ⊃ . ψx .≡ . ψy : ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·12 -/
/- PM-VERBATIM-BEGIN PM1:✱13·13
✱13·13.  ⊢ : ψx . x = y .⊃ . ψy  [✱13·101 . Comm . Imp]
PM-VERBATIM-END PM1:✱13·13 -/
/- PM-VERBATIM-BEGIN PM1:✱13·14
✱13·14.  ⊢ : ψx . ∼ψy .⊃ . x ≠ y  [✱13·13 . ✱4·14]
PM-VERBATIM-END PM1:✱13·14 -/
/- PM-VERBATIM-BEGIN PM1:✱13·15
✱13·15.  ⊢ . x = x  [Id . ✱10·11 . ✱13·1]
PM-VERBATIM-END PM1:✱13·15 -/
/- PM-VERBATIM-BEGIN PM1:✱13·16
✱13·16.  ⊢ : x = y .≡ . y = x  [✱13·11 . ✱10·32]
PM-VERBATIM-END PM1:✱13·16 -/
/- PM-VERBATIM-BEGIN PM1:✱13·17
✱13·17.  ⊢ : x = y . y = z .⊃ . x = z
Dem.
⊢ . ✱13·1 . ⊃ ⊢ :: Hp . ⊃ :: φ!x .⊃φ . φ!y : φ!y .⊃φ . φ!z ::
[✱10·3] ⊃ :: φ!x .⊃φ . φ!z :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·17 -/
/- PM-VERBATIM-BEGIN PM1:✱13·171
✱13·171.  ⊢ : x = y . x = z .⊃ . y = z  [✱13·16·17]
PM-VERBATIM-END PM1:✱13·171 -/
/- PM-VERBATIM-BEGIN PM1:✱13·172
✱13·172.  ⊢ : y = x . z = x .⊃ . y = z  [✱13·16·17]
PM-VERBATIM-END PM1:✱13·172 -/
/- PM-VERBATIM-BEGIN PM1:✱13·18
✱13·18.  ⊢ : x = y . x ≠ z .⊃ . y ≠ z  [✱13·17 . ✱4·14]
PM-VERBATIM-END PM1:✱13·18 -/
/- PM-VERBATIM-BEGIN PM1:✱13·181
✱13·181.  ⊢ : x = y . y ≠ z .⊃ . x ≠ z  [✱13·171 . ✱4·14]
PM-VERBATIM-END PM1:✱13·181 -/
/- PM-VERBATIM-BEGIN PM1:✱13·182
✱13·182.  ⊢ :. x = y .⊃ : z = x .≡ . z = y  [✱13·17·172 . Exp . Comp]
PM-VERBATIM-END PM1:✱13·182 -/
/- PM-VERBATIM-BEGIN PM1:✱13·183
✱13·183.  ⊢ :: x = y .≡ : z = x .≡z . z = y
Dem.
⊢ . ✱13·182 . ✱10·11·21 . ⊃ ⊢ :: x = y .⊃ : z = x .≡z . z = y  (1)
⊢ . ✱10·1 . ⊃ ⊢ :: z = x .≡z . z = y : ⊃ : x = x .⊃ . x = y :
[✱13·15] ⊃ : x = y  (2)
⊢ . (1).(2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·183 -/
/- PM-VERBATIM-BEGIN PM1:✱13·19
✱13·19.  ⊢ . (∃y). y = x  [✱13·15 . ✱10·24]
PM-VERBATIM-END PM1:✱13·19 -/
/- PM-VERBATIM-BEGIN PM1:✱13·191
✱13·191.  ⊢ :: y = x .⊃y . φy : ≡ . φx
Dem.
⊢ . ✱10·1 . ⊃ ⊢ :: y = x .⊃y . φy : ⊃ : x = x .⊃ . φx :
[✱13·15] ⊃ : φx  (1)
⊢ . ✱13·12 . ⊃ ⊢ :: y = x .⊃ : φx .⊃ . φy ::
[Comm] ⊃ ⊢ :: φx .⊃ : y = x .⊃ . φy ::
[✱10·11·21] ⊃ ⊢ :: φx .⊃ : y = x .⊃y . φy  (2)
⊢ . (1).(2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·191 -/
/- PM-VERBATIM-BEGIN PM1:✱13·192
✱13·192.  ⊢ :: (∃c) : x = b .≡x . x = c : ψc : ≡ . ψb
Dem.
⊢ . ✱4·2 . ✱3·2 . ⊃ ⊢ :: ψb .⊃ :: x = b .≡x . x = b : ψb ::
[✱10·24] ⊃ :: (∃c) : x = b .≡x . x = c : ψc  (1)
⊢ . ✱10·1 . ⊃ ⊢ :: x = b .≡x . x = c : ψc : ⊃ : b = b .≡ . b = c : ψc :
[✱5·501.✱13·15] ⊃ : b = c . ψc :
[✱13·13] ⊃ : ψb  (2)
⊢ . (2).✱10·11·23 . ⊃ ⊢ :: (∃c) : x = b .≡x . x = c : ψc : ⊃ . ψb  (3)
⊢ . (1).(3) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·192 -/
/- PM-VERBATIM-BEGIN PM1:✱13·193
✱13·193.  ⊢ : φx . x = y .≡ . φy . x = y
Dem.
⊢ . Simp . ⊃ ⊢ : φx . x = y .⊃ . x = y  (1)
⊢ . ✱13·13 . ⊃ ⊢ : φx . x = y .⊃ . φy  (2)
⊢ . (1).(2).Comp . ⊃ ⊢ : φx . x = y .⊃ . φy . x = y  (3)
⊢ . ✱13·16.Fact . ⊃ ⊢ : φy . x = y .⊃ . φy . y = x .
[(3) y, x/x, y] ⊃ . φx . y = x .
[✱13·16.Fact] ⊃ . φx . x = y  (4)
⊢ . (3).(4) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·193 -/
/- PM-VERBATIM-BEGIN PM1:✱13·194
✱13·194.  ⊢ : φx . x = y .≡ . φx . φy . x = y  [✱13·13.✱4·71]
PM-VERBATIM-END PM1:✱13·194 -/
/- PM-VERBATIM-BEGIN PM1:✱13·195
✱13·195.  ⊢ : (∃y). y = x . φy .≡ . φx
Dem.
⊢ . ✱3·2 . ✱13·15 . ⊃ ⊢ : φx .⊃ . x = x . φx .
[✱10·24] ⊃ . (∃y). y = x . φy  (1)
⊢ . ✱13·13 . ✱10·11 . ⊃ ⊢ :: (y) : y = x . φy .⊃ . φx :
[✱10·23] ⊃ ⊢ :: (∃y). y = x . φy .⊃ . φx  (2)
⊢ . (1).(2) . ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·195 -/
/- PM-VERBATIM-BEGIN PM1:✱13·196
✱13·196.  ⊢ :: ∼φx .≡ : φy .⊃y . y ≠ x
PM-VERBATIM-END PM1:✱13·196 -/
/- PM-VERBATIM-BEGIN PM1:✱13·21
✱13·21.  ⊢ :: z = x . w = y .⊃z,w . φ(z, w) : ≡ . φ(x, y)
Dem.
⊢ . ✱11·62 . ⊃
⊢ :: z = x . w = y .⊃z,w . φ(z, w) : ≡ :: z = x .⊃z : w = y .⊃w . φ(z, w) ::
[✱13·191] ≡ :: w = y .⊃w . φ(x, w) ::
[✱13·191] ≡ :: φ(x, y) :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·21 -/
/- PM-VERBATIM-BEGIN PM1:✱13·22
✱13·22.  ⊢ : (∃z, w). z = x . w = y . φ(z, w) .≡ . φ(x, y)
Dem.
⊢ . ✱11·55 . ⊃ ⊢ :: (∃z, w). z = x . w = y . φ(z, w) .
≡ : (∃z) : z = x : (∃w). w = y . φ(z, w) :
[✱13·195] ≡ : (∃w). w = y . φ(x, w) :
[✱13·195] ≡ : φ(x, y) :: ⊃ ⊢ . Prop
PM-VERBATIM-END PM1:✱13·22 -/

/- PM-VERBATIM-BEGIN PM1:✱13·3
✱13·3. ⊢::φ a∨∼φ a.⊃:.φ x∨∼φ x.≡:x=a.∨.x≠ a
PM-VERBATIM-END PM1:✱13·3 -/
