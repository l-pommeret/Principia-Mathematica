/-!
Source-critical transcription of the opening of PM I, ✱40, from PG78050,
section `*40. PRODUCTS AND SUMS OF CLASSES OF CLASSES`.
-/

/- PM-VERBATIM-BEGIN PM1:✱40·01
✱40·01. pʻκ = x̂(α ∈ κ .⊃ₐ. x ∈ α)  Df
PM-VERBATIM-END PM1:✱40·01 -/
/- PM-VERBATIM-BEGIN PM1:✱40·02
✱40·02. sʻκ = x̂{(∃α). α ∈ κ . x ∈ α}  Df
PM-VERBATIM-END PM1:✱40·02 -/
/- PM-VERBATIM-BEGIN PM1:✱40·1
✱40·1. ⊢ :: x ∈ pʻκ .≡ : α ∈ κ .⊃ₐ. x ∈ α  [✱20·3.(✱40·01)]
PM-VERBATIM-END PM1:✱40·1 -/
/- PM-VERBATIM-BEGIN PM1:✱40·11
✱40·11. ⊢ : x ∈ sʻκ .≡. (∃α). α ∈ κ . x ∈ α  [✱20·3.(✱40·02)]
PM-VERBATIM-END PM1:✱40·11 -/
/- PM-VERBATIM-BEGIN PM1:✱40·12
✱40·12. ⊢ : α ∈ κ .⊃. pʻκ ⊂ α
PM-VERBATIM-END PM1:✱40·12 -/
/- PM-VERBATIM-BEGIN PM1:✱40·13
✱40·13. ⊢ : α ∈ κ .⊃. α ⊂ sʻκ
PM-VERBATIM-END PM1:✱40·13 -/
/- PM-VERBATIM-BEGIN PM1:✱40·14
✱40·14. ⊢ : α ∈ κ . x ∈ pʻκ .⊃. x ∈ α  [✱40·12 . Imp]
PM-VERBATIM-END PM1:✱40·14 -/
/- PM-VERBATIM-BEGIN PM1:✱40·141
✱40·141. ⊢ : α ∈ κ . x ∈ α .⊃. x ∈ sʻκ  [✱40·11 . ✱10·24]
PM-VERBATIM-END PM1:✱40·141 -/
/- PM-VERBATIM-BEGIN PM1:✱40·15
✱40·15. ⊢ :: β ⊂ pʻκ .≡ : γ ∈ κ .⊃_γ. β ⊂ γ
PM-VERBATIM-END PM1:✱40·15 -/
/- PM-VERBATIM-BEGIN PM1:✱40·151
✱40·151. ⊢ :: sʻκ ⊂ β .≡ : γ ∈ κ .⊃_γ. γ ⊂ β
PM-VERBATIM-END PM1:✱40·151 -/
/- PM-VERBATIM-BEGIN PM1:✱40·16
✱40·16. ⊢ : κ ⊂ λ .⊃. pʻλ ⊂ pʻκ
PM-VERBATIM-END PM1:✱40·16 -/
/- PM-VERBATIM-BEGIN PM1:✱40·161
✱40·161. ⊢ : κ ⊂ λ .⊃. sʻκ ⊂ sʻλ
PM-VERBATIM-END PM1:✱40·161 -/
/- PM-VERBATIM-BEGIN PM1:✱40·17
✱40·17. ⊢. pʻκ ∪ pʻλ ⊂ pʻ(κ ∩ λ)
PM-VERBATIM-END PM1:✱40·17 -/
/- PM-VERBATIM-BEGIN PM1:✱40·171
✱40·171. ⊢. sʻκ ∪ sʻλ = sʻ(κ ∪ λ)
PM-VERBATIM-END PM1:✱40·171 -/
/- PM-VERBATIM-BEGIN PM1:✱40·18
✱40·18. ⊢. pʻ(κ ∪ λ) = pʻκ ∩ pʻλ
PM-VERBATIM-END PM1:✱40·18 -/
/- PM-VERBATIM-BEGIN PM1:✱40·181
✱40·181. ⊢. sʻ(κ ∩ λ) ⊂ sʻκ ∩ sʻλ
PM-VERBATIM-END PM1:✱40·181 -/
/- PM-VERBATIM-BEGIN PM1:✱40·19
✱40·19. ⊢ :: x ∈ sʻκ .≡ : γ ∈ κ .⊃_γ. γ ⊂ β :⊃_β. x ∈ β
PM-VERBATIM-END PM1:✱40·19 -/
/- PM-VERBATIM-BEGIN PM1:✱40·2
✱40·2. ⊢ : κ = Λ .⊃. pʻκ = V
PM-VERBATIM-END PM1:✱40·2 -/
/- PM-VERBATIM-BEGIN PM1:✱40·21
✱40·21. ⊢ : κ = Λ .⊃. sʻκ = Λ
PM-VERBATIM-END PM1:✱40·21 -/
/- PM-VERBATIM-BEGIN PM1:✱40·22
✱40·22. ⊢ :: Λ ∈ κ .⊃. pʻκ = Λ
PM-VERBATIM-END PM1:✱40·22 -/
/- PM-VERBATIM-BEGIN PM1:✱40·221
✱40·221. ⊢ : V ∈ κ .⊃. sʻκ = V
PM-VERBATIM-END PM1:✱40·221 -/
/- PM-VERBATIM-BEGIN PM1:✱40·23
✱40·23. ⊢ : ∃!κ .⊃. pʻκ ⊂ sʻκ
PM-VERBATIM-END PM1:✱40·23 -/
/- PM-VERBATIM-BEGIN PM1:✱40·24
✱40·24. ⊢ :: ∃!κ : γ ∈ κ .⊃_γ. β ⊂ γ :⊃. β ⊂ sʻκ
PM-VERBATIM-END PM1:✱40·24 -/
/- PM-VERBATIM-BEGIN PM1:✱40·25
✱40·25. ⊢ : x ∈ sʻκ .≡. ∃!{κ ∩ α̂(x ∈ α)}
PM-VERBATIM-END PM1:✱40·25 -/
/- PM-VERBATIM-BEGIN PM1:✱40·26
✱40·26. ⊢ : ∃!sʻκ .≡. (∃α). α ∈ κ . ∃!α
PM-VERBATIM-END PM1:✱40·26 -/
/- PM-VERBATIM-BEGIN PM1:✱40·27
✱40·27. ⊢ :: α ∩ sʻκ = Λ .≡ : γ ∈ κ .⊃_γ. α ∩ γ = Λ
PM-VERBATIM-END PM1:✱40·27 -/
/- PM-VERBATIM-BEGIN PM1:✱40·3
✱40·3. ⊢. pʻRʻʻ(α ∪ β) = pʻRʻʻα ∩ pʻRʻʻβ  [✱37·22.✱40·18]
PM-VERBATIM-END PM1:✱40·3 -/
/- PM-VERBATIM-BEGIN PM1:✱40·31
✱40·31. ⊢. sʻRʻʻ(α ∪ β) = sʻRʻʻα ∪ sʻRʻʻβ  [✱37·22.✱40·171]
PM-VERBATIM-END PM1:✱40·31 -/
/- PM-VERBATIM-BEGIN PM1:✱40·32
✱40·32. ⊢. pʻRʻʻα ∪ pʻRʻʻβ ⊂ pʻRʻʻ(α ∩ β)
PM-VERBATIM-END PM1:✱40·32 -/
/- PM-VERBATIM-BEGIN PM1:✱40·33
✱40·33. ⊢. sʻRʻʻ(α ∩ β) ⊂ sʻRʻʻα ∩ sʻRʻʻβ  [✱37·21.✱40·161.✱40·181]
PM-VERBATIM-END PM1:✱40·33 -/
/- PM-VERBATIM-BEGIN PM1:✱40·4
✱40·4. ⊢ : E‼Rʻʻβ .⊃. sʻRʻʻβ = x̂{(∃y). y ∈ β . x ∈ Rʻy}
PM-VERBATIM-END PM1:✱40·4 -/
/- PM-VERBATIM-BEGIN PM1:✱40·41
✱40·41. ⊢ : E‼Rʻʻβ .⊃. pʻRʻʻβ = x̂{y ∈ β .⊃_y. x ∈ Rʻy}  [Similar proof]
PM-VERBATIM-END PM1:✱40·41 -/
/- PM-VERBATIM-BEGIN PM1:✱40·42
✱40·42. ⊢ : (x). Rʻx = Pʻx ∪ Qʻx .⊃. sʻRʻʻα = sʻ(Pʻʻα ∪ Qʻʻα) = sʻPʻʻα ∪ sʻQʻʻα
PM-VERBATIM-END PM1:✱40·42 -/
/- PM-VERBATIM-BEGIN PM1:✱40·43
✱40·43. ⊢ :: E‼Rʻʻβ .⊃:. sʻRʻʻβ ⊂ α .≡: y ∈ β .⊃_y. Rʻy ⊂ α
PM-VERBATIM-END PM1:✱40·43 -/
/- PM-VERBATIM-BEGIN PM1:✱40·44
✱40·44. ⊢ : E‼Rʻʻβ .⊃. α ⊂ pʻRʻʻβ .≡. y ∈ β .⊃_y. α ⊂ Rʻy
PM-VERBATIM-END PM1:✱40·44 -/
/- PM-VERBATIM-BEGIN PM1:✱40·45
✱40·45. ⊢ :. y ∈ β .⊃_y. Rʻy ⊂ Sʻy :⊃. sʻRʻʻβ ⊂ sʻSʻʻβ
PM-VERBATIM-END PM1:✱40·45 -/
/- PM-VERBATIM-BEGIN PM1:✱40·451
✱40·451. ⊢ :. y ∈ β .⊃_y. Rʻy ⊂ Sʻy :⊃. pʻRʻʻβ ⊂ pʻSʻʻβ
PM-VERBATIM-END PM1:✱40·451 -/
/- PM-VERBATIM-BEGIN PM1:✱40·5
✱40·5. ⊢. sʻR⃗ʻʻβ = Rʻʻβ
PM-VERBATIM-END PM1:✱40·5 -/
/- PM-VERBATIM-BEGIN PM1:✱40·51
✱40·51. ⊢. pʻR⃗ʻʻβ = x̂{y ∈ β .⊃_y. x R y}  [✱32·12.✱40·41.✱32·18]
PM-VERBATIM-END PM1:✱40·51 -/
/- PM-VERBATIM-BEGIN PM1:✱40·52
✱40·52. ⊢. sʻR⃖ʻʻβ = R̅ʻʻβ
PM-VERBATIM-END PM1:✱40·52 -/
/- PM-VERBATIM-BEGIN PM1:✱40·53
✱40·53. ⊢. pʻR⃖ʻʻβ = ŷ{x ∈ β .⊃_x. x R y}
PM-VERBATIM-END PM1:✱40·53 -/
/- PM-VERBATIM-BEGIN PM1:✱40·54
✱40·54. ⊢. pʻR⃗ʻʻβ = x̂(β ⊂ R⃖ʻx)
PM-VERBATIM-END PM1:✱40·54 -/
/- PM-VERBATIM-BEGIN PM1:✱40·55
✱40·55. ⊢. pʻR⃖ʻʻα = ŷ(α ⊂ R⃗ʻy)
PM-VERBATIM-END PM1:✱40·55 -/
/- PM-VERBATIM-BEGIN PM1:✱40·56
✱40·56. ⊢. sʻCʻʻλ = Fʻʻλ  [✱33·5.✱40·5]
PM-VERBATIM-END PM1:✱40·56 -/
/- PM-VERBATIM-BEGIN PM1:✱40·57
✱40·57. ⊢. sʻCʻʻλ = sʻ(Dʻʻλ ∪ ᗡʻʻλ) = sʻDʻʻλ ∪ sʻᗡʻʻλ  [✱40·42.✱33·16]
PM-VERBATIM-END PM1:✱40·57 -/
/- PM-VERBATIM-BEGIN PM1:✱40·6
✱40·6. ⊢. pʻR⃗ʻʻΛ = V . pʻR⃖ʻʻΛ = V
PM-VERBATIM-END PM1:✱40·6 -/
/- PM-VERBATIM-BEGIN PM1:✱40·61
✱40·61. ⊢ : ∃!β .⊃. pʻR⃗ʻʻβ ⊂ Rʻʻβ
PM-VERBATIM-END PM1:✱40·61 -/
/- PM-VERBATIM-BEGIN PM1:✱40·62
✱40·62. ⊢ : ∃!β .⊃. pʻR⃗ʻʻβ ⊂ CʻR . pʻR⃖ʻʻβ ⊂ CʻR
PM-VERBATIM-END PM1:✱40·62 -/
/- PM-VERBATIM-BEGIN PM1:✱40·63
✱40·63. ⊢ : ∃!β − ᗡʻR .⊃. pʻR⃗ʻʻβ = Λ
PM-VERBATIM-END PM1:✱40·63 -/
/- PM-VERBATIM-BEGIN PM1:✱40·64
✱40·64. ⊢ : ∃!β − DʻR .⊃. pʻR⃖ʻʻβ = Λ
PM-VERBATIM-END PM1:✱40·64 -/
/- PM-VERBATIM-BEGIN PM1:✱40·65
✱40·65. ⊢ : ∃!β − CʻR .⊃. pʻR⃗ʻʻβ = Λ . pʻR⃖ʻʻβ = Λ
PM-VERBATIM-END PM1:✱40·65 -/
/- PM-VERBATIM-BEGIN PM1:✱40·66
✱40·66. ⊢. α ⊂ pʻR⃗ʻʻβ .≡: x ∈ α . y ∈ β .⊃_{x,y}. x R y
PM-VERBATIM-END PM1:✱40·66 -/
/- PM-VERBATIM-BEGIN PM1:✱40·67
✱40·67. ⊢. β ⊂ pʻR⃖ʻʻα .≡: x ∈ α . y ∈ β .⊃_{x,y}. x R y .≡. α ⊂ pʻR⃗ʻʻβ
PM-VERBATIM-END PM1:✱40·67 -/
/- PM-VERBATIM-BEGIN PM1:✱40·68
✱40·68. ⊢ : α ⊂ pʻP⃗ʻʻβ .⊃. α ∩ β ⊂ Pʻʻβ
PM-VERBATIM-END PM1:✱40·68 -/
/- PM-VERBATIM-BEGIN PM1:✱40·681
✱40·681. ⊢. α ∩ pʻP⃗ʻʻα ⊂ PʻʻpʻP⃗ʻʻα
PM-VERBATIM-END PM1:✱40·681 -/
/- PM-VERBATIM-BEGIN PM1:✱40·682
✱40·682. ⊢ : ∃!α ∩ pʻP⃖ʻʻβ .⊃. β ⊂ Pʻʻα
PM-VERBATIM-END PM1:✱40·682 -/
/- PM-VERBATIM-BEGIN PM1:✱40·69
✱40·69. ⊢ : ∃!CʻP⃗ ∩ pʻP⃗ʻʻα .≡. ∃!P . ∃!pʻP⃗ʻʻα
PM-VERBATIM-END PM1:✱40·69 -/
/- PM-VERBATIM-BEGIN PM1:✱40·7
✱40·7. ⊢. sʻα♀_{,,}ʻʻβ = ẑ{(∃x,y). x ∈ α . y ∈ β . z = x ♀ y}
PM-VERBATIM-END PM1:✱40·7 -/
/- PM-VERBATIM-BEGIN PM1:✱40·71
✱40·71. ⊢. sʻ♀_{,,}yʻʻκ = (sʻκ)♀_{,,}y = ♀ʻʻsʻκ
PM-VERBATIM-END PM1:✱40·71 -/
/- PM-VERBATIM-BEGIN PM1:✱40·8
✱40·8. ⊢ :. α ∈ κ .⊃_α. Řʻʻα ⊂ α :⊃. Řʻʻsʻκ ⊂ sʻκ
PM-VERBATIM-END PM1:✱40·8 -/
