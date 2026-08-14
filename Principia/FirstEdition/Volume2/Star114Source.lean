/-! # PM II, ✱114 source ledger

Project Gutenberg ebook 78255, section ✱114, cardinal products.
-/

/- PM-VERBATIM-BEGIN PM2:✱114·01
✱114·01. ΠNcʻκ = Ncʻ∈Δʻκ Df
PM-VERBATIM-END PM2:✱114·01 -/

/- PM-VERBATIM-BEGIN PM2:✱114·1
✱114·1. ⊢ . ΠNcʻκ = Ncʻ∈Δʻκ [(✱114·01)]
PM-VERBATIM-END PM2:✱114·1 -/

/- PM-VERBATIM-BEGIN PM2:✱114·11
✱114·11. ⊢ : β∈ΠNcʻκ .≡. β sm ∈Δʻκ .≡. β∈Ncʻ∈Δʻκ [✱114·1.✱100·31]
PM-VERBATIM-END PM2:✱114·11 -/

/- PM-VERBATIM-BEGIN PM2:✱114·12
✱114·12. ⊢ . ∈Δʻκ∈ΠNcʻκ [✱100·3.✱114·1]
PM-VERBATIM-END PM2:✱114·12 -/

/- PM-VERBATIM-BEGIN PM2:✱114·2
✱114·2. ⊢ . ΠNcʻΛ = 1 [✱83·15.✱101·2]
PM-VERBATIM-END PM2:✱114·2 -/

/- PM-VERBATIM-BEGIN PM2:✱114·21
✱114·21. ⊢ . ΠNcʻιʻα = Ncʻα [✱83·41]
PM-VERBATIM-END PM2:✱114·21 -/

/- PM-VERBATIM-BEGIN PM2:✱114·22
✱114·22. ⊢ . ΠNcʻιʻΛ = 0 [✱114·21.✱101·1]
PM-VERBATIM-END PM2:✱114·22 -/

/- PM-VERBATIM-BEGIN PM2:✱114·23
✱114·23. ⊢ : Λ∈κ .⊃. ΠNcʻκ = 0 [✱83·11.✱101·1]
PM-VERBATIM-END PM2:✱114·23 -/

/- PM-VERBATIM-BEGIN PM2:✱114·24
✱114·24. ⊢ : ΠNcʻλ ≠ 0 . κ⊂λ .⊃. ΠNcʻκ ≠ 0
PM-VERBATIM-END PM2:✱114·24 -/

/- PM-VERBATIM-BEGIN PM2:✱114·25
✱114·25. ⊢ :: Mult ax .≡: ΠNcʻκ = 0 .⊃κ. Λ∈κ
PM-VERBATIM-END PM2:✱114·25 -/

/- PM-VERBATIM-BEGIN PM2:✱114·26
✱114·26. ⊢ :: Mult ax .≡: ΠNcʻκ = 0 .≡κ. Λ∈κ [✱88·372.✱101·1]
PM-VERBATIM-END PM2:✱114·26 -/

/- PM-VERBATIM-BEGIN PM2:✱114·261
✱114·261. ⊢ :: Mult ax .≡: ΠNcʻκ = 0 .≡κ. 0∈Ncʻʻκ [✱114·26.✱101·1]
PM-VERBATIM-END PM2:✱114·261 -/

/- PM-VERBATIM-BEGIN PM2:✱114·27
✱114·27. ⊢ ::: Mult ax .≡:: α∈κ .⊃α. ∃!α :≡κ. ΠNcʻκ ≠ 0
PM-VERBATIM-END PM2:✱114·27 -/

/- PM-VERBATIM-BEGIN PM2:✱114·3
✱114·3. ⊢ : κ≠λ .⊃. ∈Δʻ(ιʻ∈Δʻκ ∪ ιʻ∈Δʻλ) sm ∈Δʻκ × ∈Δʻλ
PM-VERBATIM-END PM2:✱114·3 -/

/- PM-VERBATIM-BEGIN PM2:✱114·301
✱114·301. ⊢ : κ∩λ = Λ .⊃. ∈Δʻ(κ∪λ) sm ∈Δʻκ × ∈Δʻλ
PM-VERBATIM-END PM2:✱114·301 -/

/- PM-VERBATIM-BEGIN PM2:✱114·31
✱114·31. ⊢ : κ∩λ = Λ .⊃. ΠNcʻκ ×c ΠNcʻλ = ΠNcʻ(κ∪λ) [✱114·301·1.✱113·25]
PM-VERBATIM-END PM2:✱114·31 -/

/- PM-VERBATIM-BEGIN PM2:✱114·311
✱114·311. ⊢ . ΠNcʻ(κ∪λ) = ΠNcʻκ ×c ΠNcʻ(λ−κ) [✱114·31.✱22·91]
PM-VERBATIM-END PM2:✱114·311 -/

/- PM-VERBATIM-BEGIN PM2:✱114·32
✱114·32. ⊢ : ΠNcʻ(κ∪λ) ≠ 0 .≡. ΠNcʻκ ≠ 0 . ΠNcʻλ ≠ 0
PM-VERBATIM-END PM2:✱114·32 -/

/- PM-VERBATIM-BEGIN PM2:✱114·33
✱114·33. ⊢ : α∼∈κ .⊃. ΠNcʻ(κ∪ιʻα) = ΠNcʻκ ×c Ncʻα [✱114·31·21]
PM-VERBATIM-END PM2:✱114·33 -/

/- PM-VERBATIM-BEGIN PM2:✱114·34
✱114·34. ⊢ : ΠNcʻκ ≠ 0 . ∃!α .≡. ΠNcʻ(κ∪ιʻα) ≠ 0 [✱114·32·21.✱101·14]
PM-VERBATIM-END PM2:✱114·34 -/

namespace PM.FirstEdition.Volume2.Star114Source
def gutenbergId : Nat := 78255
def openingLoci : List String :=
  ["114·01", "114·1", "114·11", "114·12", "114·2", "114·21", "114·22",
   "114·23", "114·24", "114·25", "114·26", "114·261", "114·27", "114·3",
   "114·301", "114·31", "114·311", "114·32"]
def sourceSummary : String :=
  "Definition and elementary laws of ΠNc, null factors, the multiplicative principle, and products over unions."
end PM.FirstEdition.Volume2.Star114Source
