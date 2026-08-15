/-! PM II ✱117, canonical Gutenberg 78255, first audited catalogue. -/
/- PM-VERBATIM-BEGIN PM2:✱117·01
✱117·01. μ > ν .=. (∃α,β). μ=N₀cʻα . ν=N₀cʻβ . ∃!Clʻα∩Ncʻβ . ∼∃!Clʻβ∩Ncʻα Df
PM-VERBATIM-END PM2:✱117·01 -/
/- PM-VERBATIM-BEGIN PM2:✱117·05
✱117·05. μ ≥ ν .=: μ > ν .∨. μ,ν∈N₀C . μ=smʻʻν Df
PM-VERBATIM-END PM2:✱117·05 -/
/- PM-VERBATIM-BEGIN PM2:✱117·103
✱117·103. ⊢ : μ < ν .≡. ν > μ
PM-VERBATIM-END PM2:✱117·103 -/
/- PM-VERBATIM-BEGIN PM2:✱117·105
✱117·105. ⊢ : μ ≤ ν .≡. ν ≥ μ [(✱117·06)]
PM-VERBATIM-END PM2:✱117·105 -/
/- PM-VERBATIM-BEGIN PM2:✱117·221
✱117·221. ⊢ : Ncʻα ≥ Ncʻβ .≡. (∃ρ). ρ⊂α . ρ sm β
PM-VERBATIM-END PM2:✱117·221 -/
/- PM-VERBATIM-BEGIN PM2:✱117·222
✱117·222. ⊢ : β⊂α .⊃. Ncʻα ≥ Ncʻβ
PM-VERBATIM-END PM2:✱117·222 -/
/- PM-VERBATIM-BEGIN PM2:✱117·23
✱117·23. ⊢ : Ncʻα ≥ Ncʻβ . Ncʻβ ≥ Ncʻα .≡. Ncʻα=Ncʻβ
PM-VERBATIM-END PM2:✱117·23 -/
/- PM-VERBATIM-BEGIN PM2:✱117·24
✱117·24. ⊢ : μ ≥ ν .≡. (∃α,β). μ=N₀cʻα . ν=N₀cʻβ . Ncʻα ≥ Ncʻβ
PM-VERBATIM-END PM2:✱117·24 -/
/- PM-VERBATIM-BEGIN PM2:✱117·241
✱117·241. ⊢ : μ ≥ ν .≡. (∃α,β). μ=N₀cʻα . ν=N₀cʻβ . ∃!Clʻα∩Ncʻβ
PM-VERBATIM-END PM2:✱117·241 -/
/- PM-VERBATIM-BEGIN PM2:✱117·242
✱117·242. ⊢ :: μ,ν∈NC .⊃: μ ≥ ν .≡. (∃α,β). α∈μ . β∈ν . ∃!Clʻα∩Ncʻβ
PM-VERBATIM-END PM2:✱117·242 -/
/- PM-VERBATIM-BEGIN PM2:✱117·243
✱117·243. ⊢ :: μ ≥ ν .≡: (∃α,β): μ=N₀cʻα . ν=N₀cʻβ : (∃ρ). ρ⊂α . ρ sm β
PM-VERBATIM-END PM2:✱117·243 -/
namespace PM.FirstEdition.Volume2.Star117Source
def records : List (String × String) := [
  ("✱117·01", "μ > ν .=. (∃α,β). μ=N₀cʻα . ν=N₀cʻβ . ∃!Clʻα∩Ncʻβ . ∼∃!Clʻβ∩Ncʻα  Df"),
  ("✱117·05", "μ ≥ ν .=: μ > ν .∨. μ,ν∈N₀C . μ=smʻʻν  Df"),
  ("✱117·103", "⊢ : μ < ν .≡. ν > μ"),
  ("✱117·105", "⊢ : μ ≤ ν .≡. ν ≥ μ"),
  ("✱117·221", "⊢ : Ncʻα ≥ Ncʻβ .≡. (∃ρ). ρ⊂α . ρ sm β"),
  ("✱117·222", "⊢ : β⊂α .⊃. Ncʻα ≥ Ncʻβ")]
end PM.FirstEdition.Volume2.Star117Source
