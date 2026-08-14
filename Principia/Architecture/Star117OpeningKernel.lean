import Principia.Architecture.Star117CardinalArchitecture
import Principia.FirstEdition.Volume2.Star117Source

namespace PM.Architecture.Star117OpeningKernel
open PM.FirstEdition.Volume2.Star103Source
open PM.Architecture.Star117CardinalArchitecture

/-- ✱117·01. `μ > ν .=. (∃α,β). μ=N₀cʻα . ν=N₀cʻβ . ∃!Clʻα∩Ncʻβ . ∼∃!Clʻβ∩Ncʻα Df`. -/
def star_117_01 (A B : Set' α) : Prop := Embeddable A B ∧ ¬ Embeddable B A
/-- ✱117·05. `μ ≥ ν .=: μ > ν .∨. μ,ν∈N₀C . μ=smʻʻν Df`. -/
def star_117_05 (A B : Set' α) : Prop := StrictlyLarger A B ∨ Equinumerous A B
theorem star_117_103 : StrictlySmaller A B ↔ StrictlyLarger B A := Iff.rfl
theorem star_117_105 : AtMost A B ↔ AtLeast B A := Iff.rfl
end PM.Architecture.Star117OpeningKernel
