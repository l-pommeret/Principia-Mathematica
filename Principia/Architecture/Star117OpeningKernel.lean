import Principia.Architecture.Star117CardinalArchitecture
import Principia.FirstEdition.Volume2.Star117Source

namespace PM.Architecture.Star117OpeningKernel
open PM.FirstEdition.Volume2.Star103Source
open PM.Architecture.Star117CardinalArchitecture

theorem star_117_01 : StrictlyLarger A B ↔ Embeddable A B ∧ ¬ Embeddable B A := Iff.rfl
theorem star_117_05 : AtLeast A B ↔ StrictlyLarger A B ∨ Equinumerous A B := Iff.rfl
theorem star_117_103 : StrictlySmaller A B ↔ StrictlyLarger B A := Iff.rfl
theorem star_117_105 : AtMost A B ↔ AtLeast B A := Iff.rfl
end PM.Architecture.Star117OpeningKernel
