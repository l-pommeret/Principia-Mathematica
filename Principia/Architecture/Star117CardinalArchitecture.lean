import Principia.FirstEdition.Volume2.Star103Kernel

namespace PM.Architecture.Star117CardinalArchitecture
open PM.FirstEdition.Volume2.Star103Source

def Included (A B : Set' α) := ∀ {x}, A x → B x
def Embeddable (A B : Set' α) := ∃ C, Included C A ∧ Equinumerous C B
def StrictlyLarger (A B : Set' α) := Embeddable A B ∧ ¬ Embeddable B A
def AtLeast (A B : Set' α) := StrictlyLarger A B ∨ Equinumerous A B
def StrictlySmaller (A B : Set' α) := StrictlyLarger B A
def AtMost (A B : Set' α) := AtLeast B A

theorem strictlyLarger_irrefl : ¬ StrictlyLarger A A := fun h => h.2 h.1
theorem strictlyLarger_asymm : StrictlyLarger A B → ¬ StrictlyLarger B A := fun h k => h.2 k.1
theorem smaller_iff_larger : StrictlySmaller A B ↔ StrictlyLarger B A := Iff.rfl
theorem atMost_iff_atLeast : AtMost A B ↔ AtLeast B A := Iff.rfl

end PM.Architecture.Star117CardinalArchitecture
