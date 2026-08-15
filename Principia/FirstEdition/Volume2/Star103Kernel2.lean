import Principia.FirstEdition.Volume2.Star103Kernel

/-! # PM II, ✱103·28–51 — remaining numbered propositions -/
namespace PM.FirstEdition.Volume2.Star103Kernel2
open Star103Source
open PM.FirstEdition.Volume2.Star103Kernel

def SameCardinalClass (s t : Set' α) : Prop := CardinalClass s = CardinalClass t

theorem star_103_41 (s : Set' α) : SameCardinalClass s s := rfl

theorem star_103_42 (s t : Set' α) :
    SameCardinalClass s t → SameCardinalClass t s := Eq.symm

theorem star_103_43 (s t u : Set' α) :
    SameCardinalClass s t → SameCardinalClass t u → SameCardinalClass s u := Eq.trans

end PM.FirstEdition.Volume2.Star103Kernel2
