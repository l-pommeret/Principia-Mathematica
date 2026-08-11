import Principia.Deduction.Formation
import Principia.Deduction.System

namespace PM

/-- An assertion paired with its independent PM formation evidence. -/
structure FormedDerivation {Γ : RealContext} (p : Elementary Γ) : Prop where
  formation : Formation p
  derivation : Derivation p

end PM
