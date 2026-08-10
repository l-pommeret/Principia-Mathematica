import Principia.Syntax.Formula

namespace PM

/-- Diplomatic surface syntax of a printed PM formula. The string preserves
assertion signs, scope dots, spacing conventions, and metasymbols. -/
structure PrintedFormula where
  source : String
  deriving DecidableEq, Repr

/-- Mark a string as diplomatic PM surface syntax. -/
def pmPrinted (source : String) : PrintedFormula := ⟨source⟩

/-- An audited link from printed syntax to an elementary expression. -/
structure ElementaryReading (Γ : RealContext) where
  printed : PrintedFormula
  parsed : Elementary Γ
  scopeReading : String
  deriving Repr

end PM
