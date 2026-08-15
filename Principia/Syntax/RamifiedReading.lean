import Principia.Syntax.Printed
import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-- An audited T4 link from PM's diplomatic surface syntax to one claim in the
ramified object calculus. -/
structure RamifiedReading (signature : Signature) (real : Context) where
  printed : PM.PrintedFormula
  parsed : Claim signature real
  scopeReading : String

end PM.RamifiedSyntax
