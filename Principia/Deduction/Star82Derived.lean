import Principia.Deduction.Star63Derived
import Principia.FirstEdition.Volume1.Star82Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱82

All thirty-two assertions depend on object-language selection and relational
composition.  Neither operation has a reducible construction in
`RamifiedSyntax`, and ✱81 supplies no `⊢ᵣ` theorem because the required class
and relation definition-conversion layer is absent.  The `Star82Kernel`
results are statements in Lean's `Prop`, not values of `Derivation`, and some
also use host equality and extensionality.  They cannot certify PM assertions.

No theorem is declared until the missing object-calculus definitions and
their derived conversion theorems exist.
-/

end PM.RamifiedSyntax
