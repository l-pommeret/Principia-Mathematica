import Principia.Deduction.Star36Derived
import Principia.FirstEdition.Volume1.Star37Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱37 — images of relations

The 138 catalogue items were audited from `Star37Source`.  The eliminable
definition ✱37·01 expands membership in `Rʻʻβ` to
`(∃y). y∈β . xRy`.  Its first asserted consequence, ✱37·1, is printed from
✱20·3 and ✱37·01.  The syntax can represent the expansion, but the current
ramified deduction layer has no derived ✱20·3 theorem eliminating a contextual
class abstraction inside `Derivation`.

This missing conversion is not cosmetic: ✱37·1 is the first step used
throughout the printed image proofs, including repeated and double images
✱37·103 and ✱37·04.  Later propositions additionally cite the unavailable
✱33--✱36 derived relation/class results.  The host-logic image kernels under
`Principia.Architecture` are not PM derivations and are not imported.

Declaring the expanded matrix alone, or assuming the asserted equivalence as a
premise, would change the printed proposition.  Therefore this module contains
no theorem declaration until a pure, kernel-checked ✱20·3 conversion is derived
from the existing eighteen primitives.
-/

end PM.RamifiedSyntax
