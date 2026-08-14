import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star32Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱32

The four printed definitions ✱32·01--·04 use contextual class and relation
abstractions.  Their first asserted eliminations, ✱32·1 and ✱32·101, require
the unavailable ramified ✱21·3 rule; ✱32·11 and ✱32·111 then require the
unavailable descriptive-function result ✱30·3.  Thus the apparent direct
uses of ✱14·21 at ✱32·12, ·121, ·22, and ·221 cannot be reached merely by
declaring that ✱14 theorem as an explicit hypothesis: each also consumes an
earlier underived ✱32 equality.

All later propositions depend on these openings or need the same absent
elimination rules for contextual abstractions, PM identity, membership, and
descriptions.  The secondary `Prop` kernels in `Principia.Architecture` are
not derivations in `PM.RamifiedSyntax` and cannot be imported as certificates.

Accordingly this module contains no theorem declaration.  No formula is
weakened, no same-typed premise is passed through as a vacuous proof, and no
new primitive is added.
-/

end PM.RamifiedSyntax
