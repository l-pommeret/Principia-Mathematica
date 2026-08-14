import Principia.Syntax.Ramified
import Principia.FirstEdition.Volume1.Star40Source

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱40

The source contains 64 asserted catalogue propositions concerning products
and sums of classes of classes.  None can yet be stated and derived honestly
as a `⊢ᵣ` theorem.

The obstruction occurs at the first assertion, ✱40·1.  Its printed proof is
`[✱20·3.(✱40·01)]`: it applies the membership theorem for a class abstraction
to the contextual definition of `pʻκ`.  In `RamifiedSyntax`, however,
`star_20_01` produces `Formula.incompleteScope`; it deliberately does not
produce a class-valued `Term`.  The eighteen primitive constructors of
`Derivation` contain no rule that eliminates this scope or rewrites its
continuation by its matrix.  The identical obstruction affects ✱40·11 and
its definition of `sʻκ`.

Every remaining assertion uses `pʻκ`, `sʻκ`, or later operations built from
them, and the printed demonstrations start from ✱40·1/·11 or from earlier
class theorems that require the same unavailable conversion.  Replacing the
printed class expressions with opaque propositional atoms, host-language
sets, or reflexive surrogates would violate the source and purity contracts.

Consequently this module declares zero `⊢ᵣ` theorems.  The precise missing
derived infrastructure is a kernel-checked elimination/conversion theorem
for `star_20_01` constructed from the existing eighteen primitives; adding a
new primitive constructor is forbidden.
-/

end PM.RamifiedSyntax
