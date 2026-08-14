import Principia.Deduction.Star23Derived
import Principia.FirstEdition.Volume1.Star24Source
import Principia.FirstEdition.Volume1.Star25Source

namespace PM.RamifiedSyntax

/-!
# PM I, ✱25 — relations and existing relations

The catalogue contains 73 items: three eliminable definitions and 70
assertions.  None of the 70 assertions can yet be stated faithfully as a
theorem of `Derivation`.

The universal and null relations of ✱25·01–02 are contextual incomplete
symbols.  `star_21_01` therefore yields an `incompleteScope` formula rather
than a relation-valued `Term`.  The current judgement has no derived rule
that eliminates this scope into relation application or Leibniz identity.
The opening assertion ✱25·1 already needs precisely that passage; the
remaining assertions additionally depend on the unavailable ramified class
and relation operations inherited from ✱22–✱24.

The host-logic relation kernels under `Principia.Architecture` cannot supply
`⊢ᵣ` evidence and are intentionally not imported.  Introducing a
standalone relation constant, Lean equality, or a nineteenth primitive
constructor would violate the purity contract.  Consequently this module
deliberately declares no theorem.  The exact missing prerequisite is a pure
derived elimination theorem for `star_21_01`, after the corresponding class
elimination required by ✱24.
-/

end PM.RamifiedSyntax
