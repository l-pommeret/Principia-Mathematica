import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱74

All 86 catalogue items are assertions.  Their formulas require the same
blocked unconditional chain as ✱73, now also for restrictions, images,
converse images, domains, converse domains, and one-one relation classes.  The
PM-verbatim blocks for this chapter are appended to
`Principia/Architecture/Star74Kernel.lean`; there is no separate
`FirstEdition/Volume1/Star74Source.lean` module.

The first assertion ✱74·1 cites ✱71·55, and later assertions repeatedly
cite ✱72 and ✱73.  These cannot be supplied as unconditional `Derivation`
values while the ✱70·1 relation-class instance is conditional.  Concretely,
the required `.sometimes` binder carries
`.function [relationSort relationOrder 0] conditionOrder 0`, whereas the
available ✱20·3 theorem carries `classSort resultOrder 0`; the constructor
indices do not reduce to one another.

`Principia.Architecture.Star74Kernel` is deliberately not imported: it defines
sets as Lean predicates and proves Lean `Prop` statements, so it cannot supply
evidence for `PM.RamifiedSyntax.Derivation`.  Until the contextual definitions
used by the printed statements have an unconditional pure elimination proof,
no exact `⊢ᵣ` declaration is available.
-/

end PM.RamifiedSyntax
