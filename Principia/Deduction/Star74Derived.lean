import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱74

All 86 catalogue items are assertions.  Their formulas require the same
unavailable object-calculus conversion layer as ✱73, now also for restrictions,
images, converse images, domains, converse domains, and one-one relation
classes.  The repository has no `Star74Source.lean`; the diplomatic text is
currently distributed among the 18 `metadata/items/PM1-star-74-catalogue-*`
records.  Those records are sufficient to audit the obstruction, but are not
an importable object-syntax implementation.

`Principia.Architecture.Star74Kernel` is deliberately not imported: it defines
sets as Lean predicates and proves Lean `Prop` statements, so it cannot supply
evidence for `PM.RamifiedSyntax.Derivation`.  Until the contextual definitions
used by the printed statements have pure derived conversion theorems, no exact
`⊢ᵣ` declaration is available.
-/

end PM.RamifiedSyntax
