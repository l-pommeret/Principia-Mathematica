import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱73

The catalogue contains 76 items, of which 74 are assertions.  Similarity is
introduced through classes of one-one relations and immediately uses the
class-valued operations `DʻR`, `ʗʻR`, relation restriction, and relational
image.  `star_20_01` and `star_21_01` correctly represent these abstractions as
contextual incomplete symbols; they do not manufacture standalone class- or
relation-valued `Term`s.

The first asserted use of these definitions ultimately requires the
unconditional one-one theory of ✱71.  That chain is blocked earlier by the
same non-convertible binder indices: ✱20·3 binds
`classSort resultOrder 0`, while the ✱70 relation-class instance binds
`.function [relationSort relationOrder 0] conditionOrder 0`, and the available
generalized replay still assumes `reducibility_scope_transport`.

The similarly named declarations in `Principia.Architecture.Star73*` are
host-language propositions over `A → Prop`; several depend on `propext` and
library automation.  Importing them would neither state PM's printed formulas
nor satisfy the empty-axiom requirement.  Treating similarity and its class
operations as opaque propositional atoms would likewise lose the printed
syntax and is therefore not done here.  No conditional ✱73 assertion is
propagated across the blocked ✱70--✱72 chain.
-/

end PM.RamifiedSyntax
