import Principia.Syntax.Ramified

namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱73

The catalogue contains 76 items, of which 74 are assertions.  None can yet be
declared as an exact `⊢ᵣ` theorem.  Similarity is introduced through classes of
one-one relations and immediately uses the class-valued operations `DʻR`, `ʗʻR`,
relation restriction, and relational image.  `star_20_01` and `star_21_01`
correctly represent class and relation abstractions as contextual incomplete
symbols; they do not manufacture class- or relation-valued `Term`s.  The
current `Derivation` API has no derived definition-conversion theorem that
eliminates either contextual node inside an assertion.

The similarly named declarations in `Principia.Architecture.Star73*` are
host-language propositions over `A → Prop`; several depend on `propext` and
library automation.  Importing them would neither state PM's printed formulas
nor satisfy the empty-axiom requirement.  Treating similarity and its class
operations as opaque propositional atoms would likewise lose the printed
syntax and is therefore not done here.
-/

end PM.RamifiedSyntax
