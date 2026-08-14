# ✱40 source catalogue review

The sixty numbered blocks are transcribed from Project Gutenberg 78050 and
located against the bold proposition headings on printed pages 320–330
(first-edition scan leaves 342–352).  Each source ID resolves uniquely to an
existing Lean declaration.

## Exact opening audit (15 items)

`PM1:✱40·01` through `PM1:✱40·22` in catalogue batches 01–03 were checked
item by item against the diplomatic statements and the declarations in
`Star40OpeningKernel.lean` and `Star40SecondKernel.lean`.  In the typed
class-as-predicate reconstruction, `Product`, `Sum`, class/family inclusion,
intersection, union, empty class, and universal class have exactly the
membership conditions printed by PM.  All fifteen declarations prove the
whole displayed proposition with the same quantifier direction and inclusion
orientation; none adds a mathematical hypothesis or drops a case.

The Lean proofs use direct definitional or extensional reasoning rather than
replaying every historical citation.  This is a dependency-level relaxation,
not a statement-level weakening.  These fifteen items are therefore promoted
to `awaiting-ci`; the remaining ✱40 catalogue stays `prepared` pending its own
item-level audit.

The Unicode PM parser accepts the ordinary membership, inclusion, product,
and sum formulas in this catalogue.  Thirty-two formulas additionally use
printed constructs not yet in its grammar: explicit scope subscripts,
relation-image arrows, the `‼` product operator, and the printed `♀`
construction.  Those items carry an explicit `reviewed-gap`; their diplomatic
source bytes are not normalized away.

Catalogue-03 strict re-audit confirms ✱40·16, ·161, ·17, ·171 and ·18 as
exact typed family-inclusion/product/sum endpoints. Their proofs are direct
from definitions and introduce no historical theorem dependency. These five
records were already `kernel-checked`, so no status mutation was appropriate.

Catalogue-04 strict audit accepts ✱40·181, ·19, ·2, ·21 and ·22. The first and
last three close directly from the typed family definitions. ✱40·19 uses the
earlier upper-bound characterization ✱40·13, recorded in all three dependency
fields. All five are therefore `awaiting-ci`; no refusal was necessary.

Catalogue-05 strict audit accepts ✱40·221, ·23, ·24, ·25 and ·26. They are
direct typed expansions of universal membership, product-to-sum inclusion,
lower-bound inclusion, membership in a family sum, and existence in a sum.
All close from definitions without a Lean or historical theorem edge and are
`awaiting-ci`; no refusal was necessary.
