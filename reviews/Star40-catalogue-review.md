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

Catalogue-06 strict audit accepts all five of ·27, ·3, ·31, ·32 and ·33. The
typed predicates preserve the intersection/union directions and the family
image quantifiers. The direct Lean proof of ·3 uses ·18 and that of ·31 uses
·171; those edges are now explicit. Their unused ✱37·22 citation is recorded
as a dependency relaxation. Items ·27 and ·32 have no numbered edge; ·33 is
proved directly, with all three unused printed citations recorded explicitly.

Catalogue-07 accepts ·4, ·41, ·43 and ·44. Lean's total typed fibre classes
discharge PM's `E‼` existence guard, and the conclusions retain the complete
sum/product membership or inclusion characterization. Item ·42 is refused:
Lean proves only the endpoint equality between `Forward R a` and the union of
the two forward images, omitting PM's displayed intermediate equality with
`sʻ(Pʻʻα ∪ Qʻʻα)`. The ten-item wave is therefore 9 awaiting CI and one
documented refusal, in disjoint manifests with unique IDs.

Catalogues 10–11 strict audit promotes eight of ten items. In catalogue 10,
·6, ·61, ·63 and ·64 preserve the complete typed product, nonemptiness and
empty-class statements. Item ·62 is refused: PM places both products inside
the same field `CʻR`, while Lean substitutes two distinct domain predicates
and supplies no common field target. In catalogue 11, ·65, ·66, ·68 and ·681
are exact. Item ·67 is refused because PM states a three-member chained
equivalence and Lean omits its final `α ⊂ pʻR⃗ʻʻβ` member. The result is eight
awaiting CI and two prepared refusals in four homogeneous, disjoint manifests.
