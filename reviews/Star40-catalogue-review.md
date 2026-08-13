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
