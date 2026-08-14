# ✱51 source catalogue review

The fifty-two items are checked against Project Gutenberg 78050 on printed
pages 357–362 (scan leaves 379–384) and resolve uniquely to existing numbered
Lean declarations.  They remain `prepared` pending semantic promotion.

## Opening semantic audit

The five opening items ✱51·01, ·1, ·11, ·12, and ·13 were checked
individually against their typed Lean declarations. The relation `ι`, its
descriptive value, and the displayed singleton abstraction agree extensionally.
The former ·12 declaration incorrectly read PM's `E!ιʻx` as inhabitation of the
unit class; it now asserts existence of the class-valued descriptive-function
value itself. All five statements are exact and are promoted to `awaiting-ci`.

The next five items ✱51·131, ·14, ·141, ·15, and ·16 were likewise
audited statement by statement. Here PM's `∃!α` is the established
existence-of-class notation, represented by `ClassExists A`; the adjacent
universal implication supplies uniqueness of the member, not uniqueness of a
class witness. The Lean conjunction in ·141 preserves both printed
equivalences and all scopes. These five items are exact and promoted to
`awaiting-ci`.

Catalogue 04 (✱51·22, ·221, ·222, ·23, ·231) was checked against
the complete Lean proposition types and proof bodies. The conjunctions in
·22 preserve both printed hypotheses and conclusions; ·23 represents the
entire four-term equivalence chain as three adjacent equivalences, rather than
selecting one endpoint. Deletion, restoration, disjointness, and equality all
retain the printed direction and quantifier scope. No item is refused; all
five are promoted to `awaiting-ci`.

Catalogue 03 (✱51·161, ·17, ·2, ·21, ·211) is also exact in the
typed reconstruction. In ·161, `∃!ιʻx` again denotes existence of the
unit class (and is therefore correctly `ClassExists`), whereas ·17 quantifies
the class witness in the converse domain. The inclusion, difference, and
intersection statements preserve their printed orientations and both sides of
each equivalence. No item in this lot is refused; all five are promoted to
`awaiting-ci`.

The Gutenberg heading `*51.161` uses a full stop where the numbered series and
printed scan require the ordinary middle dot; the canonical ID is therefore
✱51·161 while the formula itself is unchanged.

Fifteen formulas use class binders such as `ŷ`, decorated unit-class
relations, or incomplete-symbol contexts beyond the current parser grammar.
They carry `reviewed-gap`; the remaining items are parsed directly.
