# ✱105 source catalogue review

The five former range blocks are split into eighty-eight unique item blocks,
checked against Project Gutenberg 78255 on printed pages 53–59 (scan leaves
93–99). All 88 IDs resolve to Lean declarations. Eighty-one legacy source-only
records are upgraded in place; seven previously missing records are added in
small catalogue batches. Every item remains `prepared` pending semantic audit.

The parser accepts 73 formulas; 15 ascending-cardinal formulas carry `reviewed-gap`.

Catalogue 01 (·3, ·322, ·4, ·41, ·42) was audited strictly source-to-Lean.
None is eligible for promotion. In ·3 and ·4, Lean assumes the displayed
conclusion as an extra parameter and returns that parameter unchanged; ·3 also
leaves `N0` unused and replaces the printed antecedent by an unrelated carrier
equality. In ·322, Lean assumes and returns the whole biconditional while
omitting the printed uniqueness/existence condition. Items ·41 and ·42 likewise
assume their complete implications and return them unchanged; ·41 additionally
replaces PM's cardinal-existence propositions by arbitrary propositions.
Accordingly all five remain `prepared`, with explicit semantic-mismatch
integration statuses. There is no `awaiting-ci` promotion in this lot.
