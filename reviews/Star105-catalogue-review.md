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

Catalogue 02 (·43, ·44) was then audited by the same strict criterion. Item
·43 assumes the complete implication from the first to the second ascending
cardinal equality and returns it unchanged. Item ·44 assumes and returns its
empty-class conclusion, while supplying no representation of PM's `t²`
argument. Both therefore remain `prepared` with explicit pass-through
semantic-mismatch statuses. This lot likewise promotes nothing to
`awaiting-ci`.

The next two prepared source lots, Q430 (·01, ·011, ·02) and Q430b (·021,
·03, ·031), were audited with a maximum of five items per lot. Definitions
·01 and ·011 are exact typed intersection definitions, and ·02 and ·021 are
exact range definitions; these four unique records are promoted to
`awaiting-ci`. Definitions ·03 and ·031 are refused: their Lean declarations
prove only `Inter sm typ = Inter sm typ`, leave the alleged class `m` unused,
and omit both PM's image `smʻʻμ` and the defined operators `μ_(1)`/`μ_(2)`.
They remain `prepared` with explicit semantic-mismatch statuses.
