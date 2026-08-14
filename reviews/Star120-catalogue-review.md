# ✱120 source catalogue review

The fifteen locally transcribed loci are checked against Project Gutenberg
78255 and map uniquely to Lean declarations. This strict audit is deliberately
limited to the first five-item catalogue, ·11, ·12, ·121, ·13, and ·15,
on printed pages 211–212 (scan leaves 251–252). The later ten records remain
`prepared`; the additional source-less ✱120 declarations are not counted.

The module's declared typed reconstruction represents inductive finite
cardinals by `Nat`. Under that contract, ·11 is exactly ordinary induction,
·12 is its zero member, ·121 is closure under `n + 1`, and ·13 is the
restricted-step induction rule. Their theorem statements retain the printed
quantifier order and add no mathematical premise. Those four items pass strict
equivalence and are promoted in place to `awaiting-ci`; no kernel or CI success
is claimed here.

✱120·15 is refused. PM's conclusion is that `smʻʻα`, the cardinal
similar to α at another type, belongs to the inductive cardinals when the
displayed value exists. The Lean declaration instead concludes that
`successor n` is inductive. A cardinal successor is not the printed type-lift,
and the signature does not encode the displayed existence antecedent. The item
therefore stays `prepared` with
`blocked-semantic-mismatch-successor-for-type-lift` evidence.

The printed proof graph is recorded from the displayed Gutenberg brackets and
demonstrations. The four accepted Lean bodies call no numbered proposition;
their Lean graphs are empty, with the omitted historical routes documented as
`relaxed-closure`. The refused item's printed graph is retained but is not
normalized into a false Lean correspondence. The deterministic parser accepts
none of these transfinite-cardinal formulas, so all five keep `reviewed-gap`.
