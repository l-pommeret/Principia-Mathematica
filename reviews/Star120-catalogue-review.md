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

## Catalogue 02 strict audit

The next five prepared records are audited independently. ✱120·151 is the
typed successor-closure theorem; totality of `Nat` discharges the printed
existence guard. ✱120·21 normalizes the cardinal criterion for an inductive
class to an explicit finite enumeration, and ✱120·212 supplies the empty
enumeration. These three statements preserve the source claims and are moved
to the homogeneous `awaiting-ci` lot.

✱120·152 is refused because the source transports nonzero inductive-cardinal
membership backward across the type-lift `smʻʻ`, whereas Lean assumes
inductivity of `successor n` and concludes a weakened disjunction about `n`.
✱120·211 is also refused: its Lean premise already contains `finiteClass A`,
the exact conclusion projected by the proof, and it omits `Ncʻρ` entirely.
Both remain `prepared` in a separate homogeneous refused lot.

The printed dependencies are extracted proposition by proposition from the
displayed Gutenberg demonstrations. The three accepted Lean bodies invoke no
numbered theorem, so their empty Lean graphs and historical relaxed closures
are explicit. Every catalogue-02 ID occurs in exactly one split artifact.

## Catalogues 03 and 04 strict audit

Catalogue 03 accepts only ·213 (singleton enumeration) and ·251 (adjoining
one member). It refuses ·214 because equality replaces similarity, ·26 because
the generalized conclusion is assumed as `finiteInduction`, and ·311 because
successor injectivity omits `smʻʻ` and the existence assertions.

The next five loci (·322, ·41, ·411, ·4111, ·412) are transcribed in
`Star120NextSource`. None passes strict audit: their targets omit an existence
biconditional, type transport and guards, cardinal-difference membership, or
the printed class-of-witnesses identity. They form one homogeneous refused lot.
