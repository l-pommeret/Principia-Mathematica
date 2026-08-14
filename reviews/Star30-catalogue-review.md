# ✱30 source catalogue review

The fifteen items in `PM1-STAR30-CATALOGUE-{1,2,3}` are diplomatic
transcriptions of the `data-tex` readings in Project Gutenberg 78050,
checked against printed pages 248–249 (scan leaves 270–271).  Their existing
Lean declarations are recorded as candidates, not promoted as semantically
audited proofs.

The deterministic PM parser currently consumes normalized Unicode PM syntax.
These blocks deliberately retain raw TeX delimiters and commands such as
`\(`, `\vdash`, `\colon`, and `\supset`; therefore their parser route is the
explicit `reviewed-gap` classification rather than a lossy rewrite of the
diplomatic bytes.

Catalogue batches 4–6 add the fourteen canonically transcribed final propositions
✱30·32–·52 (at most five per file). Their Lean declarations were semantically
audited, contain no pass-through certificates, and are synchronized as
`awaiting-ci`; CI evidence remains pending.

## Catalogues 1 and 2 strict semantic audit

Catalogue 1 accepts ✱30·12, ·13, ·141, and ·142.  Their `Scope` targets retain
the printed existence antecedent and respectively distribute disjunction,
negation, implication to a constant consequent, and equivalence through the
contextual description.  Each is promoted in the homogeneous awaiting-CI
sidecar.  ✱30·14 is refused and remains alone in the prepared catalogue: PM
prints distribution of `p ⊃ χ(Rʻy)`, but `star_30_14` proves distribution of
the conjunction `p ∧ φ`.  This connective substitution is substantive even
though the Lean proof itself is valid.

All five catalogue-2 items pass.  ✱30·15 distributes the constant conjunction;
·16 commutes the two independent scopes; ·17 is their exact two-witness
expansion; ·18 instantiates a universally true matrix at the existent described
value; and ·19 performs substitution under identity with that value.  The
contextual `Scope` representation introduces no arbitrary description-valued
term and drops no existence or uniqueness condition.  These five are promoted
in place to `awaiting-ci`.

The ten printed ✱14 citations are retained as historical edges.  The Lean
bodies instead expand `Scope` and use only the local uniqueness lemma, so the
accepted records carry explicit `relaxed-closure` evidence and empty Lean and
normalized numbered-proposition graphs.  The split partitions all ten IDs;
none is duplicated.
