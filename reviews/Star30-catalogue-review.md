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
