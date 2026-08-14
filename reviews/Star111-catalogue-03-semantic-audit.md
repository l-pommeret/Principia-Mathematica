# ✱111 catalogue 03 — strict source/Lean semantic audit

Scope: the next five as-yet-unpromoted loci in the source order on PM II
pp. 88–89, checked against the diplomatic `verbatimStatements` catalogue and
the typed declarations in `Star111Kernel.lean`. Promotion is strict: a shared
theorem number or vocabulary is not evidence of source equivalence.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱111·01 | `star_111_01` | exact typed definition, awaiting CI | `DoubleSimilar κ lam` unfolds to the existence of one bijective class map `F` carrying membership in `κ` exactly to membership in `lam`; the theorem exposes precisely those conjuncts rather than replacing them by a consequence. |
| ✱111·02 | `star_111_02` | exact typed definition, awaiting CI | `Corresponds F b` unfolds exactly to similarity of the correlated class `F b` and `b`, matching the defining equation for `Crp(S)ʻβ`. |
| ✱111·1 | `star_111_1` | refused | PM characterizes membership of a specified `T` in `κ sm sm λ` by one-one-ness, the range condition, and the image equation. Lean proves only `DoubleSimilar κ lam ↔ DoubleSimilar κ lam`; it has no specified `T` and exposes none of the three defining components. |
| ✱111·12 | `star_111_12` | refused | PM states that restricting `T` to any superclass of `sʻλ` preserves the inverse image of `λ`. Lean instead characterizes membership in `a` through a chosen preimage of an unrelated globally bijective function; neither restriction nor the superclass premise occurs. |
| ✱111·121 | `star_111_121` | refused | PM specializes the preceding restriction identity to `T↾sʻλ`. Lean merely returns its assumption `Bijective F`; it contains no restriction, image, inverse, or equality. |

The promoted set is therefore exactly 2/5. The two accepted declarations are
definitional (`Iff.rfl`) and have empty theorem-dependency graphs. The three
refused candidates remain prepared and cannot contribute to source-critical
coverage. No proposition ID occurs in both manifests.

This verdict concerns equivalence to the project's established typed reading:
it does not identify PM's ramified class notation with unrestricted Lean sets
beyond that declared interpretation boundary.
