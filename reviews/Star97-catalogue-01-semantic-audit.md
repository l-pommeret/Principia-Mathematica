# ✱97 catalogue 01 — strict source/Lean semantic audit

Scope: the first five loci on PM I p. 656 (1910 scan leaf 678), checked
against both the first-edition scan and Project Gutenberg 78050.  Promotion is
strict: theorem names and broad subject matter are not evidence of equivalence.

| PM locus | Lean declaration | verdict | reason |
|---|---|---|---|
| ✱97·01 | `star_97_01` | exact, awaiting CI | The pointwise `family` equation is precisely the union of the converse fibre, the singleton guarded by the field, and the direct fibre. |
| ✱97·1 | `star_97_1` | exact, awaiting CI | Lean unfolds the same three membership alternatives, with the same relation orientations and field guard. |
| ✱97·101 | `star_97_101` | exact, awaiting CI | Both sides are exactly membership in the generated neighbourhood with the two points exchanged. |
| ✱97·11 | `star_97_11` | refused | PM gives the class equality `sʻR↔ʻʻCʻR = CʻR`; Lean supplies only `family R x y → field R y`, i.e. one pointwise inclusion, with no converse witness. |
| ✱97·111 | `star_97_111` | refused | PM has a three-way equivalence and includes existence/non-emptiness of `R↔ʻx`; Lean stops after `field R x ↔ family R x x`. |

The promoted set is therefore exactly 3/5.  The two refused loci remain
`prepared` and cannot count toward source-critical coverage.  No proposition ID
is duplicated between the awaiting-CI and refused manifests.

Dependency note: the three promoted Lean declarations are self-contained at
the theorem-declaration level (`Iff.rfl` or a direct propositional proof), so
their extracted and normalized dependency graphs are empty.  No historical
dependency relaxation is claimed.
