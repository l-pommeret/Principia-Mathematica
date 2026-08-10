# Audit Q252 retry 01 — terminal error and repository-context mismatch

Final verdict: **A — accepted, awaiting repository CI**. Confidence: high.

The B diagnosis below records why the first terminal task required a
same-project continuation. The final retry result is audited in the last
section.

## Evidence inspected

- Original request: `aristotle/Q252.md`.
- Original audit: `reviews/Q252-review.md`.
- Current repository API: `Principia/Syntax/Apparent.lean`, SHA-256
  `781387ff47f160b546d91106d5bf9afe5750735aec49ccb58bcf28501d4e069b`;
  its direct dependency `Principia/Syntax/Formula.lean` has SHA-256
  `4ae57f04fe68659b5afc75e7edf065a229ca1b68ef7ada719797c5011240bb8d`.
- Immutable archive: `aristotle/results/Q252-final.tar.gz`, SHA-256
  `a59ab1b65bd38ba13c7095a7ea13d999253b85437d3da99d1f234ada977c866a`.
  All 11 archive entries were inspected.
- Remote project status and all task events for task
  `0f7e984b-0eec-4af6-af8f-671ac5cfcc56`: terminal
  `COMPLETE_WITH_ERRORS`.

## Exact failure

The task event stream contains one `ERROR` event,
`34ed18cf-7134-4bab-8a5e-41f296661faf`:

`Failed: Writing /workspace/request-project/Principia/Syntax/Apparent.lean`

The event lasted 0.2 seconds. No Lean compiler diagnostic or failed theorem
is recorded. The task recovered, subsequently wrote that path, invoked
`lake build Principia`, and ran disposable `rfl` checks. Its final summary
claims the build and checks succeeded. The terminal error label therefore
tracks the failed first file-write event, not an identified failure of any
of the four declarations.

There is, however, a decisive compiler-context mismatch. The successful
checks were performed against a replacement syntax file invented inside the
empty request project. That file defines `Index`, `RealSort`,
`ApparentSort`, `Argument`, and an incompatible `Apparent`. The accepted
repository API instead imports `Principia.Syntax.Formula` and defines the
architecture in terms of `RealType`, `RealVar`, `BoundVar`, capture-safe
renaming/substitution, and the existing `Quantified`/`FirstOrder` layer.
The original prompt explicitly forbade reconstructing or replacing this
architecture. Consequently, the remote compiler checked the right four
definitions against the wrong foundation.

## Valid work preserved

`Principia/FirstEdition/Volume1/Star9.lean` in the archive preserves the
diplomatic source comment and contains the requested four `abbrev`
declarations with their bodies exactly as specified. Static inspection also
found no `sorry`, `admit`, new axiom, `unsafe`, or `@[implemented_by]` in the
returned Lean sources. The four abbreviations are the reusable result;
the invented `Principia/Syntax/Apparent.lean` is not reusable and must be
replaced rather than merged.

## Continuation decision

`aristotle/followups/Q252-retry-01.md` is a standalone staged continuation
for the existing project. It embeds the authoritative current
`Formula.lean` and `Apparent.lean`, requires full replacement of the invented
foundation, preserves the exact Star9 bodies, and demands remote compilation
plus explicit `rfl` reduction checks. It neither widens nor narrows the
canonical target and forbids placeholders, axioms, unsafe declarations, and
other escape hatches.

During that preparatory audit, no continuation was submitted, no local Lean
command was run, and no commit or push was performed.

## Retry result audit

Same Aristotle project `118e4b43-2dc7-4e58-a81d-efe890562749`, retry task
`44e52428-6a47-4593-aadb-d2d8bca9faed`, terminal status `COMPLETE`.
The immutable archive `aristotle/results/Q252-retry-01-final.tar.gz` has
SHA-256
`449ec59064bd288acbe1d739b0e1f14bb9496c438a77844947dde453c60ee627`.
All twelve archive entries were inspected.

The restored context is byte-exact against the current repository:

- `Principia/Syntax/Formula.lean`:
  `4ae57f04fe68659b5afc75e7edf065a229ca1b68ef7ada719797c5011240bb8d`;
- `Principia/Syntax/Apparent.lean`:
  `781387ff47f160b546d91106d5bf9afe5750735aec49ccb58bcf28501d4e069b`.

The diplomatic source body is byte-exact against the canonical text in
`aristotle/Q252.md`. The returned declaration section is also byte-exact:
it contains exactly `star_9_01`, `star_9_02`, `star_9_011`, and
`star_9_021`, with no extra declaration and no changed parameter, context,
body, or namespace. Thus all four canonical IDs are covered; ✱9·011 and
✱9·021 remain aliases rather than new logical claims.

Negative source audit found no `sorry`, `admit`, new `axiom`, `unsafe`,
`@[implemented_by]`, `native_decide`, quotient, alternate syntax, semantic
object-language quantifier, weakened target, or added hypothesis. Aristotle
reports `lake build Principia` successful and four disposable `rfl` checks
successful, including both negation reductions and both brace-omission
aliases; the check file was removed from the archive.

The canonical Star9 file and item metadata are integrated with formal status
`awaiting-ci`. No local Lean command, commit, or push was performed for this
final audit; only repository CI may promote the four items to
`kernel-checked`.
