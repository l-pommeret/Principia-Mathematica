# Audit Q252 retry 01 — terminal error and repository-context mismatch

Verdict: **B — exact target declarations recovered; same-project context
repair required**. Confidence: high.

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

No continuation was submitted, no local Lean command was run, and no commit
or push was performed during this audit.

