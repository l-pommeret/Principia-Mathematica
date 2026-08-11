# Constrained reconstruction of printed PM demonstrations

The reconstruction pipeline treats the printed demonstration as a search
constraint, not merely as prose checked after a proof has been found.

1. `scripts/pm_syntax.py` parses a printed proposition into the PM object AST.
2. `scripts/pm_proof_skeleton.py` parses the demonstration into ordered
   references, printed aliases, substitutions, and intermediate-line uses.
3. `scripts/pm_constraint_manifest.py` resolves those references against the
   reviewed item metadata and emits two deliberately distinct sets:

   - `allowed_pm_items` / `allowed_lean_declarations`: the only historical
     results that a reconstructed proof may cite;
   - `context_closure` / `context_declarations`: declarations that must be
     present merely so that the allowed results typecheck in an isolated
   sandbox.
4. `scripts/pm_constraint_audit.py` compares the PM dependencies extracted
   from the returned Lean term with that manifest. It classifies strict
   closure, unused printed citations, and relaxed closure, recording the exact
   additional PM items required by a relaxation.
5. `scripts/pm_aristotle_prompt.py` renders the compact request. For any
   nonempty implementation closure it refuses to produce a submission without
   an explicitly supplied, reviewed isolated Lean context. The context is
   labelled as compilation scaffolding and the proof whitelist is printed in a
   separate section.
6. `scripts/pm_context_bundle.py` constructs that isolated context for the
   elementary profile. It strips commentary and imports from the complete
   trusted syntax/deduction foundation, appends only declarations in the
   implementation closure, and records SHA-256 digests for every source and
   slice. The generated source still requires a remote kernel check before use.
   A tracked bundle is accepted only when its metadata records a successful CI
   run that kernel-checks the standalone generated file.

The context closure grants no proof permission. A generated Aristotle request
must state the whitelist explicitly, and the returned term must still pass the
repository dependency audit. Thus the prompt constrains search and the audit
independently checks the resulting term.

Strict compilation fails before submission when a printed reference has no
metadata, is not kernel checked, or an alias cannot be resolved at the current
historical locus. Family aliases such as `Transp` remain explicit finite
families rather than being silently resolved to whichever theorem happens to
close the goal.

Rules that PM declares globally implicit may be supplied separately with
`--global-convention`. They enter the whitelist but are not misreported as
literal bracket citations. This covers, for example, silently used inference
rules ✱1·1/✱1·11 and later ✱9·12; the choice must come from an audited source
convention at the current locus.

Substitutions are retained as first-class audit data. In the elementary
fragment they may be implemented by instantiation of Lean schema parameters,
as documented in `docs/SUBSTITUTION.md`; the manifest nevertheless records the
printed substitution instead of erasing it.

## Failure and relaxation

If the strict whitelist does not close the goal, that outcome is evidence. A
later relaxation must produce a second manifest recording every added item;
the strict failure is never overwritten. This supports three distinct
editorial outcomes:

- strict closure: reconstruction faithful to the printed citations;
- alias-family closure: faithful up to a printed named family;
- relaxed closure: printed dependency list incomplete, with the minimal added
  dependencies recorded explicitly.

The current manifest compiler is the deterministic boundary. Automatic prompt
rendering and minimal-relaxation search may be built on it, but must not merge
proof permissions with implementation closure.

## Ordered batches

Small batches may contain a genuine forward sequence such as
✱2·73→✱2·74→✱2·75→✱2·76. A batch manifest audits each declaration separately:
an earlier target becomes a local proof permission only after it has been
declared, is never added to the kernel-checked external closure, and cannot be
used by a preceding target. `metadata/constrained_batches/Q218.json` is the
first end-to-end fixture. Its manifest, isolated context, and compact
Aristotle request are reproduced by `scripts/verify_constrained_batches.py`.
Returned declarations are then classified independently by
`scripts/pm_batch_audit.py`; one relaxed target cannot make its neighbours look
strict, and every additional PM item is retained as explicit audit data.
