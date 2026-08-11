# Q259 review — ✱9·3, ✱9·31, ✱9·32, ✱9·33

**Audit status: A — architecture-interface only.** This review licenses an
isolated, assigned-order proof task after its exact prerequisite API is
included in the context bundle. It is not a canonical-integration approval.

## Witness and transcription

- First edition, volume I (1910), printed p. 140, scan leaf 162.
- Canonical Commons DjVu derivative SHA-256:
  `bd0e3af38b946e64c1f6d9a59d95d427ff9dac0fef26f9f7f7898896ea1ddcab`.
- Independent text witness: Project Gutenberg 78050.
- Diplomatic targets and demonstrations: `Principia/FirstEdition/Volume1/Star9.lean`
  and `aristotle/demonstrations/PM1-star-9-{3,31,32,33}.txt`.

The four targets are respectively the universal and existential analogues of
✱1·2, and the two right injections analogous to ✱1·3. Their printed scopes
are retained: ✱9·3/·31 use same-assigned-order disjunction; ✱9·32/·33 use
the mixed elementary-left quantified disjunction normalized by ✱9·03/·05.

## Licensed dependency graph

| Target | Printed dependencies retained in the proof task |
| --- | --- |
| ✱9·3 | ✱1·2; Pp ✱9·1; Pp ✱9·13; Df ✱9·05·01·04; ✱9·21; Df ✱9·03 |
| ✱9·31 | Pp ✱9·11; Pp ✱9·13; Df ✱9·03·02 and ✱9·05·06 |
| ✱9·32 | ✱1·3; Pp ✱9·13; ✱9·25; Df ✱9·03 |
| ✱9·33 | the printed “Proof as above”, with the existential branch and the same ✱9·13/·25 route |

✱9·11 is not replaceable by a derived elementary-disjunction route: the
printed discussion explicitly records the circularity through ✱1·2.

## Architecture and promotion gate

- Object formulas are `PM.OrderedFormula`; only the metalinguistic
  `PM.OrderedDerivation` judgment has Lean result sort `Prop`.
- The exact first-order targets are named in
  `PM.Architecture.FirstOrderQ259`; their same-order disjunctions use the
  audited `scopedFirstOrderDisj .sameAssignedOrder` constructor.
- The bundle must list the exact prerequisite source adapter and closed Q259
  rulebook as hash-audited local architecture context. Those local paths grant
  no proof permission and are permitted only under `interface_gated` policy.
- Every cited non-kernel result remains an explicit named interface and must
  be remapped one-to-one to an accepted canonical declaration before any
  integration. A remote kernel result for this bundle is evidence for the
  isolated task only.

No native logical semantics, `Classical`, axioms, placeholders, generic
substitution/inference rule, target-as-primitive constructor, or unscoped
first-order disjunction is permitted.
