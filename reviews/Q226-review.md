# Audit Q226 — PM I, ✱3·44–✱3·48

Verdict: **strict retry rejected; scope-limited relaxation documented for ✱3·47**. Sources: first edition, vol. I,
pp. 118–119, leaves 140–141. SHA-256: leaf 140
`20db12e87b5e387660bb8d9fd44527b82fe2b63f0c1ea8211e89b8be1dd64ebe`;
leaf 141 `8d1f60a3cdcc48bada28c4a505c20529ee4e94f4c8a03da3f633132015a6f837`.

Scopes are `((q→p)·(r→p))→(q∨r→p)`,
`(p→q)→(p·r→q·r)`, `((p→r)·(q→s))→(p·q→r·s)`, and
`((p→r)·(q→s))→(p∨q→r∨s)`. The products of implications are ✱3·02
readings. ✱3·45 is `Fact`; ✱3·47's ✱3·03 citation is valid. Preserve all
numbered intermediates and the complete historical prose. No print defect or
Wikisource corruption is established within these four items. Confidence high.

Syll and Comm resolve respectively to ✱3·33/✱3·34 and ✱2·04; a missing solver
ledger entry for those aliases is a manifest-coverage defect, not a PM gap.
The generic Lean scope adds Γ = [] beyond the printed real-variable branch of
✱3·47. Exactly ✱3·2 is documented for that empty-context branch only; ✱3·03
remains the printed real-variable branch. Retry-01 archive
`aristotle/results/Q226-retry-01-final.tar.gz` (SHA-256 prefix `b7c0a27f`) is
rejected and unintegrated: ✱3·45 remains obstructed, and the delivered
PMContext.lean has inherited ✱1·5/✱1·6 uses that fail literal prompt-source
policy, although Q226.lean and its obstruction report are clean.
