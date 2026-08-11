# Audit Q226 — PM I, ✱3·44–✱3·48

Verdict: **kernel-checked-relaxed-printed-gaps**. Sources: first edition, vol. I,
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

Accepted candidate: retry-05 archive
`aristotle/results/Q226-retry-05-final.tar.gz` (SHA-256
`fb6d15ca745a031b7c9f95b7285c609acd694da0f618357e4ce64435661259a6`). It
proves all four targets in `Star3.lean`. Its literal audit finds no direct
`PM.Derivation.star_1_5/_1_6`, `syllRuleQ220`, `sorry`, `admit`, `unsafe`, or
axiom declaration in delivered sources. The exact relaxation is ✱3·3 only in
✱3·45 (two implicit exportations) and ✱3·2 only in ✱3·47, including its
documented equivalence-packaging carry in both Γ branches; ✱3·47 calls local
✱3·45 twice and contains no direct ✱3·3. The integrated source was
kernel-checked remotely at commit `fcfe6f5285732f672241281f1ff73f15477b9184`,
[run 31487053480](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31487053480),
whose edition build, placeholder guard, and reader build all succeeded.
