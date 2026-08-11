# Audit Q222 — PM I, ✱3·2, ✱3·21, ✱3·22, ✱3·24

Verdict: **A — kernel-checked relaxed reconstruction with printed gaps
recorded**. Sources: first edition, vol. I, pp. 116–117, leaves 138–139.
SHA-256: leaf 138
`c18eb6890dc92335e8df8773cbd46b8e98c2e550cdcb01f91a397bed27e9958b`;
leaf 139 `1b819017782765dda67ae70a26b49055f1a636edbc04ed5aa52985fd018f047c`.

The final clean Aristotle artifact is the retry-03 archive
`aristotle/results/Q222-repair-forbidden-output-final.tar.gz`, SHA-256
`30f5f28fce7457d6dfb27f277f0304af1cb60e114f91fcacf2948be2a378f349`.
It was integrated in the edition and remote Lean CI kernel-checked the full
edition at commit `e9707ed15b2359170ba135973dd0948558136b8b`, GitHub run
[31458071367](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31458071367),
with conclusion `success`.

The reconstruction is deliberately **not** a strict printed-dependency
closure (`strict: false`). Its two independently reviewed additions are:

- ✱3·2 uses ✱2·32 once. ✱3·12 is left-associated by its printed scope marks,
  whereas ✱3·2 is right-nested; ✱2·33 does not silently identify them.
- ✱3·22 uses ✱2·06 twice. Both joins are required to make the printed
  ✱3·13–Perm–✱3·14 chain load-bearing before the printed Transp conclusion.

The ordinary asserted-implication application is recorded separately as the
reviewed ✱1·11 detachment convention. ✱3·21 and ✱3·24 otherwise have strict
printed-event coverage. The generated reconstruction audit
[`Q222-reconstruction-audit.json`](Q222-reconstruction-audit.json) records all
four target terms, their event coverage, and the two approved relaxation uses.
The first association-only result and archive
`98db29f6adebc8bb531127e9247d69ba09501ad3a07ca8d634ce920a67ee9232` remain
rejected historical artifacts; the latter was rejected for forbidden output
and is not the promoted archive.

The central anomaly register retains the two source/reconstruction gaps and
the rejected artifacts as distinct records. Neither gap is entered as an
official PM erratum, and no diplomatic reading or parsed AST has been altered.
