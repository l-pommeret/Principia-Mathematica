# Audit Q224 — PM I, ✱3·33–✱3·35

Verdict: **kernel-checked-relaxed-printed-gaps**. Source: first edition, vol. I,
p. 118, leaf 140; SHA-256
`20db12e87b5e387660bb8d9fd44527b82fe2b63f0c1ea8211e89b8be1dd64ebe`.

Scopes: `((p→q)·(q→r))→(p→r)`,
`((q→r)·(p→q))→(p→r)`, and `(p·(p→q))→q`. In particular,
the first two instantiate the ✱3·02 chain definition; they are not nested
right-associated implications. The canonical scan has the opening bracket in
✱3·34's `[Syll.Imp]`; Wikisource omits it, a separately recorded digital-witness
error with no AST or PM emendation. No PM print defect is established. Confidence
high.

The strict reconstruction is impossible for the generic target at `Γ = []`:
the printed Syll.Imp and ✱2·27.Imp citations support only the ✱1·11
nonempty-context detachment branch. Each of ✱3·33, ✱3·34 and ✱3·35 therefore
uses exactly one documented ✱1·1 empty-context detachment branch; no other
permission is added. The accepted archive is
`2e6011ebad20b3e51bde4945b66ad2696468a92567b298dfd1d01de2c82d6ef5`;
the strict retry `f22814d205cad296734ebaa176311acb4dd855afe3a8102f9dedc4080105612b`
remains rejected. Remote Lean CI is green at
[`31465395073`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31465395073),
commit `eff84d63c362fe72e2f2ce0e655b594e579b448e`.
