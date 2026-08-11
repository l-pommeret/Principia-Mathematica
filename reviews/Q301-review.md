# Audit Q301 — PM I, ✱9·23 and ✱9·25

Verdict: **A-interface-only; submission prohibited pending Q300 remap.**

The first-edition witness is PM I (1910), p. 140, scan leaf 162, SHA-256
`bd0e3af38b946e64c1f6d9a59d95d427ff9dac0fef26f9f7f7898896ea1ddcab`.
The canonical `PM-VERBATIM` text in `Star9.lean` gives exactly:

- ✱9·23: `⊢:(x).φx.⊃.(x).φx [Id.✱9·13·21]`;
- ✱9·25: `⊢:.(x).p∨φx.⊃:p.∨.(x).φx [Id.✱9·23.(✱9·04)]`.

The required target for ✱9·23 has no extra Lean hypothesis: the printed
`Id` is the existing elementary `PM.FirstEdition.Volume1.Star2.star_2_08`
at `Apparent.openHead (matrixImp φ φ)`. The proof must then use the explicit
✱9·13 constructor and Q300's exact ✱9·21 theorem at `(φ, φ)`. Replacing this
path by reflexivity would erase both printed citations.

The required target for ✱9·25 likewise has no extra identity hypothesis.
It must cite the preceding local ✱9·23 at
`Apparent.ofElementary p ∨ₐ φ`; the target's right side is the exact
✱9·04 reduction. Here `p` remains elementary and independent of the
apparent `x` throughout.

Q300 currently supplies an audited target and a local architecture context,
not a terminal kernel-checked theorem body. Therefore no Lean `axiom`,
bodyless `opaque`, target constructor, or synthetic monotonicity interface is
allowed in Q301. Its only future interface is the one-to-one remap contract
recorded in `aristotle/manifests/Q301.json`; it becomes executable only after
the Q300 archive, project, exact declaration, and successful canonical CI are
recorded together.
