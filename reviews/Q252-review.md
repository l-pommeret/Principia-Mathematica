# Audit Q252 — PM I, ✱9·01, ✱9·02, ✱9·011 and ✱9·021

Verdict: **A FOR TARGET AND CONTEXT — await follow-up GitHub CI before
submission**. Canonical source:
first edition, vol. I, pp. 132–135, leaves 154–157. The complete introductory
text and the definitions through ✱9·08 are embedded in the prompt so that the
formalizer receives PM's type-theoretic motivation, not four contextless
formulae.

Exact definitional content: `∼{(x).φx}` reduces to `(∃x).∼φx`, and
`∼{(∃x).φx}` reduces to `(x).∼φx`; ✱9·011 and ✱9·021 define the omission of
braces after the negation sign and add no theorem. Dependencies are ✱9·01 for
✱9·011 and ✱9·02 for ✱9·021. No PM printing error is established. The
Wikisource `shell/shall` and Gutenberg's missing opening parenthesis at
✱9·03 are digital-witness defects only.

The current `Principia/Syntax/Apparent.lean` supplies an elementary matrix
syntax with capture-safe de Bruijn renaming/substitution and a separate
`Quantified` step. Its injectively distinct `.always` and `.sometimes`
constructors represent PM's two primitive binding ideas. `FirstOrder.neg`
uses `Quantified.neg` and kernel-reduces on those constructors exactly as
✱9·01/02 require; existence is not encoded as `∼∀∼`.

The prompt copies the relevant API and fixes four exact repository-ready
`abbrev` bodies. `star_9_01` and `star_9_02` reduce to the printed right-hand
sides; `star_9_011` and `star_9_021` are aliases only, correctly recording
PM's brace omission without inventing theorem dependencies. No semantic
Lean quantifier, new axiom, or alternate syntax is introduced.

The target/context audit is A with high confidence. Submission remains gated
only because the current `Quantified`/`FirstOrder` worktree addition does not
yet have immutable GitHub CI evidence; run 31427351077 covers its predecessor.
