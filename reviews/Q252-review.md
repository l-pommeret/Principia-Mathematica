# Audit Q252 — PM I, ✱9·01, ✱9·02, ✱9·011 and ✱9·021

Verdict: **PREPARED — architecture review required**. Canonical source:
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

The current repository has only elementary-proposition real variables and
cannot state these definitions faithfully. Submission is therefore barred
until an intrinsic, order-sensitive syntax for typed arguments,
propositional functions and apparent-variable binding is separately reviewed
and kernel-checked. Confidence in source collation: high; confidence in a
specific Lean architecture: deliberately withheld pending review.
