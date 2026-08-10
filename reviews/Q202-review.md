# Audit Q202 — PM I, ✱2·03–✱2·05

Verdict: **A — exact source, scope, dependencies, and formal targets audited**.

Canonical source: Whitehead and Russell, *Principia Mathematica*, first
edition, volume I (1910), printed p. 104, scan leaf 126:
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/126

Independent working witnesses: Project Gutenberg ebook 78050 and the
Wikisource transcription. The scan, rather than either digital transcription,
is authoritative when witnesses diverge.

## Exact coverage

- ✱2·03: `⊢ : p ⊃ ∼q . ⊃ . q ⊃ ∼p`, read as
  `(p ⊃ ∼q) ⊃ (q ⊃ ∼p)`.
- ✱2·04: `⊢ :. p . ⊃ . q ⊃ r : ⊃ : q . ⊃ . p ⊃ r`, read as
  `(p ⊃ (q ⊃ r)) ⊃ (q ⊃ (p ⊃ r))`.
- ✱2·05: `⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r`, read as
  `(q ⊃ r) ⊃ ((p ⊃ q) ⊃ (p ⊃ r))`.

The printed demonstrations are single primitive-proposition instances followed
by a definitional change of notation:

- ✱2·03 uses Perm (✱1·4) with `p ↦ ∼p` and `q ↦ ∼q`, producing
  `(∼p ∨ ∼q) ⊃ (∼q ∨ ∼p)`; ✱1·01 reads the two disjunctions as implications.
- ✱2·04 uses Assoc (✱1·5) with `p ↦ ∼p`, `q ↦ ∼q`, and `r ↦ r`, producing
  `(∼p ∨ (∼q ∨ r)) ⊃ (∼q ∨ (∼p ∨ r))`; ✱1·01 supplies the displayed reading.
- ✱2·05 uses Sum (✱1·6) with its first parameter `p ↦ ∼p` and leaves `q,r`
  unchanged, producing
  `(q ⊃ r) ⊃ ((∼p ∨ q) ⊃ (∼p ∨ r))`; ✱1·01 supplies the displayed reading.

No application of ✱1·1 or ✱1·11 occurs. No earlier derived theorem is needed.
Lean parameter instantiation represents PM's particular recognition of the
displayed primitive instance; it does not add an object-language substitution
rule.

## Formal target audit

The three targets retain a single arbitrary real context `Γ`. Their variables
are elementary propositional expressions in that same context, and the PM
assertion is represented by `PM.Derivation`. The targets neither interpret
those expressions as Lean propositions nor insert object-language universal
quantifiers.

The target parentheses reproduce the hierarchy of PM's dots and colons. Since
`PM.Elementary.imp p q` is definitionally `∼ₚ p ∨ₚ q`, each target reduces
exactly to the corresponding ✱1·4, ✱1·5, or ✱1·6 instance. No associativity,
commutativity, semantic reasoning, or unrecorded structural principle is
hidden in the translation.

## Editorial status

No error, conjectural emendation, or witness divergence affecting ✱2·03–✱2·05
was found in the checked source. Accordingly, this batch requires no `[sic]`,
`corr.`, or `conj.` entry. If a later collation reveals a divergence, the scan
reading and the digital-witness reading must be recorded separately rather
than silently normalizing the diplomatic text.

Confidence: high for formula, scope, dependency, and formal-target identity,
based on direct inspection of the canonical page and comparison with the
existing audited encodings of ✱1·01 and ✱1·4–✱1·6.
