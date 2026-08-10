# Audit Q201 — PM I, ✱2·01–✱2·02

Verdict: **A — exact source and formal targets audited**.

Canonical source: first edition, volume I, printed p. 104, scan leaf 126:
https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/126

Independent witnesses: Project Gutenberg 78050 and Wikisource transcription.
The source sub-agent checked a 1920-pixel scan derivative with SHA-256
`39ef7ff5ed20046523393af261508ed63c872e9c2f82dfb944f4ab50e0c26f59`.

## Exact coverage

- ✱2·01: `⊢ : p ⊃ ∼p . ⊃ . ∼p`, read as `(p ⊃ ∼p) ⊃ ∼p`.
- ✱2·02: `⊢ : q . ⊃ . p ⊃ q`, read as `q ⊃ (p ⊃ q)`.

The printed demonstrations use only schema instantiation and the definitional
reading ✱1·01:

- ✱2·01 is Taut (✱1·2) under `p ↦ ∼p`, then notation is read through ✱1·01.
- ✱2·02 is Add (✱1·3) under `p ↦ ∼p`, then notation is read through ✱1·01.

No use of ✱1·1, ✱1·11, semantic truth, or an object-language substitution rule
is licensed. Lean's instantiation of theorem parameters represents PM's
particular recognition of an instance; no new PM inference constructor is
introduced.

## Scope decision

The targets quantify at Lean's metalevel over the same elementary
real-variable context `Γ`. This encodes PM's ambiguous assertion and does not
insert universal quantification into the object language.

## Exclusions

The natural printed page continues through ✱2·05, but ✱2·03–✱2·05 depend on
primitive propositions Perm, Assoc, and Sum (✱1·4–✱1·6), not yet present in the
audited calculus. They are deliberately excluded rather than proved from
stronger modern logic.

Ordinal confidence: high, based on direct source cross-check and independent
formal dependency audit. No mathematical or textual gap is known for the two
declared targets.

