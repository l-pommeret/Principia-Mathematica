# ✱96 catalogue 02 semantic audit

The five canonical loci ·103, ·104, ·11, ·121, and ·14 were checked
against Project Gutenberg 78050 and the first-edition scan on printed pages
640–641 (scan leaves 662–663). They form a unique, duplicate-free second
catalogue lot.

Three declarations are strict typed equivalents. `star_96_103` says exactly
that restricting the proper ancestral to `J_Rʻx` yields an irreflexive
relation. `star_96_11` preserves the domain restriction and inclusion between
the two proper ancestrals. `star_96_14`, under PM's field premise, decomposes
the reflexive posterity into the singleton of `x` and its proper posterity.
These three are `awaiting-ci`.

Two candidates are refused. PM ·104 prints a chain of three equivalent
conditions, ending with `J_Rʻx = R_*⃖ʻx`; `star_96_104` proves only the first
equivalence and omits that final condition. The local source ledger was
corrected to restore it. At ·121, PM's hypothesis `Rʻʻα ⊂ α` is forward
closure of `α` under `R`, while Lean requires `BackwardClosed A R`; this reverses
the closure direction and is not a faithful conditional theorem. Both remain
`prepared` with explicit blocked semantic-mismatch statuses.

The targeted Lean source compiles without placeholders or unsafe declarations.
No CI success is asserted by this audit.

For the three promoted declarations, Lean uses direct typed normalization or
induction rather than replaying PM's printed derivations. Their printed
citations are retained in the historical graph and explicitly classified as
unused by the closed Lean term; no extra Lean dependency is introduced.
