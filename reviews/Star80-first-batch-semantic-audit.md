# ✱80 first-batch semantic audit

Audited items: ✱80·01, ·1, ·11, ·12, ·13. None is promoted.

- ·01: `Selection` captures subrelation, converse-domain equality, and
  uniqueness of referents, but `star_80_01` only unfolds that local predicate;
  it does not identify PM's class-valued operator `P_Δ` itself.
- ·1 and ·11: both Lean declarations are reflexive tautologies and omit the
  printed class characterization.
- ·12: Lean proves existence of a predicate equal to `Selection P k`, not PM's
  descriptive existence assertion for the class `P_Δʻκ`.
- ·13: Lean assumes an arbitrary `S` and proves `S = Selection P k` iff itself;
  it does not formalize the printed membership/equality characterization.

The five declarations are total Lean proofs, but their statements are weaker
than the source readings. All therefore remain `prepared`; no dependency or
promotion claim is made.
