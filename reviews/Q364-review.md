# Q364 review

PM I p. 232 / leaf 254 is canonical; the 1910 scan fixes the Λ reading in ✱24·3. PG 78050 is consulted only as a secondary witness. No apparatus or `[sic]` is required.

## Star2/T1–T9 object-judgment audit

This three-item lot is homogeneous blocked, 0/3. The declarations
`star_24_26`, `star_24_27`, and `star_24_3` establish the intended extensional
class propositions in Lean `Prop`, without placeholders. They are useful
secondary semantic checks, but none has a PM syntactic formula
as endpoint and none is a judgment of an inductive primitive-rule relation.
`Classical.byContradiction` in ·3 is a valid Lean semantic step, not a
reconstruction of PM's printed derivation.

The axiom gate also fails independently: `#print axioms` reports
`[propext, Quot.sound]` for ·26/·27 and
`[propext, Classical.choice, Quot.sound]` for ·3. Thus these declarations are
not evidence for an axiom-free tier even if the judgment-layer defect were
ignored.

No `Df` is promoted to a derivation constructor. The class operations unfold
as ordinary definitions inside the secondary proofs only.

Graphs rebuilt from zero:

- ·26 printed: ✱22·621, ✱24·11; actual Lean: empty; normalized: empty;
- ·27 printed: ✱22·62, ✱24·11; actual Lean: empty; normalized: empty;
- ·3 printed: empty; actual Lean: empty; normalized: empty.

Definition constants in signatures and proof reductions are not theorem edges.
These empty secondary graphs do not supply the absent PM derivations, so all
three items remain `prepared` and blocked.

For completeness, the source-level secondary definition references are:
·26 uses `Intersection` and the Q362 duplicate `universalClass`; ·27 uses
`Union` and that same duplicate; ·3 uses `Included`, `Difference`, and the Q362
duplicate `nullClass`. The dependency extractor explicitly rejects
`Difference` as an unindexed qualified reference. Those definitions are not
silently normalized to PM theorem edges: the secondary graph is itself blocked
rather than completed by invention.
