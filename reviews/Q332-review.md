# Q332 exact Lean audit

Leaf 238 (p. 216), SHA-256
`bf0ff41a2c61faff2e7d55b655b572aa0fbe16a56f915355ab7d34ad40019067`,
witnesses ✱21·11, ✱21·111, ✱21·112, ✱21·12, and ✱21·13.

The Lean module retains each relation as `Left → Right → Prop`, so neither
apparent variable is erased or forced to share a type. Formal equivalence
with subscript `(x,y)` is `∀ x y, … ↔ …`. Function application in
✱21·11/111/112/12 is genuinely at a relation argument, while ✱21·13
concludes equality of the complete binary extensions.

The only logical extensionality step is Lean's kernel-level `propext` followed
by function extensionality. There is no `Classical`, choice, relation axiom,
placeholder, unsafe feature, narrowed unary instance, or semantic stub.

## Object-judgment re-audit

The five declarations are axiom-free semantic Lean theorems, but none meets
the T1–T9 object-judgment standard established in `dialogue.md`. Their
statements are host `Prop`, not a relational syntax indexed by an inductive PM
derivation, and their bodies do not call earlier PM derivations. The archived
`Support` prototype is neither imported nor an admissible replacement.

Accordingly all five items are blocked. In ·11 and ·13, `propext` and function
extensionality establish semantic function equality rather than the printed
assertion. Item ·111 merely specializes a host universal equivalence. Items
·112 and ·12 choose the input function/relation itself as a reflexive witness;
they do not consume the printed reducibility and earlier-✱21 chains.

The graphs were rebuilt from scratch. Lean numbered-derivation graphs are
empty for all five. Printed and normalized graphs are: ·11 =
`[✱4·86, ✱4·36, ✱10·281, ✱21·1]` (the source compacts its first two
canonical references as `✱4·86·36`); ·111 = `[]`; ·112 =
`[✱12·1, ✱21·111]`; ·12 = `[✱21·11, ✱12·11]`; and ·13 =
`[✱21·1, ✱12·11, ✱13·195]`. The old dependency relaxations are removed:
failure to consume a printed proof is a blocker, not a relaxation.

The printed edge from ·112 to the reducibility postulate ✱12·1 transmits its
non-logical assumption `PM1:REDUCIBILITY`. Thus ·112 declares no direct
assumption and declares that inherited assumption explicitly; this records
the historical proof closure without pretending that the current Lean body
consumes the derivation.

Likewise, ·12 and ·13 inherit `PM1:REDUCIBILITY` through their printed edges
to the binary reducibility postulate ✱12·11; neither introduces a direct
non-logical assumption.
