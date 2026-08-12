# Q336 exact relation-description audit

Leaf 242 (p. 220), SHA-256
`c256535376791e2e7a96923675c04e5226822c332c25e25872ad55d80a3e81b9`,
is the canonical witness, collated with PG78050.

All five endpoints are formalized in `Star21Q336Kernel.lean` over polymorphic
binary relation extensions. ✱21·53 and ✱21·54 are the universal and existential
forms of identity elimination. ✱21·57 is congruence for an arbitrary function
of relations.

For ✱21·55/56 the incomplete description is represented contextually as the
subtype of relations carrying the displayed pointwise characterization. Its
canonical witness is the relation `φ` itself. ✱21·56 additionally proves the
full unique-existence condition by function and proposition extensionality.
This preserves the scope of the incomplete symbol, proves existence without
choice, and makes the printed identity definitionally true. It does not turn
the description into a freely denoting term outside that context.

No inhabitance, decidability, classical principle, new axiom, placeholder, or
unsafe declaration is used. The batch awaits CI after targeted Lean 4.30.0
compilation.
