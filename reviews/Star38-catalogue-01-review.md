# ✱38 catalogue-01 axiom-free PM-derivation gate

The five items are re-audited against the `Star2`/T1–T9 standard. Completion
requires genuine PM syntax plus a judgment and axiom-free derivation; a closed
ambient-`Prop` theorem is secondary evidence only. Printed definitions must be
represented by actual definitions, not theorem wrappers.

The graphs were rebuilt from the source. Definitions ·01–·03 have no printed
theorem citations. Proposition ·1 cites only ✱38·01, and ·101 cites only
✱38·02. In Lean those two real definitional edges are respectively
`LeftSection` and `RightSection`; the `Iff.rfl` proofs introduce no numbered
theorem edge.

All five items are blocked. `LeftSection`, `RightSection`, and `Slice` are
genuine Lean `def`s and provide coherent typed semantics, but they construct
meta-level functions and predicates rather than PM formulas. Likewise ·1 and
·101 are correct `Prop` equivalences, but neither constructs an object-language
formula, a PM judgment, or a `PM.Derivation`. The earlier successful CI checked
only that secondary layer and therefore does not satisfy this gate.

The unique five-record artifact remains `prepared`; no later ✱38 item is in
scope.
