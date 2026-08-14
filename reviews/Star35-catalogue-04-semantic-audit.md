# ✱35 catalogue 04 Star2/T1–T9 audit

`dialogue.md` was reread before this audit. None of ·17, ·18, ·22, ·23, or ·24
has an object-language reading and inductive derivation. The first four are
axiom-free semantic equalities proved with `funext`, `propext`, constructors,
or `simp`; ·24 is a host-language definition unfolded by `rfl`. These do not
satisfy T3/T4 and are not promoted.

Graphs were reconstructed independently from source and calls. Printed edges
are ·17→·13, ·18→·15, ·23→·22; ·22 and the definition ·24 have none. The Lean
bodies make no numbered theorem calls for these five. Because no candidate
reaches the object-judgement gate, accepted Lean and normalized graphs remain
empty rather than treating semantic helpers or definitions as PM citations.

All five are `prepared`, blocked, and retain pending CI evidence.
