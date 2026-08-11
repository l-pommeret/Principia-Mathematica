# Q229 continuation — discard forbidden interface-audit scaffold

The terminal archive from task `6016323e-0d25-4367-a74c-0476aecfbd29` (SHA-256
`1d9544f1924a7d83f7d86a0d09ab21b05ecbe8d81bf0e1c3d2a8aaea01b27bd7`) is
rejected: `Q229InterfaceStubAudit.lean` uses `Classical`, and no local
interface/audit/copy/remap may stand in for canonical bodies.  Continue the
same project and deliver only the exact unconditional canonical Q229 target
declarations and signatures from `Q229.md`, in their submitted order, using
only their accepted project-visible whitelisted kernel bodies.  No local PM
module/interface/import/namespace/helper, remap, `Classical`, axiom, opaque,
sorry, admit, unsafe, conditional target, or obstruction Lean code is allowed.
If a needed accepted body is missing, return only its exact per-target kernel
name and printed locus; that is incomplete, not a proof.
