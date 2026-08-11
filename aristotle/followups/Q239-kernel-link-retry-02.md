# Q239 continuation — remove forbidden copied proof layer

The terminal archive from task `549cc03b-f4a9-4f89-bcf0-df54f0395ecf` (SHA-256
`c3ac60051045adf4a0e81a59023c1b36e8bf3c7370cbd6840e8098fc99875db4`) is
rejected: its local `PM/Star4.lean` contains `sorry`, `admit`, and `Classical`.
Continue this same project and deliver only the exact unconditional targets
✱4·73, ✱4·74, ✱4·76, ✱4·77 from `Q239.md`, using only accepted project-visible
bodies for the stated whitelist.  No copied/remapped PM module, local rule or
helper (`Proof.Equiv`, `EquivComm` included), import, redefinition, Classical,
axiom, opaque, placeholder, unsafe code, or target change is permitted.  If a
kernel body is absent, return a concise exact per-target missing-declaration
report only; it is incomplete, never a proof.
