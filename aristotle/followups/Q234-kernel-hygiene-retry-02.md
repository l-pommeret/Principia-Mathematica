# Q234 continuation — exact kernel bodies, no archive-local interface

The immediately preceding terminal archive (task
`a25f01b3-288c-42eb-b332-f82f254280f3`, immutable SHA-256
`baca35b44ad43bbab515f8edad328ed19d8bdb8f15db3e7430b39b0f9f031eb8`) is
rejected.  It includes archive-local PM syntax and `PM/Star2.lean`; the latter
contains a new `axiom`.  The claimed five proofs consequently do not establish
the canonical targets against accepted kernel bodies.

Continue this same project.  The only acceptable Lean deliverable is exactly
the five unconditional declarations in `Q234.md`, in order: `star_4_5`,
`star_4_51`, `star_4_52`, `star_4_53`, `star_4_54`, with their exact submitted
signatures, citations, the complete De Morgan paragraph, and the corrected
✱4·52 formula `∼(∼p∨q)`.  Do not add hypotheses or alter the target scope.

Use only already accepted project-visible kernel bodies for the permitted
dependencies.  Do not copy, import, rebuild, remap, or rely on local PM
syntax/Star2/Star4 modules or archived interfaces; do not introduce any
`axiom`, `opaque`, `Classical`, `sorry`, `admit`, `unsafe`, native connective,
semantic shortcut, generic substitution, helper, or extra declaration.

First inspect whether the accepted kernel bodies are actually visible in this
project.  If they are, replace every archive-local derivation with direct exact
target proofs and verify the output has no local-copy or remap artifact.  If a
required body is absent, introduce no substitute code and return a short
per-target report naming the exact missing kernel declaration and printed step.
That report is incomplete, not a completion.
