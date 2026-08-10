# Metadata

One JSON record under `items/` describes each printed PM item. Dependency edges
use stable editorial IDs rather than filenames or mutable Lean theorem names.
For every `kernel-checked` item, `printed_dependencies` records exactly the
references in PM, `lean_dependencies` records constants extracted from its Lean
proof term, and `normalized_dependencies` resolves the latter back to PM IDs.
`dependency_justifications` makes definitionally erased references and
metalinguistic bridges explicit. `scripts/verify_dependencies.py` rejects a
later, unprinted, unknown, or unjustified dependency. This check currently
covers kernel-checked items; it is not a claim about unintegrated future text.

`dependency_aliases.json` is the reviewed resolution table for PM's names
(`Taut`, `Perm`, `Syll`, and so on) and for Lean-only presentation bridges.

One JSON record under `source_blocks/` describes each unnumbered or extended
prose block retained in a `PM-VERBATIM` comment. These records identify the
canonical scan leaves and control witnesses, state the reflow policy, and pin
the canonical UTF-8 body and downloaded witnesses with SHA-256 hashes where a
stable byte stream is available. Page-local footnote symbols may be replaced by
global numeric labels only when the mapping is recorded explicitly.
