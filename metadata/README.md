# Metadata

One JSON record under `items/` describes each printed PM item. Dependency edges
use stable editorial IDs rather than filenames or mutable Lean theorem names.

One JSON record under `source_blocks/` describes each unnumbered or extended
prose block retained in a `PM-VERBATIM` comment. These records identify the
canonical scan leaves and control witnesses, state the reflow policy, and pin
the canonical UTF-8 body and downloaded witnesses with SHA-256 hashes where a
stable byte stream is available. Page-local footnote symbols may be replaced by
global numeric labels only when the mapping is recorded explicitly.
