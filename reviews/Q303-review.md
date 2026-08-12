# Q303 review — ✱14·124 and ✱14·131

Leaf 208 (pp. 186–187), SHA-256
`23f4d91b4e9c1bd47a6e05d334ce52f038a10e65b04c4a58b2ae49753f3a24a2`,
and PG78050 agree on both loci.

The old ✱14·124 metadata was materially truncated: its right member continues
after `(∃x,y).φ(x,y)` with the printed coordinatewise uniqueness condition
`φ(z,w).φ(u,v) ⊃_{z,w,u,v} z=u.w=v`. The corrected Lean theorem proves the
complete equivalence between a characterizing pair and existence plus that
coordinatewise uniqueness.

For ✱14·131, `DescriptionIdentity` retains two local characterization
witnesses and equates only their candidates. Thus the symmetry proof never
manufactures `(℩x)(φx)` as a total term, respecting the contextual definition
of ✱14·01. Both theorems are unconditional and contain no placeholders.

Targeted check (Lean 4.30.0):

`lake env lean Principia/Architecture/Star14Q303Kernel.lean`
