# Q348 / ✱22 — strict semantic audit

Scope: ✱22·4, ·41, ·42, ·43, and ·45 on PM I pages 220–221 (scan
leaves 242–243), checked against their canonical PM-VERBATIM readings and the
declared Lean artifacts.

This is a homogeneous v1 refusal lot: 0/5 propositions can be promoted under
the Star2 standard. `Star22Q348Kernel.lean` now contains extensionally correct
Lean `Prop` theorems for all five loci, but those declarations are secondary
semantic checks. None constructs a PM object-language `Formula`, and none has
type `PM.Derivation formula`. Consequently there is still no PM kernel
judgment for the printed assertions about mutual inclusion, class equality,
reflexive inclusion, intersection inclusion, or distribution of inclusion
over intersection.

The five records remain `prepared`, are blocked specifically by the missing PM
object judgment, and retain pending CI evidence. Their ordinary theorems are
recorded under `statement_declaration`, never as the primary `declaration`.

The dependency graphs were recomputed independently:

| locus | printed graph | actual secondary Lean graph | normalized secondary graph |
|---|---|---|---|
| ·4 | ·22·1, ·4·38, ·10·22 | — | — |
| ·41 | ·22·4, ·20·43 | `star_22_4` | ·22·4 |
| ·42 | ·10·11 | — | — |
| ·43 | ·3·26, ·10·11 | — | — |
| ·45 | ·22·1, ·10·29, ·22·33, ·10·413 | — | — |

These normalized edges describe only the secondary Prop implementation. They
do not stand in for the missing historical derivation graph, and therefore do
not authorize promotion.

Here an empty actual graph means that the secondary proof is direct after
unfolding local definitions; definition constants in theorem signatures are
not counted as theorem edges. Extraction from the declaration bodies finds
the sole theorem dependency `star_22_4` at ·41.
