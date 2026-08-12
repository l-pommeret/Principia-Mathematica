# Gate kernel ✱4·85

The facsimile at p. 127, leaf 149 reads `p ≡ q . ⊃ : r ⊃ p . ≡ . r ⊃ q`, with printed references ✱2·05 and ✱3·47. The Lean candidate preserves that orientation. It extracts both components of `p ≡ q`, lifts each below the common antecedent `r` by ✱2·02 and ✱2·77, and explicitly joins the resulting implications using ✱3·2, ✱2·43, and ✱3·47. No generic detach or oracle is used.

Static local gate: `PATH=/Users/user/.local/lean-4.30.0/bin:$PATH lake build Principia.FirstEdition.Volume1.Part1.SectionA.Star4` succeeded (3.6 s).
