# Q256 ✱9·2 kernel review

The public result is exactly `Star92KernelAssertion φ y`. The printed target
mixes a first-order antecedent with the elementary value `φy`, so it is not
misrepresented as homogeneous `OrderedAssertion` syntax.

The closed constructor carries the actual ✱2·1 derivation, the exact ✱9·1
instance, the displayed ✱1·11 detachment stage, and syntax certificates for
✱9·05 and ✱9·01/✱1·01. No oracle, `sorry`, classical reasoning, or generic
cross-order detachment rule is introduced.

Status: kernel-checked at commit
`125839b146e32632b67146cbe46d71528b0798d4`, run `31577423330` (success).
The checked conclusion is exactly `Star92KernelAssertion`, not an
`OrderedAssertion` reinterpretation.
