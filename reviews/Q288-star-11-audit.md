# Q288 audit — PM I ✱11·71

The declaration in `Star11Q288Kernel.lean` follows the displayed grouping on
first-edition leaves 188–189. The initial juxtaposition is the conjunction of
`(∃z).φz` and `(∃w).χw`. Its consequent equates the conjunction of the two
unary formal implications with the binary formal implication between the
pointwise conjunctions.

The two existential hypotheses are mathematically essential in the reverse
direction: a witness for `χ` extracts the `φ ⊃ ψ` component, and a witness for
`φ` extracts `χ ⊃ θ`. Both witnesses are used explicitly. Thus the Lean type
retains every binder, antecedent, connective, and side condition printed in
✱11·71; it neither strengthens the hypotheses nor weakens the conclusion.

The proof is constructive and unconditional at that exact type. It uses no
classical principle, axiom, `sorry`, `admit`, or unsafe escape hatch.
