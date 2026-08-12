# Q285 exact Lean audit

The diplomatic record on PM I pp. 164–165 (scan leaves 186–187) gives five
propositions, ✱11·521, ✱11·53, ✱11·54, ✱11·55, and ✱11·56.
`Star11Q285Kernel.lean` preserves both apparent-variable domains and every
printed matrix: successive PM binders become successive Lean binders,
juxtaposition becomes conjunction, and implication and equivalence retain
their logical meanings.

✱11·521 is the literal classical no-counterexample equivalence.  ✱11·53
separates the variables of an implication.  ✱11·54 factors independent
existential conjuncts, while ✱11·55 retains the dependency of `ψ` on both
variables under the nested existential.  ✱11·56 requires `Nonempty α` and
`Nonempty β` only in its reverse direction; these assumptions explicitly
encode PM's convention that types have possible arguments and are logically
necessary for empty Lean sorts.

The proofs contain no `sorry`, `admit`, new axiom, unsafe escape hatch,
semantic stub, or narrowed example.  The historical dependencies remain in
metadata; Lean checks the complete translated propositions directly.
