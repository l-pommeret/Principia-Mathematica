# Audit — narrow matrix theorem-schema action for ✱9·21

The proof of ✱9·3 on PM I p. 140 / scan leaf 162 applies ✱9·21 directly to
its line (4):

```text
⊢ :(x):. φx ∨ (y).φy :⊃ φx                         (4)
⊢ .(4).✱9·21. ⊃ ⊢ :(x): φx ∨ (y).φy :⊃ (x).φx     (5)
```

The instance has the mixed function values

```text
α(x) = φx ∨ (y).φy,     β(x) = φx.
```

`α` is first-order whereas `β` is an apparent elementary value.  Therefore
the action belongs to the **theorem-schema layer**, not to
`OrderedAssertion`: adding a new assertion constructor would assert a new
Pp. `Star921MatrixSchemaDerivation.star_9_21_firstOrder_instance` is scoped
to this exact matrix shape and takes an explicit line-(4) schema derivation.
It does not produce an indexed `OrderedAssertion`, and it does not provide
generic detachment, substitution, or a polymorphic inference rule.

The preceding source line (1) is the identity of the mixed matrix
implication. `matrixIdentity` records this exact ✱2·08 theorem-schema
reading, still outside `OrderedAssertion`.  The existing indexed derivation
of the printed line (4) is reflected only by `indexedLine4`, whose equality
forces the source schema to be `star_9_3_matrix_schema`; applying the narrow
✱9·21 transition therefore yields the exact line-(5) Raw target.  This
remains theorem-schema evidence and is not reified as an `OrderedAssertion`.

The final bridge is therefore the closed `Star9KernelAssertion` constructor
`star_9_3_from_schema`.  Its only admissible input is the indexed
`Star921MatrixSchemaDerivation` for the exact `star_9_3_matrix_schema` line-6
Raw target, plus an equality identifying that Raw target with the fixed
assigned-order target.  It is a narrow derived judgement for ✱9·3, not a
generic Raw-to-`OrderedAssertion` conversion or a new primitive proposition.

CI [31567832588](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31567832588)
at immutable commit `17d08b6ec4966777273aada00452fc8c12767338` kernel-checked
the exact Q300/Q259 isolated contexts and the canonical build containing this
closed bridge.  The certification applies to the narrow
`Star9KernelAssertion` result only, not to a hypothetical `OrderedAssertion`
reification.

Witnesses: first edition (1910), p. 140, leaf 162; proofread Wikisource page
162; `aristotle/demonstrations/PM1-star-9-3.txt`.
