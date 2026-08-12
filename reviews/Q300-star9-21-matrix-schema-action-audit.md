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
implication; constructing its derivational bridge from ✱2·08 at the assigned
first-order carrier remains a separate task.  The module records its Raw
source target but does not claim it is derived.

Witnesses: first edition (1910), p. 140, leaf 162; proofread Wikisource page
162; `aristotle/demonstrations/PM1-star-9-3.txt`.
