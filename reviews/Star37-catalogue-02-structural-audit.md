# ✱37 catalogue 02 — non-v1 structural audit

Scope: ✱37·33, ·401, ·412, ·41, and ·6, checked against their
canonical source blocks on printed pages 302–305. `dialogue.md` was read in
full before this audit; its T1–T9 contract and the prohibition on converting a
missing proof into a constructor are applied here.

All five records are source-only. There is no existing Lean theorem to audit,
no object-syntax endpoint, no accepted inductive judgement for this relational
fragment, no concrete reading joining the diplomatic line to such an AST, and
no kernel derivation. Consequently:

| locus | missing real proof obligation | verdict |
|---|---|---|
| ✱37·33 | composition/image equality | blocked |
| ✱37·401 | domain of the printed restriction operator | blocked |
| ✱37·412 | image under restriction/intersection equality | blocked |
| ✱37·41 | two domain equalities derived through ✱37·402 and ✱36·11 | blocked |
| ✱37·6 | functional-image class abstraction under `E‼` | blocked |

No target or primitive support was invented. In particular, a constructor
named after one of these derived propositions would merely assume it, and a
`Prop` theorem would not satisfy T3/T4 even if extensionally true.

## Dependency graphs rebuilt from zero

- ✱37·41 explicitly prints citations to `PM1:✱37·402` and
  `PM1:✱36·11`; those are its two printed edges.
- ✱37·33, ·412, and ·6 print no citation.
- ✱37·401 says only “Similar proof”, which is not an identifiable numbered edge
  and is not guessed into the graph.
- Because all five are source-only, there are no Lean theorem calls and every
  Lean/normalized dependency list remains empty.

The lot remains `prepared` and structurally blocked; pending CI fields are not
evidence of completion.
