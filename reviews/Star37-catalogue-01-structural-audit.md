# ✱37 catalogue 01 — non-v1 structural audit

Scope: the five definitions ✱37·01–·05 on printed page 296 (scan leaf
318), checked against their canonical `PM-VERBATIM` blocks and against the
current Lean tree.

The Star2/T1–T9 gate requires the printed construction to occur in a typed PM
AST and a well-formed judgement, with kernel evidence. For a line marked `Df`,
the evidence must be definitional unfolding of the actual constructor; a
theorem that postulates the displayed equality, an opaque atom, or a generic
"support" constructor is not acceptable.

| locus | required definitional object | current evidence | verdict |
|---|---|---|---|
| ✱37·01 | relational image `Rʻʻβ` with its bound witness and membership/converse orientation | source block only | blocked |
| ✱37·02 | the image-membership relation `R_∈` between classes | source block only | blocked |
| ✱37·03 | converse of the actual `R_∈` constructor | source block only | blocked |
| ✱37·04 | iterated image defined through `R_∈` | source block only | blocked |
| ✱37·05 | the quantified uniqueness/existence condition `E‼Rʻʻβ` | source block only | blocked |

There is no Lean declaration for any of the five IDs, hence no definition to
unfold, no typed relational/class AST, no judgement, and no kernel derivation.
Creating an opaque propositional constant or adding an axiom/constructor would
only manufacture support and is explicitly rejected. All five records remain
`prepared` and are blocked until the missing typed constructors and genuine
definitional evidence are implemented.

These definition lines print no theorem citations. Since no Lean declaration
exists, there are likewise no Lean theorem calls. Printed, Lean, and normalized
dependency graphs are therefore independently rebuilt as empty; this is not a
claim of formal completeness.
