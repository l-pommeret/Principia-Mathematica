# ✱25 v1 primary-judgment audit

Scope: ✱25·01, ·02, ·03, ·1, and ·101, first-edition p. 241.

Verdict: **blocked**, with no canonical promotion. The required benchmark is
✱2: a typed PM syntax object, a PM judgment, and a kernel derivation of that
judgment. The current ✱25 opening module instead defines relations directly as
Lean predicates and proves equalities or implications in host `Prop`.

The obstruction is architectural and exact:

- `PM.Elementary` currently contains only propositional constants, variables,
  negation, and disjunction. It has no relation-expression, relation
  abstraction, typed relational application, quantifier, relation equality,
  or dotted-existence node.
- `PM.Derivation` derives only `PM.Elementary` formulae from the six primitive
  propositions/rules of ✱1. It has no audited bridge by which the five ✱25
  formulae could become kernel judgments.
- Consequently the declarations in `Star25OpeningKernel.lean` are retained
  only as secondary semantic companions. Treating them as primary would erase
  precisely the syntax/judgment distinction required by v1.

Graphs were rebuilt from zero. None of the five printed lines has a bracketed
citation, so each printed graph is empty. Since no primary PM declaration
exists, the primary Lean and normalized graphs are also empty; dependencies
of the secondary host-level proofs are deliberately not substituted into a
nonexistent PM derivation graph.

Unblocking requires an audited extension of the PM AST and derivation kernel,
starting from the first printed introduction of relational syntax and its
formation/inference rules. Adding ad hoc ✱25 axioms, encoding whole formulae as
opaque elementary constants, or promoting extensional `Prop` theorems would
not satisfy v1 completeness.
