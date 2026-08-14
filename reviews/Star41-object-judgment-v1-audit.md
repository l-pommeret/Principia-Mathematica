# ✱41 catalogue 01 — axiom-free object-judgment v1 audit

Scope: ✱41·01, ·02, ·1, ·11, and ·12. Acceptance follows the
✱1–✱5 / T1–T9 standard recorded in `dialogue.md`: the primary theorem must
be an axiom-free judgment of an inductive PM derivation relation over a concrete
object-syntax type, with an exact typed reading. A host `Prop` theorem is only
secondary evidence. Printed `Df` clauses must be eliminable definitions, never
constructors of the derivation relation.

## Infrastructure audit

No active module supplies a relational formula syntax or a relational
derivation judgment for ✱41. `Star41InitialKernel.lean` instead defines
`Relation α β := α → β → Prop` and `RelationClass` as a predicate on
those host relations. Every declaration in this lot concludes an equality,
iff, or implication in Lean `Prop`; none concludes an inductive judgment. The
module imports no syntax/reading or deduction system.

Constructing a fresh derivation with one constructor per desired proposition
would assume the results and violate T3/T6. Making ✱41·01/·02 constructors
would additionally turn printed definitions into irreducible axioms, the exact
failure rejected for ✱23 in `dialogue.md`. `Support` parameters or arbitrary
premises would merely hide the same assumption. Therefore the existing five
declarations remain useful secondary semantic checks, but no v1 item can be
constructed honestly until the preceding relational calculus (including the
rules actually used by ✱40 and its dependencies) exists as kernel derivations.

## Item results

- **✱41·01 and ·02:** `relationalProduct` and `sum` are valid host definitions,
  but no concrete PM syntax definitions or concrete relational readings exist.
- **✱41·1 and ·11:** `rfl` correctly unfolds those host definitions. This is
  the right behavior for `Df`, but its endpoint is still a host iff rather than
  a formula in a PM derivation judgment.
- **✱41·12:** the host proof directly specializes a universal function. It is
  axiom-free but is neither the source formula nor a PM derivation of it.

## Graphs from zero

Gutenberg prints no numbered bracket citation on these five displayed loci and
provides no separate demonstrations there. The active Lean bodies call no
numbered PM theorem: ·01/·02/·1/·11 are `rfl`, and ·12 is a direct lambda
proof. Consequently printed, Lean, and normalized proposition-dependency graphs
are all empty. Definition unfolding is not represented as a graph edge.

Result: 0/5 v1-complete, 5/5 explicitly blocked, 0 promotions. No
`formalization_level: pm-derivation-v1` is asserted and the old CI evidence for
the secondary Prop layer is not reused as canonical evidence.

## Cumulative catalogue 02 audit

The next five loci are ✱41·13, ·14, ·141, ·15, and ·151. No new
object-language infrastructure exists between this lot and catalogue 01, so
the same T3/T4 obstruction remains decisive. Each secondary theorem is a useful
axiom-free semantic fact: ·13 introduces a witness into `sum`; ·14 eliminates
the universal semantic product; ·141 introduces the sum pointwise; and
·15/·151 prove the two expected inclusion characterizations. Nevertheless,
all endpoints are host implications or iff statements, not judgments of an
inductive PM derivation relation over relational syntax.

Gutenberg displays none of these five with a numbered bracket citation and no
separate demonstrations intervene. The active Lean bodies are direct lambda,
pair, or existential proofs and invoke no numbered PM declaration. Printed,
Lean, and normalized graphs are therefore exactly empty for every item. This
does not license constructors named after the results: such constructors would
assume the five theorems and fail T3/T6.

Cumulative result after two lots: 0/10 v1-complete, 10/10 explicitly blocked,
with all ten host theorems retained only as secondary declarations.
