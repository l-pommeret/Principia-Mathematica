# ✱114 catalogue 01 strict semantic audit

Scope: exactly PM2:✱114·01, ·1, ·11, ·12, and ·2. The printed text was
checked against Project Gutenberg 78255, first-edition pp. 124–125 (scan
leaves 164–165). The audit compares propositions, not theorem names or loose
modern analogies. All five proposed correspondences are refused.

- **✱114·01.** PM defines the cardinal product as `Nc` of the selection
  relation `∈Δʻκ`. Lean defines `CardinalProduct F` as the dependent
  function type `ClassProduct F` and proves the alias by reflexivity. No PM
  cardinal object, `Nc`, or selection relation is represented.
- **✱114·1.** The printed theorem repeats that cardinal identity. Lean's
  equality with `((i : I) → F i)` is again only the unfolding of its type
  alias. It is not an exact typed rendering of `Ncʻ∈Δʻκ`.
- **✱114·11.** PM gives a biconditional characterization of membership in
  the cardinal product via similarity to the selection relation. Lean instead
  maps a supplied choice function to pointwise `Nonempty` witnesses. It
  contains neither cardinal membership nor similarity and changes both the
  hypotheses and conclusion.
- **✱114·12.** PM asserts that the specific selection relation belongs to
  its cardinal number. Lean accepts an arbitrary dependent function and wraps
  that same function in `Nonempty`; the canonical PM object and membership
  assertion have disappeared.
- **✱114·2.** PM's product has no factors (`κ = Λ`) and equals cardinal
  one. Lean uses the inhabited index type `Unit`, hence one factor `A`, and
  proves product existence iff `A` is inhabited. Empty and singleton index
  families are not interchangeable here.

The opening kernel is a useful modern choice-function model, but it provides
no interpretation map from PM cardinal objects and selection relations to its
types and propositions. Consequently metadata wording cannot make these five
declarations source-exact. They remain `prepared`; none is promoted to
`awaiting-ci`. The refusal sidecar deliberately records empty Lean dependency
graphs because none of the declarations is accepted as a formalization of the
corresponding printed item.
