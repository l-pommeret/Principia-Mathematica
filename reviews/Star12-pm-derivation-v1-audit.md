# ✱12 PM-derivation-v1 audit

Scope: ✱12·1 and ✱12·11 only. Both are primitive propositions (`Pp`) on
first-edition page 174, not consequences inferred from earlier propositions.
This audit applies the Star2 completion standard: an exact PM AST plus a
kernel-checked assertion/derivation judgement is primary; an ordinary Lean
`Prop` theorem is secondary evidence only.

The existing `PredicativeGateToy` AST preserves the distinctions erased by the
old unramified translation: general application `φx` is a different
constructor from predicative application `f!x`; the existential function
binder and universal argument binders are explicit; ·11 has exactly two
ordered argument places rather than a variadic encoding. The new
`Star12ReducibilityDerivation.ReducibilityDerivation` judgement has exactly two
primitive constructors:

- `star_12_1` asserts only `unaryReducibilityFormula function`;
- `star_12_11` asserts only `binaryReducibilityFormula function`.

This is faithful to the printed `Pp` status. There is no semantic-truth
constructor, no conversion from arbitrary Lean propositions, no variadic or
arity-three reducibility rule, and no new axiom. The prior
`Star12Q289Reducibility` theorems remain linked as secondary typed statements;
they are not the PM derivation certificates.

The three dependency graphs were rebuilt from source. The printed graph and
normalized PM graph are empty because both loci are primitive propositions and
print no citations. Each Lean graph has exactly its corresponding primitive
`ReducibilityDerivation` constructor. No prior metadata edge was inherited.

Both primary declarations compile with Lean 4.30.0 and meet
`formalization_level: pm-derivation-v1`. Their former green evidence covered
only the secondary `Prop` translation, so CI evidence is reset to pending and
the items are `awaiting-ci`, not already kernel-integrated under the stronger
standard.

