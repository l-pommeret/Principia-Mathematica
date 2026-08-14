# ✱1 T10 inference and formation audit

This audit covers exactly `Derivation.star_1_1`, `Derivation.star_1_11`, and
`Formation.constant`, `Formation.realVar`, `Formation.star_1_7`,
`Formation.star_1_71`, `Formation.star_1_72` against the canonical first-edition
blocks on printed pages 98–101 (scan leaves 120–123).

The two inference constructors are exact and deliberately distinct. ✱1·1
detaches asserted definite elementary propositions in the empty real-variable
context. ✱1·11 performs the separately printed assertion rule for elementary
propositional functions in a nonempty context; its extension to several real
variables is explicitly licensed by the sentence immediately following the
printed rule. Neither constructor is an object-language implication axiom.

The three numbered formation constructors also preserve their printed kinds.
✱1·7 closes elementary formation under negation in the same typed context.
✱1·71 is disjunction formation for definite elementary propositions, hence
the empty real-variable context. ✱1·72 requires two functions in the same
explicit nonempty context, preserving PM's identification-of-type condition.

`Formation.constant` and `Formation.realVar` are not additional PM primitive
propositions. They are carrier base cases needed to reconstruct formation
evidence for the intrinsically typed elementary syntax. The former represents
the given elementary propositions discussed under the primitive ideas (even
though PM notes that no constant elementary proposition occurs in the logical
development); the latter represents real propositional variables. Their source
comments now state this editorial status and no metadata item or numbered edge
is invented for either constructor.

The five numbered records are therefore retained and normalized as exact
kernel-integrated primitive inference/formation rules. Legacy certification
objects describing an earlier `lean-typechecked` tier are removed rather than
left in contradiction with their current status.
