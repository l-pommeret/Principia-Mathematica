# Q221 follow-up — repair the printed dependency trace

Continue the existing Q221 project. Replace the returned `Q221.lean` with all
five declarations in their original order, preserving their exact targets and
the reviewed isolated context. The first archive compiled but failed the
mechanical printed-dependency audit; this continuation is about historical
fidelity, not discovering a shorter proof.

Do not add an axiom, theorem, helper theorem, notation, semantic argument,
`Classical`, `sorry`, `admit`, `unsafe`, or a changed target. Use only the
per-target whitelists in `Q221.md`. Do not alter `PMContext.lean`.

Keep ✱3·12 and ✱3·13 strict: their existing proof terms already satisfy the
whitelist and printed events.

For ✱3·1 and ✱3·11, retain `PM.FirstEdition.Volume1.Star2.star_2_08` and make
the printed definition ✱3·01 occur textually in each theorem body. Use an
explicit definitional reading such as `simpa only [PM.Elementary.conj] using
...` or an explicit `unfold PM.Elementary.conj`; do not introduce a logical
lemma. The exact dependency auditor must be able to see both `star_2_08` and
`PM.Elementary.conj` in each proof body.

For ✱3·14, do not close the target directly with `star_2_12`. Reconstruct the
printed `[✱3·1 . Transp]` route explicitly:

1. use the earlier local `star_3_1 p q`;
2. detach it from the ✱2·16 instance with antecedent `p ∧ₚ q` and consequent
   `∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))`, obtaining
   `∼ₚ (∼ₚ ((∼ₚ p) ∨ₚ (∼ₚ q))) ⊃ₚ ∼ₚ (p ∧ₚ q)`;
3. use ✱2·12 on `(∼ₚ p) ∨ₚ (∼ₚ q)`;
4. compose the two implications with ✱2·06 and explicit detachment (✱1·11).

Thus the ✱3·14 body must visibly contain `star_3_1`, `star_2_16`,
`star_2_12`, `star_2_06`, and `PM.Derivation.detach`; it must not be a direct
one-line application of `star_2_12`. This uses only its reviewed whitelist.

Return a complete compiling `Q221.lean` and a short account of the exact
dependencies used per target.
