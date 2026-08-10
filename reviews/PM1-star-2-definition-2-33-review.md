# Audit ✱2·33 — association of iterated disjunction

The first-edition scan (volume I, printed p. 110, scan leaf 132) reads:

`p ∨ q ∨ r .=. (p ∨ q) ∨ r     Df`

followed by: `This definition serves only for the avoidance of brackets.`

The Project Gutenberg and Wikisource witnesses agree with the canonical scan
on the association and wording. No authorial printing error was found, so no
`sic` or critical-apparatus correction is warranted.

## Formal audit

Before this item, Lean declared `∨ₚ` with `infixr`, which silently parsed an
unparenthesized `p ∨ₚ q ∨ₚ r` as `p ∨ₚ (q ∨ₚ r)`, contradicting the
explicit definiens of ✱2·33. The declaration is now `infixl`; all earlier
three-place uses in the checked Lean corpus have explicit parentheses, hence
their abstract syntax is unchanged. `star_2_33` is an abbreviation for the
left-associated tree, not a derivable proposition or an object-language
equality.

Status: source audit A; formal validation awaiting GitHub CI.
