# Audit Q227 — PM I, ✱4·01–✱4·02, ✱4·1, ✱4·12, ✱4·13

Verdict: **PREPARED — contexte noyau requis**. Sources: first edition, vol. I,
pp. 120–122, leaves 142–144. SHA-256: leaf 142
`07cb1459178b04ceb27512333bd3a8ee8cd2055cb8abc6efa973568f65d133a3`;
leaf 143 `95d6946a9ca568061123df63f32b694ac0440528ed74db45bce6478d45bf39e2`;
leaf 144 `54cd7fe266d38746d15a927a0a83c62da77742373576b596e5469f77f13cb17e`.

✱4·01 is the definition `p≡q := (p→q)·(q→p)`. ✱4·02 is the special
three-place chain definition `p≡q≡r := (p≡q)·(q≡r)`. Neither is an asserted
formula or a Lean `Prop`. The proved scopes are `(p→q)≡(¬q→¬p)`,
`(p≡¬q)≡(q≡¬p)`, and `p≡¬¬p`.

Digital apparatus: Wikisource leaf 142 corrupts the summary occurrence of
✱4·01 as `p≡q .=. p⊃q⊃p`, dropping the printed `.q` before the second
implication. The scan and the repeated definition on leaf 144 both read
`p≡q .=. p⊃q.q⊃p`. Classify this only as `digital-witness-error`; canonical
bytes follow the scan and receive no `[sic]`. No print defect is established.
Confidence high.
