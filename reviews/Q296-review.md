# Q296 review — PM I ✱14·01

**Verdict: A — interface-only reduction task.** The exact definition-in-use
has been collated from first-edition volume I, printed p. 181, scan leaf 203.
The canonical Commons derivative has SHA-256
`12a57b46d16f08df1de909a28f2cc91553861a1ea5d191922791e050fc0ebabc`;
Project Gutenberg 78050 independently witnesses the same wording and
definition. The PM-VERBATIM block and
`aristotle/demonstrations/PM1-star-14-01.txt` agree exactly.

## Exact formal scope

The sole target is the reduction

`[(℩x)(φx)]. ψ((℩x)(φx))`

to

`(∃b) : (x) : φx ≡ x=b : ψb`.

It is represented by
`PM.DescriptionSyntax.Formula.star_14_01`. The description is never a
`Term`; the printed bracket is `Formula.descriptionScope`; its condition and
continuation share an intrinsically typed de Bruijn candidate; and the result
is `CoreFormula`, in which no description constructor exists. There is no
additional `φb` conjunct: the target preserves PM's printed definiens rather
than a merely equivalent modern uniqueness formulation.

The definition is reductional. The accepted Aristotle body must be `rfl` (or
an auditably identical definitional reduction) and may not cite the existing
architecture regression lemma `expand_descriptionScope`. The separately
audited Boolean `DescriptionScopeToy` supplies only a countermodel separating
narrow and wide non-denoting readings; it is not a proof of ✱14·01 and is not
present in the Q296 context.

## Interface and promotion boundary

- Canonical architecture CI
  [31513533839](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31513533839)
  at commit `94a49e0` kernel-checked `Principia.Syntax.Description`.
- Q296's generated standalone context is provenance-hashed in
  `metadata/context_bundles/Q296.json`. Its own isolated CI evidence remains
  pending until the next consolidated run.
- The whitelist is empty: only definitional reduction is licensed. No PM
  theorem, semantic truth table, choice operator, `Classical`, axiom, unsafe
  declaration, placeholder, or countermodel theorem may occur in the body.
- A successful remote body remains interface-only. Canonical promotion is
  blocked until the returned declaration is audited and remapped one-to-one
  to `PM.DescriptionSyntax.Formula.star_14_01`, followed by online Lean CI.

Thus the former architecture blocker is resolved, but ✱14·01 itself is not
yet claimed as a canonical theorem.
