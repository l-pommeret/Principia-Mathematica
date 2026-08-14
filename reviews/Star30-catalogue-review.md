# ✱30 source catalogue review

The fifteen items in `PM1-STAR30-CATALOGUE-{1,2,3}` are diplomatic
transcriptions of the `data-tex` readings in Project Gutenberg 78050,
checked against printed pages 248–249 (scan leaves 270–271).  Their existing
Lean declarations are recorded as candidates, not promoted as semantically
audited proofs.

The deterministic PM parser currently consumes normalized Unicode PM syntax.
These blocks deliberately retain raw TeX delimiters and commands such as
`\(`, `\vdash`, `\colon`, and `\supset`; therefore their parser route is the
explicit `reviewed-gap` classification rather than a lossy rewrite of the
diplomatic bytes.

Catalogue batches 4–6 add the fourteen canonically transcribed final propositions
✱30·32–·52 (at most five per file). Their Lean declarations were semantically
audited, contain no pass-through certificates, and are synchronized as
`awaiting-ci`; CI evidence remains pending.

## Catalogue 1 object/judgement re-audit against the ✱2 standard

The five opening candidates ·12, ·13, ·14, ·141, and ·142 do **not** meet
the repository's ✱2 proof standard. In ✱2, the primary theorem type is an
object-language formula together with a `PM.Derivation` judgement (`⊢ₚ ...`),
and ordinary Lean `Prop` facts may only support that primary proof. The
declarations in `Star30ScopedDescriptionKernel.lean` return ordinary `Prop`
implications/equivalences over `Scope`; none constructs a PM object formula,
an assertion, or a derivation term.

This is a non-v1 gate: no proposition-specific `Support`, `Df`, certificate,
or derivation constructor has been introduced to manufacture an assertion.
Promotion requires a genuine chain from the audited ✱14 object-level results;
until that infrastructure exists, the honest status is blocked.

Consequently ·12, ·13, ·141, and ·142 are demoted from awaiting CI to
`prepared` / `blocked-missing-object-formula-and-pm-judgement`. Their Prop
theorems remain useful secondary lemmas only. ·14 remains refused for the
additional independent reason already identified: PM prints implication from
constant antecedent `p`, but Lean proves conjunction distribution.

The dependency graphs were rebuilt from the source terms. None of the five
Prop bodies calls an indexed PM proposition; calls to the private
`characterizer_unique` helper are secondary local infrastructure and create no
PM edge. Lean and normalized graphs are therefore empty. The printed citations
✱14·31, ·32, ·33, ·331, and ·332 are retained as fully qualified historical
dependencies and recorded as printed-but-unused relaxations. No CI evidence is
claimed. A v1 promotion requires the complete object formula and kernel-checked
PM judgement, not a relabeling of these Prop lemmas.

## Earlier catalogues 1 and 2 semantic audit (superseded for catalogue 1)

Catalogue 2 is now also superseded under the mandatory T1–T9 gate. The five
items ·15, ·16, ·17, ·18, and ·19 have useful axiom-free secondary `Prop`
theorems, but none has an object formula, concrete non-`Prop` reading, or an
inductive PM derivation. They therefore fail T3 and T4 and are returned to
`prepared` with explicit blocked status. No `Support`, `Df`, certificate, or
proposition-specific constructor is introduced. Promotion requires genuine
chains consuming ✱14·34, ·113, ·112, ·18, and ·15 respectively.

Their graphs were recomputed from zero. Those five printed ✱14 citations are
the complete historical graphs. The Lean bodies call no indexed PM theorem;
`characterizer_unique` in ·19 is private semantic infrastructure, so Lean and
normalized PM-derivation graphs are empty. Each printed citation is recorded
as printed-but-unused until a real object derivation consumes it.

Catalogue 3 receives the same mandatory T1–T9 treatment. Items ·2, ·21, ·22,
·3, and ·31 are all blocked: their declarations are secondary `Prop`
characterizations, with ·2 and ·3 additionally closing by reflexivity over
semantic abbreviations. They have no object formula, concrete reading, or PM
derivation. No new constructor is introduced to hide that absence.

The catalogue-3 graphs were rebuilt independently. The printed proposition
edges are ·2 → {✱4·2, ✱14·11}, ·21 → ✱14·203, and ·22 → ✱14·28; ·3 and ·31
print no citation. The parenthetical references from ·2, ·21, and ·22 to
definition ✱30·01 are recorded separately as `definition_dependencies`.
No body calls an indexed PM proposition, so all Lean and normalized
proposition graphs are empty.

Catalogue 1 accepts ✱30·12, ·13, ·141, and ·142.  Their `Scope` targets retain
the printed existence antecedent and respectively distribute disjunction,
negation, implication to a constant consequent, and equivalence through the
contextual description.  Each is promoted in the homogeneous awaiting-CI
sidecar.  ✱30·14 is refused and remains alone in the prepared catalogue: PM
prints distribution of `p ⊃ χ(Rʻy)`, but `star_30_14` proves distribution of
the conjunction `p ∧ φ`.  This connective substitution is substantive even
though the Lean proof itself is valid.

All five catalogue-2 items pass.  ✱30·15 distributes the constant conjunction;
·16 commutes the two independent scopes; ·17 is their exact two-witness
expansion; ·18 instantiates a universally true matrix at the existent described
value; and ·19 performs substitution under identity with that value.  The
contextual `Scope` representation introduces no arbitrary description-valued
term and drops no existence or uniqueness condition.  These five are promoted
in place to `awaiting-ci`.

The ten printed ✱14 citations are retained as historical edges.  The Lean
bodies instead expand `Scope` and use only the local uniqueness lemma, so the
accepted records carry explicit `relaxed-closure` evidence and empty Lean and
normalized numbered-proposition graphs.  The split partitions all ten IDs;
none is duplicated.

## Catalogue 3 strict semantic audit

All five remaining prepared candidates pass and are promoted in place to
`awaiting-ci`.  ✱30·2 is exactly the definition of existence of the associated
description by a witness satisfying the full relation/equality biconditional;
·21 expands this into existence plus pairwise uniqueness without weakening the
universal scope.  Proposition ·22 represents the printed equality with
`(℩x)(xRy)` contextually as `Scope R y (Characterizes R y)`, so it neither
chooses an arbitrary value nor omits the description's existence condition.

✱30·3 preserves the full pointwise biconditional characterizing identity with
the associated value.  ✱30·31 is its exact equivalent decomposition into
`R b y` and uniqueness of every related term.  The first three declarations
expand local contextual definitions directly; their printed ✱4/✱14 citations
therefore carry reviewed `relaxed-closure` evidence, while ·3 and ·31 have
empty graphs on both sides.  The catalogue remains homogeneous and no split or
duplicate metadata record is introduced.
