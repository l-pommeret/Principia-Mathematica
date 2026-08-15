# Principia Mathematica in Lean

Source-critical Lean edition of Whitehead and Russell's *Principia
Mathematica*. The first canonical target is the first edition (1910–1913).

The project keeps distinct: the historical English text, a typed abstract
syntax reproducing PM, derivations in a reconstructed PM calculus, and
interpretations or metatheorems proved in Lean.

Every item retains its original starred number and page-level provenance.

## What "certified" means here

A certification tier is *computed* from the Lean sources, never asserted. The
top tier, `kernel-checked`, is reserved for items that meet the standard the
✱1–✱5 layer already meets: the module is in the import closure that `lake build`
kernel-checks; the statement is a judgement of an inductive derivation relation
whose constructors are exactly PM's printed primitive propositions; a companion
reading ties the catalogue's printed formula, character for character, to the
abstract syntax tree the theorem asserts; the asserted formula uses PM's own
connectives rather than Lean's; `#print axioms` reports nothing; the statement is
neither vacuous nor a duplicate; the recorded CI evidence resolves to a commit
that exists and predates no edit of the file it certifies; and every non-logical
assumption reached — reducibility above all — is declared.

A separate check asks the harder question: whether the proof follows the
demonstration PM actually prints, by reading the elaborated proof term and
requiring that everything the printed demonstration cites appears in it. Its
default scope is only `kernel-checked` and `awaiting-ci`: 133 of 6203 catalogue
items; `lean-typechecked` items are therefore not compared with their printed
demonstrations.

The criteria, the tier vocabulary, and what each tier does and does not license
a reader to believe are set out in
[`docs/CERTIFICATION_TIERS.md`](docs/CERTIFICATION_TIERS.md). The lower tiers are
deliberately unflattering: `lean-typechecked` means a declaration of that name
compiles and nothing more is claimed, and most of the catalogue sits there or
below. `scripts/verify_certification_tier.py --report` prints the current census;
`scripts/report_derivation_frontier.py` shows which unformalised propositions
block the most work.

The whole apparatus rests on 23 printed primitive propositions, all in ✱1, ✱9,
✱10, ✱11 and ✱12. Everything else is derived from those, so no chapter can be
reconstructed before the propositions its demonstrations cite exist.

Printed statements and demonstrations can be compiled into deterministic,
strict prover manifests. See
[`docs/CONSTRAINED_RECONSTRUCTION.md`](docs/CONSTRAINED_RECONSTRUCTION.md): the
printed citations form the proof whitelist, while their transitive compilation
closure is tracked separately and grants no additional proof permission.
The audited grammar and its current limits are recorded in
[`docs/PM_PARSER.md`](docs/PM_PARSER.md).

Aristotle credentials must exist only in `ARISTOTLE_API_KEY` or the macOS
Keychain. They must never occur in tracked files, prompts, manifests, logs,
archives, or command-line arguments.

## Experimental ramified-type vertical slice

`Principia.Experimental.RamifiedToy` is an isolated architecture test for
explicitly ramified function types. It is not source-critical coverage of any
numbered PM proposition, and the accepted `Elementary`, `Apparent`, and
`Derivation` modules do not import it. Reducibility is available only as an
explicitly passed `UnaryReducibility` value, never as a global axiom.
Its connection with the accepted elementary syntax is only a syntax embedding
with a partial retraction; no deductive conservativity theorem is claimed.
The current vertical slice is kernel-checked at commit `2f88937` by Lean CI
run `31434813268`. This validates only the exercised experimental declarations;
the remaining discriminating tests are tracked in
[`docs/ARCHITECTURE_GATES.md`](docs/ARCHITECTURE_GATES.md).

The separate editorial convention for schematic instantiation, ✱1·1/✱1·11,
and capture-free syntactic substitution is recorded in
[`docs/SUBSTITUTION.md`](docs/SUBSTITUTION.md).

`Principia.Experimental.TypicalAmbiguityToy` adds a separate minimal test for
typical ambiguity. One class proposition is parameterised by a reified PM
`RamifiedSort` and instantiated both for individuals and for predicative unary
functions of individuals. Its negative check establishes only sort separation
and sort-preserving substitution; it is not yet a reconstruction of the full
type-schematic convention used throughout the class calculus.

`Principia.Experimental.DescriptionScopeToy` is a still smaller feasibility
test for incomplete symbols. A description can occur only together with the
continuation that consumes its witness; expansion eliminates it into an
existence-and-uniqueness formula. A two-object countermodel separates both the
negation readings from the Introduction and the exact narrow/wide implication
shapes printed on ✱14 p. 181 when the description fails to denote. The source
shapes are scan-collated, but this remains an experimental HOAS gate rather
than the eventual canonical ✱14 syntax; de Bruijn substitution tests still
remain necessary.

`Principia.Experimental.PredicativeGateToy` tests the next architectural
boundary directly against the printed shapes of ✱12·1, ✱12·11, ✱13·01, and
the first reducibility-dependent move of ✱13·101. General applications and
predicative applications are distinct constructors in the proposition AST;
their renaming and substitution operations preserve that distinction.
Reducibility is supplied as an explicit unary or binary package whose
certificate is indexed by the same marked syntax. This remains an experimental
gate, not canonical coverage of ✱12–✱13 or a completed proof of ✱13·101.
The earlier marked-witness slice was kernel-checked at commit `cbef6d9` by Lean
CI run `31436937560`. The current refinement represents ✱12 itself as a scoped
object-language existential and is kernel-checked at commit `81d086c` by Lean
CI run `31437661828`. The exact scope ASTs supporting ✱10·23 and ✱10·27 are
kernel-checked at commit `c6c0e96` by Lean CI run `31437950385`; they do not yet
carry derivations.
