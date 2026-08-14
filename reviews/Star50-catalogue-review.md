# ✱50 source catalogue review

The fifty-three items are checked against Project Gutenberg 78050 on printed
pages 350–355 (scan leaves 372–377).  Definitions ·01 and ·02 map to the real
Lean constants `I` and `J`; all other IDs resolve uniquely to numbered
declarations. The first batch (·01, ·02, ·1, ·11, ·12) has now passed strict
item-level semantic audit and is `awaiting-ci`; later batches remain
`prepared` pending semantic promotion.

For the audited batch, `Relation α := α → α → Prop` preserves both relation
arguments. `I` is exactly equality, `J` is exactly its pointwise complement,
and ·1, ·11, ·12 are respectively the two pointwise expansions and the
extensional diversity-relation identity. All five proofs are definitional
(`rfl`/`Iff.rfl`), so no mathematical premise is assumed. Their dependency
metadata records the definitions actually unfolded; printed abstraction,
complement, and extensionality citations that elaborate definitionally are
retained explicitly as reviewed indirect/unused steps rather than erased.

The second batch (·13–·17) has also passed strict audit and is `awaiting-ci`.
The assigned type is explicitly inhabited for ·13, matching PM's existential
use of identity. The theorem ·14 represents the descriptive value equation by
an explicit witness `y` plus existence and uniqueness; ·15 universally gives
the same unique fibre. The image definition has PM's argument orientation, so
·16 is exactly `Iʻʻα = α`. Finally ·17 assumes, for every member of `α`, both
the self-pair and uniqueness expressed by `Rʻx = x`, and proves exactly the
image equality. No implication is weakened and no premise is hidden.

The third batch (·2, ·21–·24) passes strict audit and is `awaiting-ci`.
Converse is argument reversal and inclusion is pointwise, exactly matching PM.
Symmetry of equality and inequality proves ·2, ·21 and the two converse
equivalences ·22–·23. Inclusion in diversity at ·24 is equivalent in both
directions to irreflexivity. No assumption or implication is weakened.

The fourth batch (·3, ·31–·34) passes strict audit and is `awaiting-ci`.
Identity reflexivity gives ·3 and supplies each object's witnesses for the
domain, converse-domain and field equalities ·31–·32. At ·33, a witnessed
unequal pair is sufficient to construct a distinct partner for every object,
so all three diversity extensions are universal. For ·34 the PM restriction
to classes becomes diversity on `ClassExtension α`; under the explicit
inhabited assigned-type convention there are distinct empty and universal
classes. The conclusions and hypotheses match without weakening.

Forty-one formulas use relation abstraction/complement, converse, restriction
(`◁/▷`), product (`∥`), or dotted relation operators beyond the current parser
grammar.  Those items carry `reviewed-gap`; no diplomatic reading is weakened
to make the parser accept it.

The fifth batch (·35, ·4, ·41–·43) passes strict audit and is `awaiting-ci`.
Under the inhabited assigned-type convention already used at ·34, ·35
constructs two distinct relations, exactly witnessing diversity on relations.
Composition is oriented consistently: ·4 gives both identity laws, ·41 retains
all three equivalent asymmetry/disjointness members, ·42 is identity
idempotence, and ·43 is the square/converse form of asymmetry. No direction or
member of an equivalence is dropped.

The sixth batch (·44–·47, ·5) also passes strict audit and is `awaiting-ci`.
At ·44 a diagonal witness for `R` supplies the repeated intermediate witness
for `R²`; ·45 and ·46 are the two printed irreflexivity consequences; and ·47
retains the explicit transitivity premise and both biconditionals. At ·5 the
two typed restrictions of identity agree pointwise and their double
restriction is the same relation. All hypotheses and chained conclusions are
preserved.
