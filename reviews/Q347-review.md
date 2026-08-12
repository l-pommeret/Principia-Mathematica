# Q347 exact class-closure audit

PM I p. 220 / scan leaf 242 is canonical and PG 78050 agrees. No apparatus
or `[sic]` is required; the two printed “Similar proof” notices are retained
as historical dependency evidence.

`Star22Q347Kernel.lean` uses the exact extensional class operations already
introduced at ✱22·02--04. In the repository's documented unramified embedding,
classhood is existence of an extensionally equal predicate representative.
Consequently union and complement are closed by their own predicate matrices
(✱22·37/38), while ✱22·39/391/392 are literal reductional equalities for
intersection, union, and complement of class abstractions.

No membership case, operand, or equality direction is omitted. The proofs
are polymorphic and constructive and use no `Classical`, choice, new axiom,
`sorry`, oracle, or set-theoretic universe. The historical PM proof chains
remain in metadata; direct reduction replaces them only under explicit
reviewed-closure records.
