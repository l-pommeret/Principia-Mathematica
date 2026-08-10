# Architectural gates beyond ✱9

The first-order definitions at ✱9·01–·021 do not by themselves validate the
deep embedding for the later *Principia*. Before theorem production resumes at
scale, the following discriminating tests must pass in repository CI.

## 1. Schema instantiation and substitution

The convention is fixed in `docs/SUBSTITUTION.md`. Lean parameter
instantiation represents printed instances of the elementary schemata;
`star_1_1` and `star_1_11` remain distinct primitive constructors; and
capture-free substitution from ✱9 onward is an explicit syntax operation.

## 2. Predicative functions and reducibility

The printed distinction between `φx̂` and `φ!x̂` must survive in the AST. A
mere proposition saying that an otherwise identical function term has excess
zero is insufficient: general and predicative applications must remain
syntactically distinguishable and printable.

Reducibility must be supplied as an explicit, scoped hypothesis. For each
function to which it applies, it supplies a predicative representative and a
certificate of formal equivalence. It must never be a global instance, a
coercion lowering order, a definitional equality, or an unconditional
constructor of derivability.

Gate: formalize the exact source at ✱12, then prove one audited identity from
✱13 with an explicit reducibility parameter. Removing that parameter must make
the proof unavailable. Metadata must record the assumption directly and
transitively.

## 3. Typical ambiguity

PM type indices must be reified rather than hidden solely in Lean universes.
One type-schematic class proposition must be declared once and instantiated at
two genuinely different PM types (initially individuals and predicative
functions of individuals). Duplicating the declaration fails the gate.

The two instances must remain distinct, ordinary substitution between them
must be rejected, and later type-raising operations must be explicit. This is
required before ✱20 and is indispensable for the relative types of ✱63–✱65
and the cross-type cardinal constructions of ✱102–✱106.

## 4. Incomplete symbols and scope

Descriptions are not autonomous terms. The encoding must provide a contextual
scope constructor whose expansion implements the definition in use at ✱14·01.
Printed scope readings are editorial evidence, not a substitute for this AST.

Gate: in a separately audited small model, use a non-denoting description to
show that negation outside the description scope and negation inside its
continuation have different values. A mere syntactic inequality is too weak.
The same mechanism must later accept class and relation continuations for ✱20,
✱21, and ✱30 without introducing a second notion of scope.

## 5. Scoped non-logical assumptions

Item metadata needs an assumption ledger distinct from theorem dependencies.
The initial stable identifiers are:

- `PM1:REDUCIBILITY`;
- `PM2:INFINITY`;
- `PM2:MULTIPLICATIVE`.

Each use records the source locus, explicit Lean parameter, direct requirements,
and computed inherited requirements. CI must reject a source term that consumes
an assumption certificate without declaring it. The site and dependency export
must expose direct and inherited assumptions separately, so the edition can
answer mechanically which propositions depend on reducibility, infinity, or
the multiplicative axiom.

## Release discipline

The ramified toy is an experiment until these gates are individually audited.
A green toy build validates only the declarations actually exercised by its
tests. It does not promote numbered PM propositions, establish deductive
conservativity, or authorize silently extending the old `Elementary` calculus.
