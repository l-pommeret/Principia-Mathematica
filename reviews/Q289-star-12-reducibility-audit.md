# Q289 — ✱12·1 and ✱12·11 reducibility audit

The canonical witness is first-edition volume I, scan leaf 196, printed page
174.  Both propositions are labelled `Pp`: in PM they are primitive instances
of the axiom of reducibility, not derived theorems.

The Lean file preserves each displayed existential function quantifier, every
argument place, and pointwise formal equivalence.  Its interpretation is
explicitly an embedding into Lean's ordinary, unramified function spaces:
`Predicative₁ α = α → Prop` and `Predicative₂ α β = α → β → Prop`.  Under this
embedding the source matrix itself is the required witness, so both results
are proved by reflexivity.  This is the standard collapse of the ramified
distinction in simple type theory; it must not be read as a derivation of PM's
primitive proposition inside PM's ramified object theory.

No axiom, placeholder, unsafe declaration, choice principle, or hidden premise
is added.  Both declarations compile with the pinned Lean 4.30.0 kernel.

Parser audit: for ✱12·11 the coverage parser mistakes the function-quantifier
scope `(∃f) :` for the start of a nullary occurrence and reports `φ` as bare.
The diplomatic text explicitly applies both functions to `(x, y)`. This is a
reviewed parser-grammar gap; the binary source statement remains unchanged.
