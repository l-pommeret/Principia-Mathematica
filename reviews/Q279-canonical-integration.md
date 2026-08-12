# Q279 canonical integration

The five printed propositions are represented at their exact displayed
arity in `Star11Q279Kernel.lean`.  ✱11·25 is binary quantifier negation;
✱11·26 preserves the single witness that precedes the universal binder;
✱11·3 and ✱11·31 move only propositions independent of the two bound
variables.  ✱11·27's typographic chain is exposed as its two adjacent
equivalences (`star_11_27_left` and the catalogued `star_11_27`), both
definitionally equal under Lean's existential notation.

These are constructive Lean theorems.  No classical principle, function
significance assumption, axiom, unsafe declaration, or generic assertion
conversion is introduced.  The earlier architecture block was therefore
over-conservative: Lean's typed predicates already enforce the arity and
significance conditions needed by these five particular propositions.
