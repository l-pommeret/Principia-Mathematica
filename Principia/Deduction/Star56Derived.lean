namespace PM.RamifiedSyntax

/-!
# Derived propositions of PM I, ✱56

The 50-item diplomatic catalogue is present in `Star56Source.lean`.  Its three
opening definitions and all subsequent assertions concern cardinal classes.
The current ramified derived layer exposes neither their eliminable contextual
class definitions nor the earlier class-theoretic derivations on which their
proofs depend.  In particular `star_20_01` produces an
`incompleteScope`, not the class-valued `Term` needed as the argument of the
printed membership formulae.

No theorem is declared until the required object-judgement conversion and
dependencies exist.  This preserves T4 and avoids silently
replacing PM's cardinal-class assertions by host-logic propositions.
-/

end PM.RamifiedSyntax
