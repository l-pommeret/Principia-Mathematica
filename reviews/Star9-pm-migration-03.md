# ✱9 PM migration — lot 03

Scope: ✱9·03, ✱9·04, ✱9·05, ✱9·06, and ✱9·07, the next five axiom-free ✱9 entries in report order.

All five printed entries are marked `Df`. They are therefore classified `pm-definition-v1`, not `pm-derivation-v1`. Each Lean declaration is a reducible syntax abbreviation whose body is the printed definiens in `FirstOrder` or `SecondOrder`; none is an inductive judgement theorem, and none receives an assertion constructor.

The rebuilt dependency graph is empty for all five definitions. Their bodies use only the syntax constructors that constitute their definiens. This is intentionally distinct from a derivation dependency: T2–T4 of the derivation tier do not pass, because these declarations are definitions rather than theorems and make no object-judgement claim. They are retained only at the definition tier.
