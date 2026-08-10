# Substitution, schemata, and the two rules of inference

This edition makes an explicit editorial distinction between three operations
that are all commonly described as “substitution.” They are not identified in
the Lean development.

## 1. Schematic instantiation in ✱1–✱5

The parameters of a declaration such as

```lean
PM.Derivation.star_1_4 (p q : PM.Elementary Γ)
```

represent PM's schematic letters. A printed instruction such as
`[Perm ∼p, ∼q/p, q]` is transcribed by applying that declaration to the two
displayed formulae. Thus Lean's universal parameter instantiation is the
editorial representation of a printed *instance of a schema*. It is not an
object-language constructor, and the elementary calculus contains no generic
`substitute` rule.

This choice records faithfully which instance PM prints, but it does not settle
the historical question whether PM possessed an additional tacit substitution
rule. In particular, a Lean theorem obtained by supplying parameters must not
be cited as evidence that PM stated substitution as a primitive proposition or
primitive rule. The edition will preserve printed substitution annotations in
the source and dependency metadata so that this convention remains auditable.

## 2. ✱1·1 and ✱1·11 are primitive inference rules

`PM.Derivation.star_1_1` and `PM.Derivation.star_1_11` are distinct constructors
of `PM.Derivation`:

- ✱1·1 detaches between asserted definite elementary propositions, whose real
  context is empty;
- ✱1·11 detaches between asserted elementary propositional functions and
  requires an explicitly nonempty real-variable context.

The convenience theorem `PM.Derivation.detach` dispatches on the context and
uses exactly one of those constructors. It is an editorial interface, not a
replacement primitive. Consequently the use of Lean parameters to instantiate
a schema does not erase PM's separate “axiom of identification of type.”

## 3. Object-syntactic substitution from ✱9 onward

`PM.Apparent.substitute` and `PM.Apparent.instantiate` are different machinery.
They recursively transform the encoded PM syntax, act on de Bruijn variables,
and lift beneath the primitive `always` and `sometimes` binders to avoid
capture. These operations are required because the real/apparent distinction
and binder scope are themselves objects of PM's theory in ✱9. They must never
be implemented merely by applying a Lean theorem to different parameters.

The same separation is retained in the experimental ramified syntax:
renaming, capture-free apparent substitution, and instantiation are explicit
syntax operations. Any future rule that licenses a syntactic substitution must
appear as its own derivation constructor or proved admissibility theorem, with
the relevant order and type restrictions; it may not be smuggled in through
Lean elaboration.

## Audit invariant

The repository's substitution guard checks that:

1. ✱1·1 and ✱1·11 remain separate `Derivation` constructors with their distinct
   context restrictions;
2. uniform `detach` still invokes both historical constructors;
3. `Elementary` does not acquire a generic syntax-substitution operation;
4. the apparent-variable layer retains explicit capture-free `rename`,
   `substitute`, `instantiateSubstitution`, and `instantiate` operations.

This is an encoding convention, not a claim that the historical controversy
about PM's unstated substitution practices has been resolved.
