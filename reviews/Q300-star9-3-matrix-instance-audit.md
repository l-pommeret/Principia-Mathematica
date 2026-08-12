# Audit — the ✱9·21 matrix instance used in ✱9·3

The first-edition proof of ✱9·3 is on printed p. 140, scan leaf 162.  Its
line (4) is

```text
⊢ :(x):. φx ∨ (y).φy :⊃ φx,
```

and the next displayed application is

```text
⊢ .(4).✱9·21. ⊃ ⊢ :(x): φx ∨ (y).φy :⊃ (x).φx.       (5)
```

Thus the occurrence of ✱9·21 is an instance of its theorem schema with
matrix arguments

```text
α(x) = φx ∨ (y).φy,       β(x) = φx.
```

The left argument contains a first-order quantified subformula and is not an
`Apparent` value.  This authorizes a **matrix-level theorem-schema
instantiation**, not a new primitive proposition and not a polymorphic
`OrderedAssertion` constructor.  Any Lean implementation must therefore
keep (i) Raw substitution syntax, (ii) the source theorem derivation, and
(iii) the specialized reification/transport proof distinct.  The source does
not license an unrestricted detachment rule between arbitrary canonical Raw
formulae.

Witnesses: PM I (1910), p. 140 / leaf 162; proofread Wikisource page 162;
`aristotle/demonstrations/PM1-star-9-3.txt`.
