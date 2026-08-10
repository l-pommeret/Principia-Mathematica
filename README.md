# Principia Mathematica in Lean

Source-critical Lean edition of Whitehead and Russell's *Principia
Mathematica*. The first canonical target is the first edition (1910–1913).

The project keeps distinct: the historical English text, a typed abstract
syntax reproducing PM, derivations in a reconstructed PM calculus, and
interpretations or metatheorems proved in Lean.

Every item retains its original starred number and page-level provenance. A
proof is accepted only after Lean and CI checks, with no `sorry`, `admit`, unsafe
escape hatch, or unrecorded axiom.

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
