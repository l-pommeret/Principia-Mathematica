# Q310 review — PM I ✱14·02, ✱14·03 and ✱14·04

**Verdict: A — strictly remapped and kernel-checked.** These are
the smallest remaining reductional definitions in the source-only Q297 lot.
They are collated from first-edition volume I, printed p. 182, leaf 204,
SHA-256
`23427375b6f708a53ed91a28fb43eed247d732ff4047ee7e88fd779e2a50ad28`,
with independent Project Gutenberg 78050 witness.

✱14·02 is represented by `descriptionExists`, which reduces to the exact
formula `(∃b):(x):φx≡x=b`; it is not a semantic predicate applied to a
description term. ✱14·03 reduces a comma bracket to two nested
`descriptionScope` nodes in printed order. ✱14·04 makes the later explicitly
bracketed description the outer scope; it is not asserted as a commutation
theorem. All candidates are intrinsically typed de Bruijn indices.

The three Aristotle targets are reductional and have empty whitelists. Their
accepted bodies must be `rfl` or auditably identical definitional reductions;
they may not cite the regression lemmas `star_14_02_reduction`,
`star_14_03_reduction`, or `star_14_04_reduction`. The Q296 countermodel is
absent and supplies no proof permission.

The retry archive was audited as three `rfl` bodies, its supplied context was
byte-identical to the sealed interface, and every declaration was remapped
one-to-one to the corresponding `PM.FirstEdition.Volume1.Star14Source`
declaration. The resulting canonical transplant and the full edition were
kernel-checked by CI
[31529111742](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31529111742)
at commit `3167dacbec913db5d4e2471de6d2a5fc6460bec8`. The earlier exact isolated context and full
edition were kernel-checked successfully by CI
[31517498507](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31517498507)
at commit `f5fafdf6ec8003a0a70be5a4b69ca79383742c59`.

The derived items ✱14·18/·21 and every item in Q298/Q299/Q302 remain blocked:
they require an assertion/derivation layer for contextual descriptions,
identity, and existence which this reduction-only module deliberately does
not introduce.
