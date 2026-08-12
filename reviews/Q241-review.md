# Audit Q241 — PM I, ✱4·82–✱4·85

Verdict: **KERNEL-CHECKED LOCAL**. Source: first edition, vol. I,
p. 127, leaf 149; SHA-256
`afdca6640d248e94fc93bd1144afa53935688c80c995072602ab9493b3cae767`.

The first two antecedents are products of implications, not implication
chains. The last two transport equivalent antecedents or consequents. Preserve
the note linking ✱4·82·83 to ✱4·43. No print defect or material digital-witness
error is established. Confidence high.

The four exact targets `star_4_82` through `star_4_85` are integrated in the
canonical `Star4` module.  Their closure uses only the existing numbered PM
propositions and the context-sensitive primitive detachment branches already
present in the repository.  In particular, ✱4·82 follows ✱2·65 / Imp /
✱2·21 / Comp; ✱4·83 follows ✱2·61 / Imp / Simp / Comp; and ✱4·84·85
transport the two components of equivalence by ✱2·06 and ✱2·05 respectively,
then package them through ✱3·47.  The note linking ✱4·82·83 to ✱4·43 is
retained in the theorem documentation.

Local kernel gate (Lean 4.30.0):
`PATH=/Users/user/.local/lean-4.30.0/bin:$PATH lake build Principia.FirstEdition.Volume1.Part1.SectionA.Star4`
succeeded with 10 jobs.  Remote CI evidence remains required before changing
this verdict to remotely certified.
