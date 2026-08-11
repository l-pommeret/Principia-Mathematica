# Audit Q220 — PM I, ✱2·82–✱2·86 selected sequence

Verdict: **A — accepted mixed strict/documented-relaxed reconstruction,
integrated and kernel-checked**.

Source: first edition, vol. I, p. 113, leaf 135; derivative SHA-256
`0015ae56c8a9c1eedab541d07e06d683c499319b60fa021d088077535f93f2f0`.
The AST follows ✱2·33 and therefore reads every unbracketed triple sum as
left-associated.

The deterministic proof parser generated independent whitelists:

- ✱2·82: ✱2·8, ✱2·81;
- ✱2·83: the preceding local result ✱2·82;
- ✱2·85: Add, Syll, ✱2·55, ✱2·83, Comm, ✱2·54;
- ✱2·86: the preceding local result ✱2·85;

plus the reviewed ✱1·11 convention wherever detachment is used. The isolated
20.3 kB context was kernel-checked at commit
`67663311e24ddd1ca3bdb267d36436ae674ca3bf`, GitHub run
[`31446802971`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31446802971),
conclusion `success`.

The first Aristotle result exposed a genuine fidelity issue. Its proof of
✱2·83 bypassed the printed citation ✱2·82 through a right-associated helper.
A constrained follow-up on the same project was therefore required. Project
`e0043584-c2b5-47fa-99a1-abc5339329c4`, final task
`0f7ff4c9-53c3-4ba1-b636-3936f39edb5b`; immutable final archive
`aristotle/results/Q220-followup-final.tar.gz`, SHA-256
`7a32207ec69edaa558bf0a3f07925c74111946af8961d44663d37b230697c61a`.
No `sorry`, `admit`, `unsafe`, `Classical`, new axiom, or semantic shortcut is
present.

The final transitive machine audit is recorded in
`reviews/Q220-reconstruction-audit.json`:

- ✱2·85 and ✱2·86 are strict closures;
- ✱2·82 covers both printed citations but additionally needs the already
  proved associativity apparatus ✱2·31·32 and its implementation closure;
- ✱2·83 now calls the required left-associated ✱2·82 and no longer reaches
  ✱2·8 or ✱2·81 through a hidden helper. It requires the same associativity
  apparatus to expose the right-associated disjunctions defining its nested
  implications.

Thus the two relaxed classifications are not proof-search escapes. They record
a precise historical gap: the printed demonstrations silently identify the
right-associated instances delivered by ✱2·8/·81 with the left-associated
notation explicitly defined by ✱2·33. The accompanying Aristotle archive also
contains finite-matrix independence checks for the literal restricted systems;
these are supporting metatheoretic evidence, not imported axioms or canonical
PM proofs.

The accepted bodies, full PM verbatim demonstrations, readings, and dependency
metadata were kernel-checked with the full edition at exact commit
`f7620f005e853910042932bdbc95b603df05e8ab`, GitHub run
[`31448777861`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31448777861),
conclusion `success`. The run also compiled every isolated Aristotle context
and passed the placeholder/unsafe rejection step.
