# Audit Q217 — PM I, ✱3·01–✱3·03 foundations

Verdict: **A — Aristotle result integrated; exact printed closure confirmed,
awaiting repository CI**. The immutable final archive is
`aristotle/results/Q217-final.tar.gz`, SHA-256
`b2ac2d081c5d61b2bfb0f116656fd0c4c6f573b25ed110dcd49be002f60cfec0`.
Its target uses exactly ✱1·01, ✱1·11, ✱1·7, ✱1·72, ✱2·11, ✱2·32 and the
reviewed correction ✱3·01; it adds nothing and leaves no printed event
uncovered. Mechanical evidence is in `Q217-reconstruction-audit.json`.
No `sorry`, `admit`, new axiom or unsafe declaration occurs in the returned
source; the only `Classical` occurrence is in Aristotle's generated harness,
outside the integrated target.

Sources: first edition, vol. I,
pp. 114 and 116, leaves 136 and 138. SHA-256 of the Wikimedia 1920 px JPEGs:
leaf 136 `2d592ee0372fd62e7d41c0260e3da50cea813616a91ba89dfd27453875792b1b`;
leaf 138 `c18eb6890dc92335e8df8773cbd46b8e98c2e550cdcb01f91a397bed27e9958b`.

✱3·01 defines `p·q` as `∼(∼p∨∼q)`. ✱3·02 defines the printed chain
`p⊃q⊃r` as `(p⊃q)·(q⊃r)`; it must never be parsed as right-associated
implication. ✱3·03 combines two asserted elementary propositional functions
of the same real-variable type and must be a theorem of `Derivation`, not a
new constructor or axiom.

The source gate omitted by the earlier prompt is substantive. PM prints:

- ✱1·7: if `p` is elementary, `∼p` is elementary, Pp;
- ✱1·71: if `p,q` are elementary, `p∨q` is elementary, Pp;
- ✱1·72: if `φp,ψp` are elementary propositional functions on elementary
  propositions, `φp∨ψp` is such a function, Pp.

The prose following ✱3·03 explicitly invokes ✱1·7 and ✱1·72 before ✱2·11,
then says ✱3·03 is the useful form of the axiom of identification of real
variables and applies to two or more variables. The current `Elementary Γ`
AST internalizes formation in Lean's type checker, so these Pp cannot yet be
represented as historical rules. Adding a redundant predicate whose proofs
are unused by ✱3·03 would only falsify the dependency audit. Q217 therefore
remains outside the generated Aristotle queue until a separate formation
judgement, and its honest connection to assertion, survives kernel CI.

That feasibility gate is now satisfied experimentally. Module
`Principia.Experimental.ElementaryFormationToy` introduces distinct
constructors for ✱1·7, ✱1·71 and ✱1·72; the latter requires a nonempty real
context, while ✱1·71 is restricted to the empty context. `Formation.ofElementary`
reconstructs a formation history recursively without a generic disjunction
constructor. The formation-aware ✱3·03 returns both its formation proof and its
`PM.Derivation`; its compatibility projection to the accepted API factors
through that object rather than duplicating the derivation or discarding a dead
formation witness. Mutation tests reject both shortcuts.

GitHub CI kernel-checked the bridge and the unchanged full corpus at commit
`01d3ef23bc5ec7b427a4cbdf76f66682fd19e36a`, run
[`31449618624`](https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31449618624),
conclusion `success`. This proves architectural compatibility, not yet canonical
integration: the numbered source items, verbatim blocks, metadata and generated
isolated Q217 context remain to be installed before Aristotle submission.

Critical locus `PM1:✱3·03:dem-line-3-reference`: the 1910 scan reads
`(✱3·03)` in the third line of its own demonstration. The explanatory text and
the displayed formula require the definition ✱3·01. Classification:
**uncertain**, apparent print error; conjectural correction `✱3·01`. Preserve
the printed reading in canonical bytes and render any marker only from the
apparatus. A second independent physical witness is still required before
`authorial-print-sic`. PG78050 repeats the circular reference but is a derived
witness and its transcription also corrupts several φ/ψ occurrences; those
are separate `digital-witness-error` readings. Confidence high on the scan,
high on the formal scope, provisional on the final critical classification.
