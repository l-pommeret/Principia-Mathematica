# Audit Q255 — PM I, ✱9·12–✱9·15

Verdict architectural actuel: **BLOQUÉ — ne pas soumettre**. ✱9·12 est une
règle primitive de détachement aux nouveaux ordres; ✱9·13 une règle primitive
de généralisation réel→apparent; ✱9·131 une définition récursive en huit
clauses de «same type»; ✱9·14 et ✱9·15 des Pp de significativité et
d’existence syntaxiques. Le socle actuel ne possède encore ni individus,
fonctions/application, propositions générales par ordre, ni dérivations à ces
ordres. Son jugement `Significant` mesure seulement l’occurrence syntaxique et
ne doit pas être confondu avec «significant» au sens PM. La clause (4) a été
recollationnée comme `u = φx̂∨ψx̂`, `v = φx̂∨φx̂`.

Verdict: **PREPARED — architecture review and Q252 context required**.
Source: first edition, vol. I, pp. 137–138, leaves 159–160. ✱9·12 and ✱9·13
are metalinguistic inference principles; encoding either as an ordinary
formula would contradict PM's explanation. ✱9·131 has eight indispensable,
step-indexed same-type clauses. ✱9·14 concerns preservation of significance
under same-type replacement and ✱9·15 links a significant value with its
function. No PM erratum is established. Wikisource's `is/if`, `aboce/above`,
and `one ore/or more` are digital defects only and do not belong in the
canonical source. Confidence high on the source; architecture remains gated.

## ✱9·12 and ✱9·13 promotion

The assigned-first-order constructors `OrderedAssertion.star_9_12` and
`OrderedAssertion.star_9_13` are now kernel-checked at immutable commit
`a773a806b9759f571ce5ddaaa781d28553fc11b5`, GitHub Actions run
`31575922684`. This certifies only their fixed first-order scopes and their
explicit capture-safe carrier operations; it does not certify the separate
higher-order/function/significance items ✱9·131, ✱9·14, or ✱9·15.

## ✱9·131 architecture audit for ✱10·13

The printed ✱9·131 is a stepwise **definition of “being of the same type”**,
not an assertion rule.  Its clause (2) classifies elementary functions by the
types of their argument places, and clause (4) classifies disjunctions of
such functions.  In the canonical syntax these clauses are already enforced
by the indices of `Apparent Γ Δ`: two matrices accepted at the same `Γ, Δ`,
and their `Apparent.disj`, cannot differ in argument-place type.

This yields no inhabitant of the judgement required by ✱10·13.  Concretely,
`SameAssignedType φ ψ` (or the stronger fact that `φ` and `ψ` share the exact
Lean carrier) has no eliminator into `OrderedAssertion`; nor should it have
one, because ✱9·131 says nothing about asserted truth.  The existing
`OrderedAssertion` constructors likewise contain no adjunction case for two
arbitrary asserted open values.  Therefore a dedicated ✱9·131 constructor
returning the conjunction assertion would not formalize the printed
definition: it would silently add the missing inference rule.  Q266 ✱10·13
must instead derive that adjunction from its cited propositional proofs at the
correct assigned order, or await a separately source-audited fixed-order
transport of those proofs.
