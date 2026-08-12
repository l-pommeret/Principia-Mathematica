# Q280 canonical integration audit

The diplomatic source on PM I p. 162 (scan leaf 184) contains five items.
The exact Raw endpoints of ✱11·32, ✱11·33, ✱11·34, and ✱11·341 are
implemented in `Principia/Architecture/Star11Q280Kernel.lean`.  Their two
successive typed binders preserve the order fixed by ✱11·01/✱11·03, and the
certificates are closed over the printed iterations of ✱10·27, ✱10·271,
✱10·28, and ✱10·281.  No generic Raw assertion, detachment, or conversion
constructor is exported.

✱11·311 is not promoted.  It is a metalinguistic conjunction rule under
function-significance and same-type conditions, and its only printed proof is
“as in ✱10·13.”  The latter still lacks an indexed assertion: packaging a
self-equality target around it would not prove the authorial rule.  Q280 thus
adds four exact closed canonical certificates while retaining ✱11·311 as an
explicit architecture dependency rather than reporting a false success.

Local evidence: Lean 4.30.0 accepts the targeted module with no warnings or
placeholders.  Online evidence remains pending until the integrating commit is
covered by the Lean workflow.

Parser audit: the coverage parser reports “function `φ` has no argument” for
✱11·32.  This is a grammar gap caused by the colon immediately following the
two-variable binder `(x, y) :`; both occurrences of `φ` are visibly applied as
`φ(x, y)` in the diplomatic transcription.  The item therefore carries a
reviewed-gap marker rather than weakening or rewriting the source text.
