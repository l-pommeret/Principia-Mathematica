# ✱32 catalogue 09 T2–T4 strict semantic audit

The four opening definitions ✱32·01–·04 remain refused for formal promotion.
They are preserved verbatim in `Star32Source.lean`, but the canonical catalogue
review explicitly identifies them as the four source-only loci, in contrast
to the 38 propositions with bijectively mapped Lean declarations.

The several architecture modules contain convenient local helpers named
`rightSection`, `leftSection`, `sg`, and `gs`. Those names alone are not exact
formal targets. In particular, the helpers `sg R` and `gs R` directly return
section families, whereas the printed ·03 and ·04 define relations by class
abstracts over both a family `A` and a relation `R`. No declaration reconstructs
those displayed abstracts. The duplicated helper definitions across modules
also provide no unique canonical mapping for ·01 or ·02.

Accordingly all four items stay `prepared` and
`blocked-no-canonical-declaration`, with individual blocking reasons. No
substitute theorem is inferred, no item is promoted, and the catalogue remains
homogeneously refused without a split.

Under the current computed gate, T2 fails because there is no canonical mapped
declaration for any of the four source items. T3 and T4 also cannot be
established: there is neither a PM object-language judgment endpoint nor a
concrete reading that links each exact printed definition to a parsed AST.
Moreover these are `Df` items, so introducing theorem constructors for them
would be invalid; a future faithful implementation must expose audited `def`
unfolding semantics. Their printed, Lean, and normalized dependency graphs are
all empty.
