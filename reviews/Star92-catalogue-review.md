# ✱92 source catalogue review

The thirty-eight loci are checked against Project Gutenberg 78050 on printed
pages 602–606 (scan leaves 624–628). Every source ID resolves uniquely to an existing Lean declaration and remains `prepared` pending semantic promotion.

The parser accepts 6 formulas; 32 historical relation-power formulas carry `reviewed-gap`.

The first canonical batch (·1, ·101, ·102, ·11, ·112) was audited
source-to-Lean. None is strictly equivalent: the kernel defines `Potid` as
domain/codomain equality instead of PM's class of powers; moreover ·11 and
·112 omit PM's relational products and restriction identities. These five
therefore remain `prepared`, with the mismatch recorded item by item.

The second canonical batch (·113, ·12, ·121, ·13, ·131) was then
audited item by item. None is strictly equivalent. In ·113 Lean proves only
that restricting an arbitrary `Q` by two equal codomains gives the same
relation; it never represents `CnvʻR|Rpo|R`. In ·12 and ·121 it turns the
two conjuncts of the weakened `Potid` into a field inclusion, omitting the
printed relation-power equalities. In ·13 and ·131 it returns only equality
of the domains or codomains of `Q` and `T`, omitting the displayed products
and restrictions. All five remain `prepared` and carry an explicit blocked
semantic-mismatch integration status; there is no `awaiting-ci` promotion.

The third canonical batch (·132, ·14, ·141, ·142, ·143) also has no
strictly equivalent declaration. Lean ·132 returns the pair of field
equalities already encoded by its `Potid`; it omits PM's product inclusion.
Lean ·14 and ·141 replace genuine `Pot` membership plus a printed field
inclusion by the unrelated weakened `Potid` premise. Lean ·142 and ·143 have
the same displayed field equality as their respective PM conclusions only
because each equality is assumed as a conjunct of Lean `Potid`; the printed
field-inclusion premise and PM's power-or-identity semantics disappear. The
five items remain `prepared`, explicitly blocked for semantic mismatch, with
no `awaiting-ci` promotion.

The fourth canonical batch (·144, ·145, ·146, ·147, ·15) is likewise
refused in full. The first two recover field inclusions only through Lean's
weakened `Potid`, without PM's functionality and genuine power semantics.
The next two equate restrictions using an assumed field equality but do not
prove the printed restriction equals `T`. Lean ·15 simply assumes its entire
conclusion. All five remain `prepared` with explicit semantic blockers.

The fifth canonical batch (·151, ·152, ·153, ·16, ·161) also contains no
strictly equivalent formalization. Lean ·151–·153 are identity functions on
the exact product equality they purport to prove. Lean ·16 and ·161 choose
the product itself as an unrestricted existential witness; they omit witness
membership in `PotidʻR`, both displayed restriction alternatives, and all
printed antecedents. These five remain `prepared`; none is promoted to
`awaiting-ci`.
