# ✱110 catalogue 01 strict semantic audit

The first five numbered propositions of ✱110 were collated against the
first-edition Volume II scan, printed page 77 (scan leaf 117), with Project
Gutenberg 78255 as a second witness. The source presents relationally
constructed, mutually exclusive copies of two classes and proves their
similarity properties. The existing Lean file instead defines a tagged sum and
assigns these five historical numbers to unrelated elementary facts about its
constructors and inhabitedness.

None of the five declarations is eligible for canonical promotion:

- `star_110_1` replaces PM's characterization of a relation `R` by case
  analysis on a tagged-sum element;
- `star_110_101` replaces the printed disjointness theorem by an emptiness
  equivalence;
- `star_110_11` and `star_110_12` replace, respectively, disjointness and two
  similarity assertions by the left- and right-tag membership reductions;
- `star_110_13` replaces the printed disjoint-union similarity theorem,
  including all three hypotheses, by a bare inhabitedness equivalence.

These are semantic and theorem-identity failures, not harmless changes of
representation: the Lean conclusions do not imply the printed conclusions and
do not encode their principal relation/similarity claims. All five records
therefore remain `prepared` with explicit refusal statuses. There is no
`awaiting-ci` item in this catalogue.

Dependency review is necessarily source-only for this refused lot. The
printed references retained in the manifest are ✱38·13·131 and the defining
✱110·01 at ·1, and ✱73·41·61·611 at ·12; no Lean dependency graph is
credited because none of the declarations proves its assigned source theorem.

All five diplomatic formulas are routed as `reviewed-gap`: the current parser
does not yet cover the arithmetical class-sum sign or the historical relational
image/application notation. This records a parser limitation only and does not
alter the source transcription.
