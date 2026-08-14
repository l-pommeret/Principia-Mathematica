# ✱37 catalogue-10 semantic audit

All five declarations pass strict item-level semantic audit and are promoted
to `awaiting-ci`.

- ✱37·24 unfolds membership in the domain of `imageRelation R` to an actual
  image and proves pointwise that every member of that image lies in `domain R`.
- ✱37·261 is the converse of ·26 with exactly the expected type exchange: the
  converse-image is unchanged after intersecting its input with `domain R`.
- ✱37·262 uses equality of the two classes on `converseDomain R` to conclude
  equality of their images, with no converse direction or premise omitted.
- ✱37·263 is the exact converse analogue of ·262 and invokes the formal ·261.
- ✱37·264 reads PM's `∃!A` as the inhabitedness of a class, as defined at
  ✱24·03 rather than as unique existence of an element.  Both displayed
  equivalences are proved and share exactly the same related witness pair.

The Lean term for ·261 proves the equality directly rather than using the
printed substitution from ·26 and ✱33·21.  That historical edge difference is
recorded as a reviewed `printed_but_unused` relaxation.  The formal terms for
·262 and ·263 use precisely their printed predecessors.
