# Q230 kernel-link continuation — preserve the opaque interface

The previous output explicitly escaped the submitted opaque ✱4·01 interface
by importing an archive-local printed definition of equivalence.  This retry
must not do that.  Deliver only `star_4_3`, `star_4_31`, `star_4_32`, and
`star_4_33` against the reviewed kernel declarations.

- `star_4_3`: `Star3.star_3_22`.
- `star_4_31`: `Star1.star_1_4`.
- `star_4_32`: `PM.Elementary.imp`, `PM.Elementary.conj`, existing
  `Star4.star_4_11`, `star_4_12`, `star_4_15`, `star_4_22`.
- `star_4_33`: `Star2.star_2_31`, `Star2.star_2_32`.

No local `equiv`, `equivChain`, `equivIntro`, `equivImp`, `adj`, helper,
module, import, or dependency copy is allowed.  No `Classical`, `axiom`,
`sorry`, `admit`, or `unsafe`.  If opacity makes a target underivable, return
the exact missing kernel declaration; do not redefine the interface.
