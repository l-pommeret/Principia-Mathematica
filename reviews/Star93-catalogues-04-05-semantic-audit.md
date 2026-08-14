# ✱93 catalogues 04–05 — strict source/Lean semantic audit

Scope: ✱93·116, ·117, ·118, ·13, ·131, ·132, ·21, ·22,
·221, and ·23 (printed pages 610–611, scan leaves 632–633). Every
reading agrees with its unique canonical `PM-VERBATIM` block.

| PM locus | verdict | semantic finding |
|---|---|---|
| ✱93·116 | exact, awaiting CI | Extensional form of the already exact maximum-membership expansion. |
| ✱93·117 | exact, awaiting CI | Both printed equalities between converse boundary and maximum of converse-domain/field are present. |
| ✱93·118 | exact, awaiting CI | Exact inclusion of maximum in the class intersected with the field. |
| ✱93·13 | exact, awaiting CI | The converse-domain of identity restricted to the field normalizes to the field itself, yielding the printed boundary equality. |
| ✱93·131 | exact, awaiting CI | Preserves converse-domain, relation square/composition, class difference, and equality orientation. |
| ✱93·132 | refused | Lean adds `cod T ⊆ field P`; without it the reverse direction cannot supply minimum's field conjunct. PM prints no such antecedent. |
| ✱93·21 | refused | `Potid P T` is definitionally `True`, so the generated family forgets the printed power-identity restriction. |
| ✱93·22 | refused | The existential Potid witness plus boundary equality is passed wholesale as `h`, assuming generated-family membership. |
| ✱93·221 | refused | Lean adds `h : Potid P P`, while local `Potid` is degenerate; PM's membership is unconditional. |
| ✱93·23 | refused | Arbitrary `H` replaces the printed minimum-image family, and the target characterization is itself premise `h`. |

The manifests are homogeneous and contain five records each: catalogue 04 has
**5 exact awaiting CI**, catalogue 05 has **5 refused**. No ID is copied to a
sidecar, and all CI evidence remains pending.

Accepted declarations use only earlier exact local declarations or
definitions. The extracted edges are recorded explicitly: ·116→·115,
·117→·112, and ·13→·112; ·118 and ·131 are locally closed. Refused
declarations' empty graphs do not cure their extra assumptions or degenerate
definitions. No historical dependency relaxation is claimed.
