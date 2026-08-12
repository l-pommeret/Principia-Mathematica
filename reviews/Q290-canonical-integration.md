# Q290 canonical integration

`PredicativeRange` and `Reducibility` keep separate the two source-critical
ingredients of this batch: the range of predicative propositional functions
in ✱13·01 and the reducibility principle cited only at the non-predicative
substitution theorem ✱13·101. Thus `star_13_01`, `star_13_02`, and `star_13_03` are the three
literal definitions; `star_13_1` is their formal-implication reading; and
`star_13_101` uses exactly one reducibility witness before applying ✱13·1.

The implementation deliberately does not identify PM identity with Lean's
built-in equality.  It adds no axiom, classical principle, choice operation,
unsafe declaration, or unrestricted substitution rule: reducibility remains
visible as model data, matching the printed dependency on ✱12·1.
