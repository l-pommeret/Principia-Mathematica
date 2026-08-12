# Audit Q260 — PM I, ✱9·34

Verdict: **AWAITING CI — closed exact narrow judgement**.  The source is the
first edition, vol. I, p. 141, leaf 163.  The diplomatic demonstration has
four explicit stages: ✱1·3 gives `φx ⊃ p∨φx`; ✱9·13 closes that matrix; ✱9·21
is applied to the displayed pair `φ` and `p∨φ`; and ✱9·04 supplies the final
spelling `p∨(x).φx`.

`Star934Kernel.derive` retains lines (1) and (2) as `OrderedAssertion`s and
uses only the fixed normalized-canonical ✱9·21 witness for that pair.  Since
the latter cannot be generally reified into the older order-one carrier, the
result is a theorem-specific `Star934KernelAssertion`, not an
`OrderedAssertion` or generic Raw detachment rule.  No print defect is
established; confidence in the source reading is high.
