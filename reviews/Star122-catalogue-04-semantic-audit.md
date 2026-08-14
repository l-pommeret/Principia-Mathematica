# ✱122 catalogue 04 strict semantic audit

Scope: PM2:✱122·22, ·23, ·231, ·24, and ·25 on printed pages
258–259 (scan leaves 298–299), checked against Gutenberg 78255 and the named
declarations in `Star122Kernel.lean` / `Star122NextKernel.lean`. All five are
refused; the split is homogeneous.

- **·22** proves uniqueness of a member outside the converse-posterity image
  of a subclass. Lean instead proves comparability by custom `Reach` for any
  two members of a subset of its field; its conclusion is not equality.
- **·23** proves existence and characterizes the minimum of a nonempty subclass.
  Lean repeats the unrelated three-way comparison already used for ·21.
- **·231** says a class included in its own converse-posterity image is empty.
  Lean assumes pointwise emptiness and returns that same hypothesis verbatim.
- **·24** identifies the domain of a power of a progression with an ancestral
  image of its initial class and its generators. Lean is only `n ≤ n` for a
  natural-number segment.
- **·25** makes the ancestral restriction of a power into a progression and
  identifies its first member. Lean unfolds `segment n k` to `k ≤ n`.

No source object needed by these propositions is interpreted in the surrogate
targets. Accepted Lean dependency graphs are empty and no item is promoted.
