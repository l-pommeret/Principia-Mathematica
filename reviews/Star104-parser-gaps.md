# PM II ✱104 parser gaps

The ten items in catalogues 03 and 04 were tested individually against the PM
syntax parser without altering their diplomatic `printed` readings.

Exactly two fail:

- ✱104·102 is rejected with `missing closing matrix brace before offset 32`;
- ✱104·112 is rejected with `missing closing matrix brace before offset 34`.

Both formulas use PM's braced type-index specialization in `Nc{(...)α}ʻα`.
The printed brace is balanced; the failure is the current parser treating the
subscript-like `α` before `}` as part of an unsupported matrix-brace form.  The
other eight new formulas parse successfully and therefore carry no exemption.
Parser status is independent of their strict semantic promotion verdicts.
