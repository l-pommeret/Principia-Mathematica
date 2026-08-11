# Editorial conventions

## Canonical edition

The initial corpus is the first edition, volumes I–III (1910, 1912, 1913).
Second-edition material (1925–1927) is an explicit variant and never silently
alters the first-edition development.

## Source and formal layers

The diplomatic, page-by-page transcription is canonical. Lean files reproduce
it in delimited `PM-VERBATIM` comments, checked automatically against that
transcription. Editorial notes and formal glosses are always separate.

Every formula has three distinguishable forms: the printed PM formula, a term
of the inductive PM syntax, and an optional interpretation as a Lean
proposition. Similar rendering is not evidence that these forms coincide.

Each item records the edition, volume, printed page, scan leaf and URL, source
image checksum, transcription checksum, verification status, and editorial
interventions. Suspected misprints are recorded, never silently corrected.

## Critical apparatus

The repository distinguishes the canonical printed witness from derived digital
witnesses. A discrepancy is classified before any marker is displayed:

- `authorial-print-sic`: an apparent error actually present in the canonical
  1910–1913 printing; the diplomatic text is preserved and the reading is
  displayed with `[sic]` in the reader-facing edition;
- `digital-witness-error`: an OCR, TeX, or transcription error absent from the
  canonical scan; it is attributed to that digital witness and never marked as
  an error by Whitehead or Russell;
- `editorial-correction`: a supplied corrected reading, always separate from
  the diplomatic reading;
- `variant`: a reading from another impression or the second edition;
- `uncertain`: insufficient evidence; no silent choice is made.

Apparatus records use standard labels where applicable: `sic`, `corr.`, `conj.`,
`lege`, `om.`, and `add.`. Every record gives an exact locus, diplomatic reading,
proposed or witnessed reading, witness sigla, evidence, editor, date, and status.

`[sic]` is never inserted into the canonical byte-for-byte transcription. It is
rendered from the linked apparatus record, so fidelity checks remain possible.
It may be assigned only after checking the scan and at least one independent
witness or second physical copy. A suspicious OCR string alone can never justify
`sic`.

## Anomaly register

`metadata/anomalies/PM1-anomaly-register.json` is distinct from the official
Errata register. It captures provenance failures found while editing or
formalizing: unconfirmed printed errors, incomplete printed citations, notation
ambiguities, digital-witness errors, and reconstruction gaps. Each record pins
the printed and added reading, canonical leaf/reading hash, affected AST and
batch, strict-audit result, any minimal relaxation, Lean impact, and review.

The register is deterministic: every apparatus entry classified
`digital-witness-error` is imported with a link back to that apparatus notice;
the remaining source-audited cases live in `metadata/anomalies/manual/`.
`scripts/verify_anomaly_registry.py` rejects a stale generated register, an
unlinked digital witness error, an official Errata duplicate, or a claim that a
rejected strict reconstruction was accepted. Add a manual record as part of
every new reconstruction/source audit before any Aristotle continuation is
considered.

Provider transport/status failures are retained separately as
`infrastructure_incidents`. They carry project and task identifiers, the raw
observed sequence, and an authoritative-status gate; they are explicitly not
PM or reconstruction anomalies and never justify a duplicate submission.

Witness sigla initially used by the project are:

- `PM1-1910-SCAN`: facsimile of volume I, first edition (canonical witness);
- `PG78050`: Project Gutenberg HTML/TeX transcription (derived witness);
- `WS-PM1`: Wikisource transcription and page facsimile (derived witness).
- `PM2-1912-SCAN`: facsimile of volume II, first edition (canonical witness);
- `PG78255`: Project Gutenberg HTML/TeX transcription of volume II (derived
  witness).

The apparatus is cumulative and immutable: a superseded judgment remains in
history and is replaced by a new reviewed record rather than silently rewritten.

## Stable names

The editorial ID preserves volume and printed label, for example
`PM1:✱2·01`. Lean names follow the printed hierarchy, for example
`PM.FirstEdition.Volume1.Star2.p01`; they never introduce a competing
mathematical numbering.

## Planned conservativity at ✱9

The ✱9 kernel has a deliberately separate apparent-variable syntax in
`Principia.Syntax.Apparent`. Its intrinsically typed de Bruijn indices make
capture impossible by construction, while `ofElementary` and the checked
partial inverse `toElementary?` expose the intended conservative inclusion of
the elementary fragment. `Apparent` contains matrices; the generic
`Quantified` constructor performs exactly one assigned order step and keeps
PM's primitive `always` and `sometimes` binders injectively distinct.

This foundation is not itself a claim that PM's extension is conservative.
It contains no new derivation rules, no semantic Lean quantifiers, and no
generic hierarchy ranging over all proposition orders. The two equations of
first-order negation are kernel reductions corresponding to ✱9·01 and ✱9·02;
the bracket omissions of ✱9·011 and ✱9·021 remain notation only. Disjunction
with one elementary operand is likewise represented by two direction-sensitive
operations whose four constructor reductions correspond exactly to ✱9·03–06.
No commutativity or inference principle is hidden in those operations.
Disjunction between two quantified orders and metalinguistic rules will be
introduced only at their audited PM loci. For ✱9·07–08, the implementation
receives renaming and disjunction explicitly for one fixed matrix family,
uses separate de Bruijn embeddings for the outer `x` and inner `y`, and then
constructs exactly two `Quantified` layers. This supports PM's stated
repetition at an assigned higher order without positing a polymorphic
object-language connective over all orders. Metalinguistic rules remain
absent. The later metatheory must prove the
relevant erasure or model theorem before the edition labels the extension
conservative or derives a relative-consistency result.
