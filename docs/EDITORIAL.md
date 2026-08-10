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

## Stable names

The editorial ID preserves volume and printed label, for example
`PM1:✱2·01`. Lean names follow the printed hierarchy, for example
`PM.FirstEdition.Volume1.Star2.p01`; they never introduce a competing
mathematical numbering.

