# ✱33 parser gaps

## Imported ✱33 diplomatic blocks

The ✱33 diplomatic source currently preserves the imported TeX transcription
(`\\vdash`, `\\text`, and `\\breve`) verbatim.  The PM object-language parser
does not accept TeX control sequences.  This item therefore remains a reviewed
parser gap until the diplomatic layer and the normalized PM syntax are stored
separately.  The chapter's catalogue manifests route these imported TeX blocks
through this single reviewed gap; their Lean targets and editorial source
blocks are unaffected.
