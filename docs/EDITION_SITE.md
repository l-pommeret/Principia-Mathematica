# Reader edition

The static reader is generated from the repository's audited sources, never
maintained as a second transcription. `metadata/items/*.json` supplies the
catalogue and provenance; `PM-VERBATIM` blocks supply the historical text;
Lean source supplies declarations and scope readings; apparatus JSON supplies
critical notes.

Build and inspect it without invoking Lean:

```sh
python3 scripts/build_edition.py
python3 scripts/verify_site.py
python3 -m http.server --directory site 8000
```

`site/` is disposable and ignored by Git. GitHub Actions performs the complete
editorial, Lean-policy, kernel, site-build, and link-verification sequence. It
retains a downloadable preview artifact for every run. A successful run on
`main` also deploys that exact generated tree to the `github-pages`
environment; repository Pages must use **GitHub Actions** as its source.

The facsimile panel links to the exact canonical scan leaf instead of copying
scan images into the repository. This keeps witness attribution explicit and
avoids presenting an unverified derivative image as canonical.
