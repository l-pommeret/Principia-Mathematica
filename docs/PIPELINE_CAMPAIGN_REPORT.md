# Principia Mathematica Lean campaign report

## Scope and trust policy

This repository is a source-critical Lean edition of the first edition of
*Principia Mathematica*.  The campaign keeps four states distinct:

1. diplomatic source transcription;
2. prepared or architecture-blocked Lean target;
3. locally kernel-checked reconstruction;
4. remotely CI-certified reconstruction published in the reader edition.

A result is never promoted merely because Aristotle reports completion.  Exact
statements, historical dependencies, absence of `sorry`, `admit`, new axioms
and unsafe escapes, local Lean elaboration, repository preflight, and remote CI
are checked independently.

## Pipeline

`pipeline.json` is the remote-task manifest.  `metadata/items/*.json` is the
reader-edition catalogue.  The safe operator is `campaign.py`:

```sh
python3 campaign.py browser probe
python3 campaign.py aristotle status --readonly Q238
python3 campaign.py aristotle download QID aristotle/results/ARCHIVE.tar.gz
python3 campaign.py ci latest
python3 campaign.py ci view RUN_ID
python3 campaign.py ci run --ref main --workflow lean.yml
python3 campaign.py ci run --ref main --workflow edition-preview.yml
python3 campaign.py book build
```

The local minimal toolchain is Lean 4.30.0:

```sh
export PATH=/Users/user/.local/lean-4.30.0/bin:$PATH
lake build
python3 scripts/verify_preflight.py
```

One monitoring cycle reconciles browser tabs, Aristotle tasks and immutable
archives, Git state, local Lean, CI, metadata inventory, and publication.  Work
is scheduled in dependency-closed parallel waves; a freed worker immediately
takes the next prerequisite or batch.  Shared modules are merged centrally and
receive one global build/preflight per wave to reduce latency and token use.

## Repairs made during this resumption

- Located the minimal local Lean installation after the shell `PATH` omitted
  it; the full project builds locally.
- Fixed `campaign.py book build`, which incorrectly invoked an obsolete RMS
  LaTeX renderer and failed on `build_sections`.  It now builds and verifies
  this repository's static reader edition.
- Rebuilt 1,136 formal-item pages and 81 source-block pages; all 1,217 pages
  passed site verification.
- Deployed the corrected Pages edition successfully in run `31609565549`.
- Reconciled Aristotle state, preserved active Q238 without duplicate
  submission, and downloaded fourteen terminal archives immutably.
- Preserved unrelated pre-existing untracked prompts and contexts.

## Lean integration wave Q240–Q244

Commit `ca068cb` integrates the completed local wave:

- Q240: exact ✱4·78 and ✱4·79 in `Star4Q240.lean`; ✱4·8 and ✱4·81 were
  already canonical.
- Q241: exact ✱4·82, ✱4·83 and ✱4·84 in canonical `Star4.lean`; ✱4·85 was
  already present.
- Q242: exact ✱4·86 integrated against canonical Star2/Star3 dependencies;
  ✱4·87 and ✱5·1 were already present.
- Q243: exact ✱5·14 added to `Star5Kernel.lean`; ✱5·11–✱5·13 were already
  present.  Its route is Add → ✱2·16 → ✱2·21 → ✱1·6 → ✱2·54.
- Q244: deliberately not promoted.  Its Aristotle bodies were conditional on
  missing canonical links.  The remaining prerequisites are ✱3·43 and
  ✱4·21, ✱4·41, ✱4·51, ✱4·61, ✱4·63, ✱4·65; these form the next parallel wave.

The combined local project completed 54 Lean jobs and the aggregate preflight
passed.  Lean CI run `31610796073` is the immutable remote certification for
commit `ca068cb` once it reaches a successful terminal state.

## Publication and continuation

After each successful Lean CI, replace `awaiting-ci` evidence with the exact
commit and run, regenerate `metadata/queue_inventory.json`, run the aggregate
preflight, then dispatch `edition-preview.yml`.  Never label an item
`kernel-checked` while its CI fields remain pending.

The durable campaign goal remains active until the catalogued first-edition
targets—and subsequently the Volume II and III architecture-dependent
targets—reach honest terminal states.  Architecture-blocked items remain
visible as source transcriptions with explicit blockers rather than fabricated
proofs.

## Progress through ✱10 (12 August 2026)

The campaign subsequently closed the late ✱4 and ✱5 prerequisites, the
structural ✱9 quantifier/function layer, and a first substantial ✱10 wave.
The canonical catalogue now contains 184 remotely certified items and 54
additional locally kernel-checked items awaiting metadata dependency audit and
CI promotion: 238 of 1,136 items have Lean bodies (20.95%).  The distinction is
intentional: a green build certifies code, while promotion additionally
requires complete `lean_dependencies`, normalized historical citations, and
immutable CI evidence for every metadata batch.

Notable ✱10 closures include definitions ✱10·01–03; propositions ✱10·1,
✱10·11–12, ✱10·121–122, ✱10·2, ✱10·21–29, ✱10·3, ✱10·301, ✱10·31,
✱10·311, ✱10·33–41, ✱10·411–412, and selected ✱10·52/541/542 instances.
Targets that still require an unaudited assertion rule, type/significance
bridge, substitution rule, or witness-combination principle remain explicitly
`prepared`; target syntax alone is never counted as a proof.

Commit `fb0ad88` passed all 21 aggregate preflight gates, 235 unit tests and 62
Lean build jobs, and was certified by Lean CI run `31618145905`.  Later commit
`bef97d6` adds the exact ✱10·33 conjunction-composition certificate plus the
next audited targets/proofs and awaits its own CI before any promotion.
