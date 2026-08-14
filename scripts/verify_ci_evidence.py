#!/usr/bin/env python3
"""Make recorded CI provenance resolvable instead of merely well-shaped."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ITEMS = ROOT / "metadata" / "items"

SHA = re.compile(r"[0-9a-f]{40}")
RUN_URL = re.compile(r"https://github\.com/[^/]+/[^/]+/actions/runs/[0-9]+")
PENDING = "pending"

#: Statuses that legitimately carry all-pending evidence.
UNCERTIFIED = frozenset({"prepared", "awaiting-ci", "lean-typechecked", "unbuilt"})

#: Reported when a batch has no CI run at all.  This is a fact about the
#: evidence, so criterion T7 always fails on it and no item of the batch can
#: reach the top tier — but it is not, by itself, a *false* claim: a batch that
#: says "pending" and certifies nothing is honest bookkeeping.  The gate below
#: therefore reports it only when the batch also claims certification, while the
#: tier computation reads the reason directly and stays a pure function of the
#: evidence.
NO_RUN_YET = (
    "no CI run has verified this batch (commit, run and conclusion are all "
    "pending)"
)


def _git(*arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *arguments], cwd=ROOT, capture_output=True, text=True, check=False
    )


@lru_cache(maxsize=None)
def commit_exists(sha: str) -> bool:
    return _git("cat-file", "-e", f"{sha}^{{commit}}").returncode == 0


@lru_cache(maxsize=None)
def is_ancestor_of_head(sha: str) -> bool:
    return _git("merge-base", "--is-ancestor", sha, "HEAD").returncode == 0


@lru_cache(maxsize=None)
def last_commit_touching(path: str) -> str | None:
    result = _git("log", "-1", "--format=%H", "--", path)
    sha = result.stdout.strip()
    return sha or None


def evidence_failures(
    batch_path: Path, evidence: dict, items: list[dict]
) -> list[str]:
    """Reasons the batch's CI evidence cannot be trusted.  Empty list = sound.

    This never repairs a claim.  A fabricated forty-hex string that happens to
    share a prefix with a real commit is reported, not silently corrected:
    provenance may not be inferred.
    """
    reasons: list[str] = []
    commit = evidence.get("commit")
    run = evidence.get("run")
    conclusion = evidence.get("conclusion")

    if {commit, run, conclusion} == {PENDING}:
        # All-pending evidence means no run has verified this batch, and that is
        # a fact about the evidence alone.
        #
        # This used to be reported only when the batch already recorded a
        # certified item, which made the criterion depend on the very statuses
        # it is used to compute: `--write` promoted an item, T7 then failed
        # because the batch certified something, the tier dropped back, T7
        # passed again, and the two answers alternated on every pass.  A tier
        # that depends on what is currently written down is not computed, it is
        # negotiated — so the question is asked of the evidence and nothing else.
        #
        # Failing here costs an uncertified item nothing: T7 alone yields
        # `awaiting-ci`, and any structural failure dominates it.
        reasons.append(NO_RUN_YET)
        return reasons

    # A batch that certifies nothing yet carries recorded evidence is stale
    # bookkeeping, not a false claim — and treating it as a T7 failure created a
    # deadlock: an item could not be certified because T7 failed, and T7 failed
    # because no item in its batch was certified.  Provenance is judged on
    # whether the recorded evidence resolves, never on how many items claim it.

    if not isinstance(commit, str) or not SHA.fullmatch(commit):
        reasons.append(f"commit {commit!r} is not a 40-hex object name")
    elif not commit_exists(commit):
        reasons.append(
            f"commit {commit} does not exist in this repository "
            "(a prefix collision with a real commit is not provenance)"
        )
    elif not is_ancestor_of_head(commit):
        reasons.append(f"commit {commit} is not an ancestor of HEAD")
    else:
        for item in items:
            lean_path = item.get("lean_path")
            if not lean_path or item.get("formal_status") in UNCERTIFIED:
                continue
            touched = last_commit_touching(lean_path)
            if touched and not _git(
                "merge-base", "--is-ancestor", touched, commit
            ).returncode == 0:
                reasons.append(
                    f"evidence commit {commit[:12]} predates the last change to "
                    f"{lean_path} ({touched[:12]}): the certified file was edited "
                    "after the run"
                )
                break

    if not isinstance(run, str) or not RUN_URL.fullmatch(run):
        reasons.append(
            f"run {run!r} is not a full GitHub Actions run URL "
            "(a bare numeric id is the signature of a promotion that bypassed "
            "scripts/promote_awaiting_ci.py)"
        )

    if conclusion != "success":
        reasons.append(f"conclusion is {conclusion!r}, not 'success'")

    return reasons


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report-all", action="store_true", help="list every failure before exiting"
    )
    arguments = parser.parse_args()

    paths = sorted(ITEMS.glob("*.json"))
    if not paths:
        print(f"no catalogue files under {ITEMS}", file=sys.stderr)
        return 1

    failures: list[tuple[str, list[str]]] = []
    affected = 0
    for path in paths:
        batch = json.loads(path.read_text(encoding="utf-8"))
        items = batch.get("items", [])
        reasons = evidence_failures(path, batch.get("ci_evidence") or {}, items)
        # A batch awaiting its first run is not a provenance failure: it claims
        # nothing.  It becomes one the moment an item in it says it is certified.
        if reasons == [NO_RUN_YET]:
            certified = {
                item.get("formal_status") for item in items
            } - UNCERTIFIED - {None}
            if not certified:
                continue
            reasons = [
                f"{NO_RUN_YET}, yet the batch certifies {sorted(certified)}"
            ]
        if reasons:
            failures.append((str(path.relative_to(ROOT)), reasons))
            affected += len(items)
            if not arguments.report_all:
                break

    if failures:
        for relative, reasons in failures:
            print(f"{relative}:", file=sys.stderr)
            for reason in reasons:
                print(f"  {reason}", file=sys.stderr)
        print(
            f"\n{len(failures)} catalogues ({affected} items) carry CI evidence "
            "that does not resolve",
            file=sys.stderr,
        )
        return 1
    print(f"CI evidence verified ({len(paths)} catalogues)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
