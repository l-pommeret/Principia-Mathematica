#!/usr/bin/env python3
"""The gates decide what may be called certified; they must not drift silently.

Every other gate in this repository judges the edition.  Nothing judged the
gates.  That asymmetry is the one an editor should worry about most: a gate is
the cheapest thing to weaken when it is inconvenient, and weakening one costs
nothing at the moment it happens while invalidating every certification made
afterwards.  This repository has already seen 969 items marked certified that
were not; the lesson was that a claim nobody can re-derive is worth nothing.

So each gate script is pinned here by SHA-256, and this check runs before any
other.  What it buys is precise and worth stating exactly:

* A gate edited by accident — or by an agent that found it easier to change the
  rule than to satisfy it — fails the build immediately, naming the file.
* A gate edited on purpose still passes, but only after its digest is updated in
  ``metadata/gate_integrity.json``.  That update lands in the same commit as the
  edit, so the diff says plainly: *this commit changed what counts as proof*.

What it does not buy: this is tamper-evident, not tamper-proof.  Anyone who can
edit a gate can also run ``--update``.  The protection is that they cannot do it
*quietly* — and combined with branch protection and CODEOWNERS review on
``scripts/verify_*``, a change to the standard becomes a decision someone signs
for rather than a line that slips through.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "metadata" / "gate_integrity.json"

#: Files whose content defines the standard.  Everything a gate imports belongs
#: here too: pinning `verify_certification_tier.py` while leaving
#: `pm_lean_index.py` free would pin the judge and release the evidence.
PROTECTED_GLOBS = (
    "scripts/verify_*.py",
    "scripts/pm_lean_index.py",
    "scripts/promote_awaiting_ci.py",
)

#: This script is pinned like the rest — a check that exempts itself protects
#: nothing — but its own digest is compared last, so that a tampered integrity
#: checker still reports the gates it was asked to protect before reporting
#: itself.
SELF = "scripts/verify_gate_integrity.py"


def protected_files() -> list[Path]:
    found: set[Path] = set()
    for pattern in PROTECTED_GLOBS:
        found.update(ROOT.glob(pattern))
    return sorted(found)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current() -> dict[str, str]:
    return {
        str(path.relative_to(ROOT)): digest(path) for path in protected_files()
    }


def recorded() -> dict[str, str]:
    if not MANIFEST.is_file():
        return {}
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    return payload.get("digests", {})


def differences(now: dict[str, str], before: dict[str, str]) -> list[str]:
    problems: list[str] = []
    for name in sorted(set(before) - set(now)):
        problems.append(
            f"{name}: pinned gate has been deleted. A standard is not retired by "
            "removing the file that enforces it; drop it from the manifest in the "
            "same commit, and say why in the message"
        )
    for name in sorted(set(now) - set(before)):
        problems.append(
            f"{name}: new gate is unpinned. Run "
            "`python3 scripts/verify_gate_integrity.py --update` and commit the "
            "manifest alongside it"
        )
    for name in sorted(set(now) & set(before)):
        if now[name] != before[name]:
            problems.append(
                f"{name}: content changed but the pinned digest did not "
                f"({before[name][:12]} -> {now[name][:12]}). If the change is "
                "intended, `--update` records it and the diff will show that this "
                "commit altered what counts as proof"
            )
    return sorted(problems, key=lambda line: line.startswith(SELF))


#: ANSI escapes, used only when stderr is a terminal.  A gate failure that
#: scrolls past unnoticed is a gate that does not exist.
_RED = "\033[1;31m"
_YELLOW = "\033[1;33m"
_RESET = "\033[0m"


def _colour(text: str, escape: str) -> str:
    return f"{escape}{text}{_RESET}" if sys.stderr.isatty() else text


def _banner(lines: list[str], escape: str = _RED) -> None:
    wrapped: list[str] = []
    for line in lines:
        wrapped.extend(textwrap.wrap(line, width=64) or [""])
    width = max(len(line) for line in wrapped) + 4
    print(_colour("╔" + "═" * width + "╗", escape), file=sys.stderr)
    for line in wrapped:
        print(
            _colour(f"║  {line.ljust(width - 4)}  ║", escape),
            file=sys.stderr,
        )
    print(_colour("╚" + "═" * width + "╝", escape), file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--update",
        action="store_true",
        help=(
            "re-pin every protected file to its current content. Refused unless "
            "--authorised-by and --reason are both given: changing a gate changes "
            "what counts as a proof of Principia Mathematica, and that is the "
            "editor's decision, not a build step"
        ),
    )
    parser.add_argument(
        "--authorised-by",
        metavar="NAME",
        help="the editor who expressly authorised this change of standard",
    )
    parser.add_argument(
        "--reason",
        metavar="TEXT",
        help="why the standard is being changed (recorded in the manifest)",
    )
    parser.add_argument("--report-all", action="store_true")
    arguments = parser.parse_args()

    if arguments.update and not (arguments.authorised_by and arguments.reason):
        _banner([
            "REFUSÉ — modification du standard non autorisée",
            "",
            "Re-pinning the gates changes what may be called a derivation",
            "of PM. It requires the editor's express authorisation:",
            "",
            "  --authorised-by <name> --reason <why>",
            "",
            "Both are recorded in metadata/gate_integrity.json and travel",
            "in the commit, so the change of standard is signed for.",
        ])
        return 2

    files = protected_files()
    if not files:
        print(
            "no gate script found; the integrity check would pass vacuously",
            file=sys.stderr,
        )
        return 1

    now = current()
    if arguments.update:
        before = recorded()
        changed = differences(now, before) if before else []
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        history = []
        if MANIFEST.is_file():
            history = json.loads(MANIFEST.read_text(encoding="utf-8")).get(
                "authorisations", []
            )
        history.append(
            {
                "authorised_by": arguments.authorised_by,
                "reason": arguments.reason,
                "scripts_changed": [line.split(":")[0] for line in changed],
            }
        )
        MANIFEST.write_text(
            json.dumps(
                {
                    "note": (
                        "SHA-256 of every script that defines the certification "
                        "standard. Changing a gate is legitimate; changing one "
                        "without updating this file is not, and the preflight "
                        "refuses it. Update lands in the same commit as the edit "
                        "so the diff shows that the standard itself moved. Every "
                        "re-pinning records who authorised it and why."
                    ),
                    "authorisations": history,
                    "digests": now,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        _banner(
            [
                "STANDARD MODIFIÉ — autorisé par "
                + str(arguments.authorised_by),
                "",
                f"raison : {arguments.reason}",
                f"scripts re-épinglés : {len(changed) or len(now)}",
            ],
            _YELLOW,
        )
        print(f"pinned {len(now)} gate scripts in {MANIFEST.relative_to(ROOT)}")
        return 0

    before = recorded()
    if not before:
        print(
            f"{MANIFEST.relative_to(ROOT)} is missing: the gates are unpinned. "
            "Run `python3 scripts/verify_gate_integrity.py --update`.",
            file=sys.stderr,
        )
        return 1

    problems = differences(now, before)
    if problems:
        _banner([
            "ALERTE — UN GATE DE CERTIFICATION A ÉTÉ MODIFIÉ",
            "",
            f"{len(problems)} script(s) ne correspondent plus à leur empreinte.",
            "",
            "Les gates décident de ce qui peut être appelé une dérivation",
            "des Principia. Ce dépôt a déjà connu 969 items marqués",
            "« certifiés » qui ne l'étaient pas : la règle ne se modifie",
            "pas en passant.",
            "",
            "Si la modification est délibérée, elle exige l'autorisation",
            "expresse de l'éditeur :",
            "  python3 scripts/verify_gate_integrity.py --update \\",
            "      --authorised-by <nom> --reason <pourquoi>",
        ])
        shown = problems if arguments.report_all else problems[:10]
        for problem in shown:
            print(_colour(f"  {problem}", _RED), file=sys.stderr)
        if len(problems) > len(shown):
            print(
                _colour(f"  ... and {len(problems) - len(shown)} more", _RED),
                file=sys.stderr,
            )
        return 1

    print(f"gate integrity verified ({len(now)} scripts match their pinned digests)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
