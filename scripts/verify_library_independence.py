#!/usr/bin/env python3
"""The object calculus must stand on PM's primitives, not on Lean's library.

``scripts/verify_axiom_audit.py`` asks the kernel what each *catalogued*
declaration assumes.  That leaves a gap, and the gap has already been used: an
infrastructure lemma nothing catalogues yet can carry an axiom silently, and
every proposition later built on it inherits the assumption.

That is exactly how ``propext`` entered this repository.  ``Nat.max_self``
(``max n n = n``) is proved in Lean's standard library through the simplifier,
so it depends on ``propext``.  ``implication`` and ``sameDisjunction`` rejoin
their ramified orders with ``Eq.mp (congrArg _ (Nat.max_self order))``, so every
formula carrying a connective inherited the axiom, and with it every derivation
from ✱9 to ✱21 — while the audit stayed green, because the carrier was a
definition rather than a catalogued theorem.

This gate closes that gap from both sides.  It asks the kernel about *every*
declaration of the object calculus, catalogued or not; and it forbids, in those
modules, the tactics that pull library lemmas in without saying so.

Lean remains the metalanguage that checks the work — ``rfl``, structural
recursion, ``congrArg``, ``Eq.mp`` and type checking are the paper and the
reader's attention.  What PM calls the process of inference stays inside
``Derivation`` and its eighteen printed primitive propositions.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

#: The modules that *are* the reconstructed object calculus.  A dependency on
#: the library here contaminates every proposition built above it, so these are
#: held to the strictest standard in the repository.
CORE_TREES = ("Principia/Syntax", "Principia/Deduction")

#: Tactics that discharge a goal by consulting Lean's library.  Each can quietly
#: introduce `propext` (rewriting under an equality of propositions) or
#: `Classical.choice`, and none of them is needed to reproduce a printed PM
#: demonstration: PM's steps are explicit, so ours can be too.
#:
#: `decide` is included even though it is often axiom-free, because it replaces
#: a printed inference by a computation and so destroys the correspondence with
#: the demonstration that criterion T4 exists to record.
LIBRARY_TACTICS = (
    "simp",
    "simpa",
    "omega",
    "decide",
    "norm_num",
    "aesop",
    "tauto",
    "linarith",
    "nlinarith",
    "positivity",
    "polyrith",
    "trivial",
)

_TACTIC = re.compile(
    r"(?<![A-Za-z0-9_'.])(" + "|".join(LIBRARY_TACTICS) + r")(?![A-Za-z0-9_'])"
)

#: `simp` may legitimately appear inside these attribute forms, which only tag a
#: lemma for a simp set someone else might use; they discharge nothing.
_ATTRIBUTE = re.compile(r"@\[[^\]]*\]")

_DECLARATION = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|def|abbrev|instance|lemma)\s+([A-Za-z_][A-Za-z0-9_'.！]*)"
)
_NAMESPACE = re.compile(r"(?m)^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
_END = re.compile(r"(?m)^\s*end\s+([A-Za-z_][A-Za-z0-9_'.]*)")

_NO_AXIOMS = re.compile(r"^'([^']+)' does not depend on any axioms")
_DEPENDS = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]")


class ToolchainError(RuntimeError):
    """Raised when the audit could not be performed at all."""


def _strip_comments(text: str) -> str:
    """Remove Lean comments so a tactic named in prose is not a finding."""
    out: list[str] = []
    index = 0
    length = len(text)
    while index < length:
        if text.startswith("/-", index):
            depth = 1
            index += 2
            while index < length and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            continue
        if text.startswith("--", index):
            newline = text.find("\n", index)
            index = length if newline < 0 else newline
            continue
        out.append(text[index])
        index += 1
    return "".join(out)


def core_files() -> list[Path]:
    files: list[Path] = []
    for tree in CORE_TREES:
        base = ROOT / tree
        if base.is_dir():
            files.extend(sorted(base.rglob("*.lean")))
    return files


def tactic_findings(paths: list[Path]) -> list[str]:
    """Uses of a library-consulting tactic inside the object calculus."""
    findings: list[str] = []
    for path in paths:
        text = _strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        text = _ATTRIBUTE.sub(" ", text)
        for number, line in enumerate(text.splitlines(), start=1):
            match = _TACTIC.search(line)
            if match:
                relative = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
                findings.append(
                    f"{relative}:{number}: `{match.group(1)}` consults Lean's "
                    "library; write the step explicitly (rfl, rw with a named "
                    "lemma of this repository, exact, show, congrArg)"
                )
    return findings


def declared_names(paths: list[Path]) -> list[str]:
    """Fully qualified names declared in the object calculus."""
    names: list[str] = []
    for path in paths:
        text = _strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        scope: list[str] = []
        for line in text.splitlines():
            opening = _NAMESPACE.match(line)
            if opening:
                scope.append(opening.group(1))
                continue
            closing = _END.match(line)
            if closing:
                if scope and scope[-1].endswith(closing.group(1).split(".")[-1]):
                    scope.pop()
                continue
            declaration = _DECLARATION.match(line)
            if declaration:
                name = declaration.group(2)
                prefix = ".".join(scope)
                names.append(f"{prefix}.{name}" if prefix else name)
    return names


def axiom_findings(names: list[str]) -> list[str]:
    """Declarations of the object calculus that depend on any axiom."""
    if not names:
        raise ToolchainError("no declaration found in the object calculus")

    unique = sorted(set(names))
    body = "\n".join(f"#print axioms {name}" for name in unique)
    program = f"import Principia\n\nset_option maxHeartbeats 1000000\n\n{body}\n"

    with tempfile.TemporaryDirectory(prefix="pm-library-independence-") as directory:
        probe = Path(directory) / "LibraryIndependence.lean"
        probe.write_text(program, encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    output = result.stdout + "\n" + result.stderr
    if "does not depend on any axioms" not in output and "depends on axioms" not in output:
        raise ToolchainError(
            "`#print axioms` produced no parsable output; run `lake build` first.\n"
            + output.strip()[:2000]
        )

    findings: list[str] = []
    for line in output.splitlines():
        depends = _DEPENDS.match(line.strip())
        if depends:
            name, axioms = depends.group(1), depends.group(2).strip()
            findings.append(
                f"{name} depends on [{axioms}]: the object calculus must rest on "
                "PM's primitives alone.\n" + REMEDY
            )
    return findings


#: What to do about it.  The first instinct is to hunt for a borrowed lemma, and
#: that is often wrong: the commonest carrier in this repository was Lean's own
#: structural recursion compiler.  A definition written with `match`, or with
#: pattern-matching equations, elaborates through `Nat.brecOn`,
#: `<Type>.brecOn` and generated `…match_1` auxiliaries, every one of which
#: depends on `propext` — so an author who never mentions the library still
#: acquires it.  Saying so here saves the next reader the search that cost this
#: edition an afternoon.
REMEDY = (
    "      Look first at how the definition recurses: `match` and\n"
    "      pattern-matching equations elaborate through `brecOn` and generated\n"
    "      `…match_N` auxiliaries, which depend on `propext`. Rewrite with the\n"
    "      primitive recursors — `Nat.rec`, `<Type>.casesOn`, explicit\n"
    "      structural recursion — as `smartDisj`, `Formation.ofElementary` and\n"
    "      `erase_embedElementary` were. If instead a library theorem is at\n"
    "      fault (`Nat.max_self` was, proved upstream by the simplifier), prove\n"
    "      the fact here under its own name, as `natMaxSelf` does."
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-all", action="store_true")
    parser.add_argument(
        "--tactics-only",
        action="store_true",
        help="skip the kernel audit (useful when the build is red)",
    )
    arguments = parser.parse_args()

    paths = core_files()
    if not paths:
        print(
            f"no Lean source under {', '.join(CORE_TREES)}; nothing was audited",
            file=sys.stderr,
        )
        return 1

    findings = tactic_findings(paths)
    audited = 0
    if not arguments.tactics_only:
        names = declared_names(paths)
        audited = len(set(names))
        try:
            findings.extend(axiom_findings(names))
        except ToolchainError as error:
            print(f"library-independence audit could not run: {error}", file=sys.stderr)
            return 1

    if findings:
        shown = findings if arguments.report_all else findings[:10]
        for finding in shown:
            print(f"  {finding}", file=sys.stderr)
        if len(findings) > len(shown):
            print(f"  ... and {len(findings) - len(shown)} more", file=sys.stderr)
        print(
            f"\n{len(findings)} dependencies on Lean's library in the object "
            f"calculus ({len(paths)} modules, {audited} declarations audited). "
            "PM's system must stand on its own primitives.",
            file=sys.stderr,
        )
        return 1

    print(
        f"library independence verified ({len(paths)} modules, {audited} "
        "declarations, no library tactic and no axiom)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
