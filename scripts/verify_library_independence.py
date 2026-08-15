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

#: Every Lean module in the reconstruction.  The scope used to be
#: ``Principia/Syntax`` and ``Principia/Deduction`` alone, on the reasoning that
#: those *are* the object calculus.  That reasoning had a hole: 33 161 lines
#: under ``Principia/Architecture`` proved PM's propositions in Lean's own
#: logic — ``∀``, ``↔``, ``Prop``, ``Classical.choice``, ``propext``, ``simpa``,
#: ``or_comm`` — and 26 of them were certified ``pm-derivation-v1``.  ✱22·57 was
#: `by apply class_ext; intro x; exact or_comm`; ✱20·13 was `id`, where PM
#: prints five steps through ✱20·1, ✱12·1, ✱10·321 and ✱13·195.
#:
#: A proof of a PM proposition must be a proof *in PM*.  Lean is the
#: metalanguage that checks it, never the logic that supplies it — so the
#: standard applies to every module, not to the ones we happened to name.
CORE_TREES = ("Principia",)

#: Tactics that discharge a goal by consulting Lean's library.  This tuple is
#: kept as a readable inventory and as a test surface; `_TACTIC` below groups
#: their prefix families so that, for example, adding `_all` to `simp` cannot
#: evade the gate.
#:
#: A blacklist alone is not a safe boundary: every new library tactic would be
#: allowed until somebody remembered to add its name.  `_tactic_heads` therefore
#: implements the inverse policy as well: at a tactic-command position, only the
#: small structural vocabulary in `EXPLICIT_TACTICS` is accepted.  That remains
#: practical for the existing corpus while making an unknown future tactic fail
#: closed.
#:
#: `decide` and its variants are included even when they are axiom-free, because
#: they replace a printed inference by a computation and so destroy the
#: correspondence with the demonstration that criterion T4 exists to record.
#: `grind` is forbidden for exactly the same reason: it can close a goal without
#: leaving any axiom trace, while still erasing the printed inference that T4 is
#: meant to preserve.
LIBRARY_TACTICS = (
    "simp",
    "simp_all",
    "simpa",
    "omega",
    "decide",
    "native_decide",
    "bv_decide",
    "grind",
    "norm_num",
    "norm_num1",
    "norm_cast",
    "aesop",
    "aesop?",
    "exact?",
    "apply?",
    "hint",
    "tauto",
    "linarith",
    "nlinarith",
    "positivity",
    "polyrith",
    "trivial",
)

_TACTIC = re.compile(
    r"(?<![A-Za-z0-9_'.])(?P<tactic>"
    r"simp(?:a|_[A-Za-z0-9_']*)?"
    r"|(?:[A-Za-z][A-Za-z0-9_']*_)?decide"
    r"|norm_[A-Za-z0-9_']+"
    r"|grind|omega|aesop\??|(?:exact|apply)\?|hint"
    r"|tauto|n?linarith|positivity|polyrith|trivial"
    r")(?![A-Za-z0-9_'?])"
)

#: These commands expose their proof structure directly.  Some are term-like
#: tactic forms (`have`, `show`, `let`, `calc`); the rest only introduce,
#: eliminate, rewrite with an explicitly named equality, or arrange cases.
#: Extend this list only after checking that the command cannot search the
#: imported library or replace a printed PM inference by computation.
EXPLICIT_TACTICS = frozenset(
    {
        "apply",
        "by_cases",
        "calc",
        "cases",
        "change",
        "constructor",
        "dsimp",
        "exact",
        "have",
        "induction",
        "intro",
        "intros",
        "let",
        "letI",
        "match",
        "nomatch",
        "obtain",
        "rcases",
        "refine",
        "rfl",
        "rintro",
        "rw",
        "show",
        "split",
        "subst",
        "unfold",
    }
)

_BY = re.compile(r"(?<![A-Za-z0-9_'.])by(?![A-Za-z0-9_'])")
_TACTIC_HEAD = re.compile(r"([A-Za-z_][A-Za-z0-9_']*\??)")
_TACTIC_SEPARATOR = re.compile(r"(?:<;>|;)\s*")

#: `simp` may legitimately appear inside these attribute forms, which only tag a
#: lemma for a simp set someone else might use; they discharge nothing.
_ATTRIBUTE = re.compile(r"@\[[^\]]*\]")

#: ``inductive``, ``structure`` and ``class`` belong here as much as ``theorem``
#: does.  Leaving them out was a blind spot with a name: ``PM.Star9.Star9Derivation``
#: — the ✱9 derivation relation itself, living in the audited tree — depends on
#: ``propext`` and ``Quot.sound``, inherited from the impure normalizer it
#: imports, and the audit reported the tree axiom-free for months because an
#: ``inductive`` never matched this pattern.  A judgement relation is exactly
#: the declaration whose purity matters most: everything derived is built from
#: its constructors.
_DECLARATION = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|def|abbrev|instance|lemma|inductive|structure|class)"
    r"\s+([A-Za-z_][A-Za-z0-9_'.！]*)"
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
                    if text[index] == "\n":
                        out.append("\n")
                    index += 1
            continue
        if text.startswith("--", index):
            newline = text.find("\n", index)
            if newline < 0:
                index = length
            else:
                out.append("\n")
                index = newline + 1
            continue
        out.append(text[index])
        index += 1
    return "".join(out)


def _strip_strings(text: str) -> str:
    """Blank string contents while preserving columns and line numbers."""
    out: list[str] = []
    index = 0
    length = len(text)
    while index < length:
        if text[index] != '"':
            out.append(text[index])
            index += 1
            continue
        out.append(" ")
        index += 1
        while index < length:
            if text[index] == "\\" and index + 1 < length:
                out.extend("  ")
                index += 2
            elif text[index] == '"':
                out.append(" ")
                index += 1
                break
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
    return "".join(out)


def _command_heads(fragment: str) -> list[str]:
    """Return command heads from one tactic line, including sequenced tactics."""
    heads: list[str] = []
    first = _TACTIC_HEAD.match(fragment.lstrip())
    if first:
        heads.append(first.group(1))
    for separator in _TACTIC_SEPARATOR.finditer(fragment):
        following = _TACTIC_HEAD.match(fragment, separator.end())
        if following:
            heads.append(following.group(1))
    # `cases` and `induction` may put all their `with | pattern => tactic`
    # alternatives on one physical line.  A vertical bar inside an `rintro` or
    # `rcases` pattern is not a tactic separator, hence this targeted handling.
    if heads and heads[0] in {"cases", "induction"}:
        for arrow in re.finditer(r"=>\s*", fragment):
            following = _TACTIC_HEAD.match(fragment, arrow.end())
            if following:
                heads.append(following.group(1))
    return heads


def _tactic_heads(text: str) -> list[tuple[int, str]]:
    """Conservatively identify heads at Lean tactic-command positions.

    This is intentionally a small layout scanner, not a Lean parser.  A `by`
    opens a tactic sequence; its first indented line fixes the sequence's layout
    column.  Bullets and `case`/`next` alternatives open nested sequences.  Term
    continuations are more deeply indented and are therefore left alone.
    """
    findings: list[tuple[int, str]] = []
    # Each entry records a layout column, the minimum column for a still-pending
    # layout, and whether the next line is the term assigned by `have ... :=`.
    # The minimum keeps a finished branch from consuming its next sibling.
    layouts: list[dict[str, int | bool | None]] = []
    pending_alternative: int | None = None

    for number, line in enumerate(text.splitlines(), start=1):
        content = line.lstrip(" \t")
        if not content:
            continue
        expanded = line.expandtabs(8)
        indent = len(expanded) - len(expanded.lstrip(" "))

        while layouts:
            column = layouts[-1]["column"]
            minimum = layouts[-1]["minimum"]
            assert isinstance(minimum, int)
            if column is None:
                if indent < minimum:
                    layouts.pop()
                    continue
                layouts[-1]["column"] = indent
                column = indent
            assert isinstance(column, int)
            if indent < column:
                layouts.pop()
                continue
            break

        if pending_alternative is not None:
            if indent <= pending_alternative and not content.startswith("|"):
                pending_alternative = None
            elif "=>" in content:
                command_fragment = content.split("=>", 1)[1].lstrip()
                findings.extend(
                    (number, head) for head in _command_heads(command_fragment)
                )
                layouts.append(
                    {"column": None, "minimum": pending_alternative + 1, "term": False}
                )
                pending_alternative = None
                # A `by` in the branch body is still found below.
                command_fragment = None

        in_command_column = bool(layouts and indent == layouts[-1]["column"])
        command_fragment: str | None = content if in_command_column else None
        if in_command_column and layouts[-1]["term"]:
            layouts[-1]["term"] = False
            command_fragment = None

        if content.startswith("·") and in_command_column:
            command_fragment = content[1:].lstrip()
            layouts.append(
                {
                    "column": indent + 2 if command_fragment else None,
                    "minimum": indent + 1,
                    "term": False,
                }
            )
        elif content.startswith("|") and in_command_column:
            marker_tail = content[1:].lstrip()
            if "=>" in marker_tail:
                command_fragment = marker_tail.split("=>", 1)[1].lstrip()
                layouts.append(
                    {
                        "column": indent + 4 if command_fragment else None,
                        "minimum": indent + 1,
                        "term": False,
                    }
                )
            else:
                command_fragment = None
                pending_alternative = indent
        elif in_command_column and (
            content.startswith("case ") or content.startswith("next ")
        ):
            marker_tail = content.split("=>", 1)[1].lstrip() if "=>" in content else ""
            command_fragment = marker_tail
            layouts.append(
                {
                    "column": indent + 2 if command_fragment else None,
                    "minimum": indent + 1,
                    "term": False,
                }
            )

        if command_fragment:
            heads = _command_heads(command_fragment)
            findings.extend((number, head) for head in heads)
            if (
                heads
                and heads[0] in {"have", "let", "letI"}
                and command_fragment.rstrip().endswith(":=")
                and layouts
            ):
                layouts[-1]["term"] = True

        for by_match in _BY.finditer(line):
            tail = line[by_match.end() :].lstrip()
            if tail:
                findings.extend((number, head) for head in _command_heads(tail))
                # Inline `by exact ...` may continue as a layout sequence on
                # following lines.  A stricter minimum than for a trailing
                # `by` prevents the next top-level declaration being consumed.
                layouts.append(
                    {"column": None, "minimum": indent + 1, "term": False}
                )
            else:
                layouts.append({"column": None, "minimum": 0, "term": False})

    # Preserve source order but do not report a head twice when `by` occurs on
    # a line that is itself already recognized as a command line.
    return list(dict.fromkeys(findings))


def core_files() -> list[Path]:
    files: list[Path] = []
    for tree in CORE_TREES:
        base = ROOT / tree
        if base.is_dir():
            files.extend(sorted(base.rglob("*.lean")))
        # Lake compiles the root module as well as the directory below it.
        # Auditing only `Principia/**/*.lean` left `Principia.lean` able to host
        # kernel-checked declarations that this gate would never inspect.
        root_module = base.with_suffix(".lean")
        if root_module.is_file():
            files.append(root_module)
    return sorted(set(files))


def tactic_findings(paths: list[Path]) -> list[str]:
    """Uses of a library-consulting tactic inside the object calculus."""
    findings: list[str] = []
    for path in paths:
        text = _strip_strings(
            _strip_comments(path.read_text(encoding="utf-8", errors="replace"))
        )
        # Attributes are declarations, not tactic commands.  Keep them in the
        # layout scan (where their leading `@` correctly ends a proof block),
        # but blank them for the forbidden-name scan so `@[simp]` stays legal.
        tactic_names = _ATTRIBUTE.sub(
            lambda match: " " * len(match.group(0)), text
        )
        for number, line in enumerate(tactic_names.splitlines(), start=1):
            match = _TACTIC.search(line)
            if match:
                relative = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
                findings.append(
                    f"{relative}:{number}: `{match.group('tactic')}` consults Lean's "
                    "library; write the step explicitly (rfl, rw with a named "
                    "lemma of this repository, exact, show, congrArg)"
                )
        for number, head in _tactic_heads(text):
            if head in EXPLICIT_TACTICS or _TACTIC.fullmatch(head):
                continue
            relative = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
            findings.append(
                f"{relative}:{number}: `{head}` is not an approved explicit "
                "tactic; unknown tactics fail closed so a new library search "
                "procedure cannot bypass criterion T4"
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
