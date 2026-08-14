#!/usr/bin/env python3
"""Reject proof escape hatches in Lean code while ignoring historical prose."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

#: Modifiers and attribute blocks that may precede a declaration keyword.  The
#: original pattern anchored `axiom` to line start plus whitespace, so
#: `@[simp] axiom foo : P` and `private axiom foo : P` were both invisible.
_PREFIX = r"(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"

FORBIDDEN = re.compile(
    # `sorryAx` is listed before `sorry` and without a trailing word boundary:
    # `\bsorry\b` cannot match `sorryAx`, so the original pattern let
    # `theorem t : P := sorryAx _ false` through while `lake env lean` exited 0.
    r"\bsorryAx\b"
    r"|\b(?:sorry|admit)\b"
    r"|(?:^|\n)\s*" + _PREFIX + r"(?:axiom|constant)\b"
    r"|\b(?:unsafe|partial)\s+(?:def|theorem|lemma|abbrev|instance)\b"
    r"|\bnative_decide\b"
    r"|(?:^|\n)\s*" + _PREFIX + r"opaque\b"
    r"|@\[\s*(?:implemented_by|extern)\b"
)


#: Next position that could start a comment or a string literal.  Skipping
#: directly to it keeps this pass linear in the *interesting* characters rather
#: than in every character: the previous per-character loop took over two
#: minutes across the tracked Lean tree, which is too slow for a CI gate.
_INTERESTING = re.compile(r'/-|--|"')


def code_without_comments_or_strings(source: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        if not depth and not in_string:
            nxt = _INTERESTING.search(source, index)
            if nxt is None:
                result.append(source[index:])
                break
            if nxt.start() > index:
                result.append(source[index:nxt.start()])
                index = nxt.start()
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end < 0:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (end - index))
            index = end
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def scanned_paths() -> list[Path]:
    """Every tracked Lean file in the repository.

    The previous walk covered ``Principia/`` only, while
    ``.github/workflows/lean.yml`` kernel-checks ``aristotle/contexts/*.lean``:
    agent-produced Lean that the escape-hatch policy never inspected.  Tracked
    files come from git so an untracked local scratch file cannot fail the gate;
    if git is unavailable the walk falls back to both source trees.
    """
    result = subprocess.run(
        ["git", "ls-files", "*.lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0 and result.stdout.strip():
        paths = [ROOT / line for line in result.stdout.split("\n") if line.strip()]
        return [path for path in paths if path.is_file()]
    return [
        ROOT / "Principia.lean",
        *sorted((ROOT / "Principia").rglob("*.lean")),
        *sorted((ROOT / "aristotle").rglob("*.lean")),
    ]


def context_stub_failure(path: Path, code: str, offset: int) -> str | None:
    """Judge an ``axiom`` found in an isolated prover-context file.

    A context file under ``aristotle/`` stubs already-proved propositions so the
    prover can work on a later one in isolation, and no catalogue item ever
    points at that tree.  The stub is therefore legitimate — but only while it
    states exactly what the real declaration states.  A stub that drifts would
    have the prover derive its target from a premise the edition does not hold,
    and `lake env lean` would still report the context green.  Returns ``None``
    when the stub is faithful, or the reason it is not.
    """
    if "aristotle/" not in path.as_posix():
        return "axiom outside the prover-context tree"
    # `offset` is the start of the whole FORBIDDEN match, which for the axiom
    # alternative begins at the preceding newline.  Anchor on the keyword itself.
    keyword = code.find("axiom", offset)
    if keyword < 0:
        keyword = code.find("constant", offset)
    if keyword < 0:
        return "axiom without a parsable name"
    line_start = code.rfind("\n", 0, keyword) + 1
    match = re.match(
        r"\s*(?:axiom|constant)\s+([A-Za-z_][A-Za-z0-9_'!]*)", code[line_start:]
    )
    if not match:
        return "axiom without a parsable name"
    name = match.group(1)

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pm_lean_index import declarations, import_closure, normalise_formula

    # Take the stub from just after its own name to the blank line that ends
    # it, so the comparison is binders-and-type against binders-and-type.
    stub_start = line_start + match.end()
    stub_end = code.find("\n\n", stub_start)
    stub_statement = code[stub_start: stub_end if stub_end > 0 else len(code)]

    # One printed number can be declared in more than one calculus.  ✱2·03 is
    # proved both in the legacy propositional development (`PM.Elementary`,
    # `⊢ₚ`) and in the ramified one that carries quantifiers (`Formula`, `⊢ᵣ`),
    # and PM's numbering is what names them both — the brief requires exactly
    # that.  A stub is therefore faithful when it states what *one* of those
    # declarations states; stopping at the first module found would report a
    # faithful stub as drifted purely because of alphabetical order.
    candidates: list[tuple[str, object]] = []
    for module in sorted(import_closure()):
        real = declarations(module).get(name)
        if real is None:
            continue
        if normalise_formula(stub_statement) == normalise_formula(real.statement):
            return None
        candidates.append((module, real))

    if candidates:
        module, real = candidates[0]
        where = (
            module
            if len(candidates) == 1
            else f"any of the {len(candidates)} declarations of `{name}`"
        )
        return (
            f"context stub `{name}` does not state what {where} states\n"
            f"      stub: {normalise_formula(stub_statement)[:160]}\n"
            f"      real: {normalise_formula(real.statement)[:160]}"
        )
    return (
        f"context stub `{name}` has no counterpart in the import closure; it "
        "assumes something the edition never proves"
    )


def main() -> None:
    failed = False
    paths = scanned_paths()
    if not paths:
        print("no Lean files were scanned; the policy gate did not run", file=sys.stderr)
        raise SystemExit(1)
    stubs = 0
    for path in paths:
        code = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
        for match in FORBIDDEN.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            token = match.group(0).strip()
            if token in {"axiom", "constant"}:
                reason = context_stub_failure(path, code, match.start())
                if reason is None:
                    stubs += 1
                    continue
                print(f"{path}:{line}: {reason}", file=sys.stderr)
                failed = True
                continue
            print(
                f"forbidden Lean declaration '{token}' at {path}:{line}",
                file=sys.stderr,
            )
            failed = True
    if failed:
        raise SystemExit(1)
    print(
        f"Lean source policy checks passed ({len(paths)} files, "
        f"{stubs} verified prover-context stubs)"
    )


if __name__ == "__main__":
    main()
