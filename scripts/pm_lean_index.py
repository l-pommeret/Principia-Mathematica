#!/usr/bin/env python3
"""Shared read-only index of the Lean tree: import closure and declarations."""

from __future__ import annotations

import re
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive",
    "example", "class", "opaque", "axiom",
)
_DECL_START = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(" + "|".join(DECL_KEYWORDS) + r")\s+([^\s({\[:]+)"
)
# Anything that can end a declaration's region.  ``end`` and ``namespace`` are
# included so a trailing declaration does not absorb the rest of the file.
_REGION_END = re.compile(
    r"(?m)^\s*(?:@\[|/--|/-!|/- |"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:" + "|".join(DECL_KEYWORDS) + r")\s|namespace\s|end\s|end$|section\s|"
    r"variable\s|open\s|import\s|notation|infix|prefix|postfix|macro|syntax)"
)


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


@lru_cache(maxsize=None)
def source(relative_path: str) -> str:
    """Return the text of a repository-relative Lean file, or '' if absent."""
    path = ROOT / relative_path
    return _read(path) if path.is_file() else ""


def _leading_imports(relative_path: str) -> list[str]:
    """Module names imported by a Lean file, read from its header only."""
    modules: list[str] = []
    for line in source(relative_path).splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            modules.append(stripped.split()[1])
        elif stripped and not stripped.startswith(("--", "/-")):
            break
    return modules


@lru_cache(maxsize=1)
def import_closure() -> frozenset[str]:
    """Repository-relative paths transitively imported by ``Principia.lean``.

    This is exactly the set of modules ``lake build`` kernel-checks, because
    ``lakefile.toml`` declares a single library whose only root is
    ``Principia.lean``.  A declaration outside this set is compiled by nothing.
    """
    reached: set[str] = set()
    pending = ["Principia.lean"]
    while pending:
        current = pending.pop()
        if current in reached:
            continue
        reached.add(current)
        for module in _leading_imports(current):
            candidate = module.replace(".", "/") + ".lean"
            if (ROOT / candidate).is_file() and candidate not in reached:
                pending.append(candidate)
    return frozenset(reached)


@lru_cache(maxsize=1)
def _library_globs() -> tuple[str, ...]:
    """``globs`` declared for the ``Principia`` library in ``lakefile.toml``."""
    lakefile = ROOT / "lakefile.toml"
    if not lakefile.is_file():
        return ()
    match = re.search(
        r"(?m)^\s*globs\s*=\s*\[([^\]]*)\]", _read(lakefile)
    )
    if not match:
        return ()
    return tuple(re.findall(r'"([^"]+)"', match.group(1)))


@lru_cache(maxsize=1)
def compiled_modules() -> frozenset[str]:
    """Repository-relative paths that ``lake build`` actually kernel-checks.

    With no ``globs`` in ``lakefile.toml`` the only library root is
    ``Principia.lean``, so the compiled set is its import closure.  A glob of the
    form ``Principia.+`` makes every module under ``Principia/`` a build target,
    which is strictly larger: a module nobody imports is still compiled.
    Criterion T1 asks whether the kernel sees a declaration at all, so it must
    read the build configuration rather than assume the aggregate root.
    """
    globs = _library_globs()
    if any(glob.endswith(".+") or glob.endswith(".*") for glob in globs):
        return frozenset(all_lean_files())
    return import_closure()


def all_lean_files() -> list[str]:
    """Every ``*.lean`` file under ``Principia/`` plus the aggregate root."""
    paths = ["Principia.lean"] if (ROOT / "Principia.lean").is_file() else []
    paths.extend(
        str(path.relative_to(ROOT))
        for path in sorted((ROOT / "Principia").rglob("*.lean"))
    )
    return paths


class Declaration:
    """A single Lean declaration located textually inside a file."""

    __slots__ = ("name", "kind", "path", "line", "statement", "body")

    def __init__(
        self, name: str, kind: str, path: str, line: int, statement: str, body: str
    ) -> None:
        self.name = name
        self.kind = kind
        self.path = path
        self.line = line
        self.statement = statement
        self.body = body

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Declaration({self.path}:{self.line} {self.kind} {self.name})"


def _split_statement_and_body(region: str) -> tuple[str, str]:
    """Split a declaration region at its top-level ``:=`` or ``where``.

    Depth counting ignores ``:=`` inside parentheses, brackets, braces and
    string literals, so a default argument or an anonymous constructor does not
    truncate the statement.
    """
    depth = 0
    index = 0
    in_string = False
    escaped = False
    length = len(region)
    while index < length:
        char = region[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif depth == 0:
            if region.startswith(":=", index):
                return region[:index], region[index + 2:]
            if region.startswith("where", index) and (
                index == 0 or not region[index - 1].isalnum()
            ) and not region[index + 5: index + 6].isalnum():
                return region[:index], region[index + 5:]
        index += 1
    return region, ""


@lru_cache(maxsize=None)
def declarations(relative_path: str) -> dict[str, Declaration]:
    """Index a Lean file by declaration name.

    Later definitions of the same short name overwrite earlier ones; Lean files
    in this repository do not reuse a name inside one module, and a collision is
    surfaced by the tier gate as an ambiguity rather than silently resolved.
    """
    text = source(relative_path)
    if not text:
        return {}
    found: dict[str, Declaration] = {}
    matches = list(_DECL_START.finditer(text))
    for position, match in enumerate(matches):
        start = match.end()
        limit = matches[position + 1].start() if position + 1 < len(matches) else len(text)
        tail = _REGION_END.search(text, start, limit)
        region_end = tail.start() if tail else limit
        statement, body = _split_statement_and_body(text[start:region_end])
        found[match.group(2)] = Declaration(
            name=match.group(2),
            kind=match.group(1),
            path=relative_path,
            line=text.count("\n", 0, match.start()) + 1,
            statement=statement,
            body=body,
        )
    return found


#: Field types that would make a "reading" meaningless: they are Lean's own
#: truth values, not PM object syntax.  A reading whose ``parsed`` field is a
#: ``Prop`` re-admits the semantic-translation layer under a certified name.
_NON_SYNTAX_PARSED = re.compile(r"^\s*(Prop|Bool|Type(\s|\*|$)|Sort|Set\b|.*→\s*Prop\s*$)")

_STRUCTURE = re.compile(r"(?m)^\s*structure\s+([A-Za-z_][A-Za-z0-9_'.]*)")


@lru_cache(maxsize=1)
def reading_types() -> frozenset[str]:
    """Structures usable as a printed↔AST reading, derived from the tree.

    A reading type is any structure carrying ``printed``, ``parsed`` and
    ``scopeReading`` fields whose ``parsed`` field is typed by PM object syntax.
    Deriving the set instead of hard-coding it lets new fragments introduce their
    own concrete reading type, while the ``parsed`` condition keeps a parametric
    or ``Prop``-valued wrapper out: the gate's subject cannot be chosen by the
    code it audits.
    """
    accepted: set[str] = set()
    for relative in all_lean_files():
        text = source(relative)
        for match in _STRUCTURE.finditer(text):
            # Bound the window to this structure's own body, otherwise a
            # neighbouring reading type's fields leak in and every adjacent
            # structure is misread as a reading.
            following = _REGION_END.search(text, match.end())
            tail = text[match.end(): following.start() if following else len(text)]
            if not re.search(r"(?m)^\s*printed\s*:", tail):
                continue
            if not re.search(r"(?m)^\s*scopeReading\s*:", tail):
                continue
            parsed = re.search(r"(?m)^\s*parsed\s*:\s*(.+)$", tail)
            if parsed and not _NON_SYNTAX_PARSED.match(parsed.group(1)):
                accepted.add(match.group(1).rsplit(".", 1)[-1])
    return frozenset(accepted)


_INDUCTIVE = re.compile(
    r"(?m)^\s*inductive\s+([A-Za-z_][A-Za-z0-9_'.]*)([^\n]*(?:\n(?!\s*(?:inductive|structure|def|theorem|lemma|abbrev|end|namespace)\b)[^\n]*)*?)\bwhere\b"
)


@lru_cache(maxsize=1)
def judgement_relations() -> frozenset[str]:
    """Inductive ``Prop``-valued relations: the only admissible judgements.

    PM's calculus is a derivation relation whose constructors are the printed
    primitive propositions.  A ``structure`` with fields is not one: its fields
    are assumptions the caller supplies, so it can be inhabited without any
    derivation having taken place.  Criterion T3 admits only these names.
    """
    relations: set[str] = set()
    evidence: set[str] = set()
    for relative in all_lean_files():
        text = source(relative)
        for match in _INDUCTIVE.finditer(text):
            signature = match.group(2)
            if re.search(r":\s*Prop\b|→\s*Prop\b|\bProp\s*$", signature):
                relations.add(match.group(1).rsplit(".", 1)[-1])
        # A judgement may also be written as an explicit proof tree in `Type`
        # with the assertion defined as its inhabitation:
        #
        #   inductive DerivationEvidence : … → Type where …
        #   def Derivation (p) : Prop := Nonempty (DerivationEvidence p)
        #
        # That is a faithful reading of PM's `⊢` — "a finite proof tree exists" —
        # and the constructors are still the printed primitives, so the evidence
        # type must be audited exactly like a `Prop`-valued relation.  Without
        # this, moving a calculus to `Type` would silently exempt it from T10.
        # The binders may themselves contain `:` and the body may sit on the next
        # line, so the span between the name and `: Prop :=` must be permissive.
        # A stricter pattern silently missed `PM.Derivation` itself, leaving the
        # reference calculus of ✱1 unaudited by T10 — the one relation that must
        # never escape it.
        for match in re.finditer(
            r"(?m)^\s*(?:@\[[^\]]*\]\s*)?def\s+([A-Za-z_][A-Za-z0-9_'.]*)"
            r"[^\n]*?:\s*Prop\s*:=\s*\n?\s*"
            r"Nonempty\s*\(?\s*([A-Za-z_][A-Za-z0-9_'.]*)",
            text,
        ):
            relations.add(match.group(1).rsplit(".", 1)[-1])
            evidence.add(match.group(2).rsplit(".", 1)[-1])
    return frozenset(relations | evidence)


def normalise_formula(text: str) -> str:
    """Whitespace-insensitive, redundant-parenthesis-insensitive normal form.

    Used to compare a printed reading's ``parsed`` field with the formula a
    theorem actually asserts.  Only *matched outermost* parentheses are peeled,
    so ``(a) ⊃ₚ (b)`` is not conflated with ``a ⊃ₚ b`` unless the parentheses
    genuinely wrap the whole expression.
    """
    collapsed = "".join(text.split())
    while collapsed.startswith("(") and collapsed.endswith(")"):
        depth = 0
        wraps = True
        for position, char in enumerate(collapsed):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and position != len(collapsed) - 1:
                    wraps = False
                    break
        if not wraps:
            break
        collapsed = collapsed[1:-1]
    return collapsed


def normalise_printed(text: str) -> str:
    """Collapse whitespace runs in a diplomatic printed reading."""
    return " ".join(text.split())


_LEAN_STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')


def lean_string_after(region: str, marker: str) -> str | None:
    """Return the first Lean string literal following ``marker`` in ``region``."""
    position = region.find(marker)
    if position < 0:
        return None
    match = _LEAN_STRING.search(region, position)
    if not match:
        return None
    return (
        match.group(1)
        .replace('\\"', '"')
        .replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\\\", "\\")
    )
