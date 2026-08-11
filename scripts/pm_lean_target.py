#!/usr/bin/env python3
"""Render audited elementary PM assertion ASTs as Lean theorem targets."""

from __future__ import annotations

import re

from pm_syntax import AST, parse_statement


class LeanTargetError(ValueError):
    pass


ELEMENTARY_TAGS = {"atom", "not", "or", "and", "implies"}


def statement_paragraph(source: str) -> str:
    """Return the numbered statement paragraph preceding a demonstration."""
    prefix = source.split("\nDem.", 1)[0].strip()
    if not prefix.startswith("✱"):
        raise LeanTargetError("demonstration lacks a numbered statement paragraph")
    return " ".join(prefix.split())


def atoms(node: AST) -> list[str]:
    found: set[str] = set()

    def visit(current: AST) -> None:
        if current.tag == "atom":
            if current.value is None or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", current.value):
                raise LeanTargetError(f"unsupported elementary atom {current.value!r}")
            found.add(current.value)
            return
        if current.tag not in ELEMENTARY_TAGS | {"assert"}:
            raise LeanTargetError(f"non-elementary AST node {current.tag}")
        for child in current.children:
            visit(child)

    visit(node)
    return sorted(found)


def render_formula(node: AST) -> str:
    if node.tag == "atom":
        if node.value is None:
            raise LeanTargetError("atom without value")
        return node.value
    if node.tag == "not":
        return f"(∼ₚ {render_formula(node.children[0])})"
    binary = {"or": "∨ₚ", "and": "∧ₚ", "implies": "⊃ₚ"}
    if node.tag in binary:
        left, right = node.children
        return f"({render_formula(left)} {binary[node.tag]} {render_formula(right)})"
    raise LeanTargetError(f"cannot render AST node {node.tag}")


def render_elementary_assertion(source: str, declaration: str) -> str:
    parsed = parse_statement(statement_paragraph(source))
    if parsed.tag != "assert" or len(parsed.children) != 1:
        raise LeanTargetError("elementary theorem target must be an asserted formula")
    namespace, name = declaration.rsplit(".", 1)
    variables = atoms(parsed)
    binder = " ".join(variables)
    parameters = f"({binder} : PM.Elementary Γ)" if binder else ""
    proposition = render_formula(parsed.children[0])
    return (
        f"namespace {namespace}\n\n"
        f"theorem {name} {{Γ}} {parameters} :\n"
        f"    ⊢ₚ {proposition} := by\n"
        f"  -- fill exactly from the generated whitelist\n\n"
        f"end {namespace}"
    )

