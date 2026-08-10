#!/usr/bin/env python3
"""Render a compact Aristotle request from an audited PM constraint manifest."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


class PromptError(ValueError):
    pass


def render_prompt(
    manifest: dict,
    *,
    printed_target: str,
    lean_target: str,
    context: str = "",
) -> str:
    if manifest.get("kind") != "pm-constrained-prover-manifest":
        raise PromptError("not a PM constrained-prover manifest")
    diagnostics = manifest.get("diagnostics", {})
    if any(diagnostics.get(key) for key in (
        "missing_items", "non_kernel_checked_items", "unresolved_aliases"
    )):
        raise PromptError("manifest has unresolved strict-mode diagnostics")
    closure = manifest.get("context_closure", [])
    if closure and not context.strip():
        raise PromptError("a reviewed isolated Lean context is required for this closure")

    allowed = manifest["allowed_lean_declarations"]
    allowed_lines = [
        f"- `{pm_id}` → `{allowed[pm_id]}`"
        for pm_id in sorted(allowed)
    ] or ["- none (definition/primitive target)"]
    substitutions = manifest.get("substitutions", [])
    substitution_lines = [
        f"- step {entry['step']}: `{entry['printed']}`"
        for entry in substitutions
    ] or ["- none"]
    item = manifest.get("current_item") or "unidentified PM item"
    context_section = (
        "\n## Reviewed isolated Lean context\n\n"
        "The declarations below are compilation scaffolding. They are not proof\n"
        "permissions unless separately listed in the whitelist.\n\n"
        f"```lean\n{context.rstrip()}\n```\n"
        if context.strip() else ""
    )
    return f"""# Strict PM reconstruction — {item}

## Printed target

```text
{printed_target.rstrip()}
```

## Required Lean declaration

```lean
{lean_target.rstrip()}
```

## Exact historical proof whitelist

{chr(10).join(allowed_lines)}

No other PM theorem may occur in the returned proof term. The compilation
context below grants no additional proof permission. Do not replace a printed
substitution by a stronger theorem.

Printed substitutions:

{chr(10).join(substitution_lines)}
{context_section}
## Output contract

Return only the requested Lean declaration. Do not add an axiom, instance,
notation, alternate syntax, `Classical`, `unsafe`, `sorry`, `admit`, semantic
truth-table shortcut, or a theorem outside the whitelist. The repository will
extract dependencies from the returned term and reject any unlicensed item.
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--printed-target", type=Path, required=True)
    parser.add_argument("--lean-target", type=Path, required=True)
    parser.add_argument("--context", type=Path)
    parser.add_argument("--output", type=Path)
    options = parser.parse_args()
    manifest = json.loads(options.manifest.read_text(encoding="utf-8"))
    rendered = render_prompt(
        manifest,
        printed_target=options.printed_target.read_text(encoding="utf-8"),
        lean_target=options.lean_target.read_text(encoding="utf-8"),
        context=(options.context.read_text(encoding="utf-8") if options.context else ""),
    )
    if options.output:
        options.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
