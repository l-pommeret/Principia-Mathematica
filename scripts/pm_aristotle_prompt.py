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


def render_batch_prompt(manifest: dict, *, printed_targets: dict[str, str],
                        lean_targets: dict[str, str], context: str) -> str:
    if manifest.get("kind") != "pm-constrained-prover-batch-manifest":
        raise PromptError("not a PM constrained-prover batch manifest")
    if manifest.get("context_closure") and not context.strip():
        raise PromptError("a reviewed isolated Lean context is required for this closure")
    sections = []
    for index, item_manifest in enumerate(manifest["batch_items"], start=1):
        identifier = item_manifest["current_item"]
        if identifier not in printed_targets or identifier not in lean_targets:
            raise PromptError(f"missing printed or Lean target for {identifier}")
        diagnostics = item_manifest.get("diagnostics", {})
        if any(diagnostics.get(key) for key in (
            "missing_items", "non_kernel_checked_items", "unresolved_aliases"
        )):
            raise PromptError(f"unresolved strict-mode diagnostics for {identifier}")
        whitelist = "\n".join(
            f"- `{pm_id}` → `{declaration}`"
            for pm_id, declaration in item_manifest["allowed_lean_declarations"].items()
        ) or "- none"
        substitutions = "\n".join(
            f"- step {entry['step']}: `{entry['printed']}`"
            for entry in item_manifest.get("substitutions", [])
        ) or "- none"
        corrections = "\n".join(
            f"- printed `{permission['printed']}` → licensed "
            f"`{', '.join(permission['candidates'])}`: {permission['editorial_reason']}"
            for permission in item_manifest.get("proof_permissions", [])
            if permission.get("resolution_status") == "reviewed-source-correction"
        )
        correction_section = (f"""

Reviewed source-critical normalizations (the diplomatic text above is not
silently altered):

{corrections}
""" if corrections else "")
        local = ", ".join(item_manifest.get("local_proof_items", [])) or "none"
        sections.append(f"""### {index}. {identifier}

Printed target:

```text
{printed_targets[identifier].rstrip()}
```

Required Lean declaration:

```lean
{lean_targets[identifier].rstrip()}
```

Exact whitelist for this declaration:

{whitelist}

Earlier local targets licensed here: {local}.

Printed substitutions:

{substitutions}{correction_section}
""")
    clean_context = "\n".join(line.rstrip() for line in context.rstrip().splitlines())
    return f"""# Strict ordered PM reconstruction batch

Produce the following declarations in exactly this order. A target may use an
earlier target only where that earlier PM number occurs in its own whitelist.
No later/forward target is available. Each proof is audited independently.

{chr(10).join(sections)}

## Reviewed isolated Lean context

The declarations below are compilation scaffolding. They grant no proof
permission unless separately listed in the target's whitelist.

```lean
{clean_context}
```

## Output contract

Return only the requested Lean declarations, in order. Do not add an axiom,
instance, notation, alternate syntax, `Classical`, `unsafe`, `sorry`, `admit`,
semantic truth-table shortcut, or any theorem outside each target's whitelist.
The repository will extract dependencies from every returned theorem separately.
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
