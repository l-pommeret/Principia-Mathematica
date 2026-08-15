#!/usr/bin/env python3
"""Require every repository gate to be reachable from GitHub Actions CI.

Coverage is a graph property, not a second hand-maintained list.  Workflow
``run:`` commands are roots.  A reachable Python gate can in turn reach gates
listed in its top-level ``GATES`` command registry (the convention used by
``verify_preflight.py``), or gates passed explicitly to a runner call.  The
walk continues until no new gate is found, so aggregators may call aggregators.
"""

from __future__ import annotations

import argparse
import ast
import re
import shlex
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

# A gate intentionally omitted from CI is a policy decision.  Record it here as
# ``"scripts/verify_name.py": "why CI must not run it"``.  Empty reasons,
# unknown paths, and exemptions for gates that CI now reaches are all errors.
CI_GATE_EXEMPTIONS: dict[str, str] = {}

GATE_NAME = re.compile(r"verify_[A-Za-z0-9_]+\.py\Z")
PYTHON_COMMAND = re.compile(r"python(?:[23](?:\.\d+)*)?\Z")
SHELL_CONTROL = frozenset({";", "&&", "||", "|", "&"})
RUNNER_CALLS = frozenset(
    {
        "call",
        "check_call",
        "check_output",
        "Popen",
        "run",
        "run_command",
        "run_gate",
    }
)


def gate_path(value: str) -> str | None:
    """Normalize one exact gate-script token to a repository-relative path."""
    token = value.strip().rstrip(";|&")
    if token.startswith("./"):
        token = token[2:]
    path = Path(token)
    if len(path.parts) == 1 and GATE_NAME.fullmatch(path.name):
        return f"scripts/{path.name}"
    if (
        len(path.parts) == 2
        and path.parts[0] == "scripts"
        and GATE_NAME.fullmatch(path.name)
    ):
        return path.as_posix()
    return None


def workflow_run_commands(path: Path) -> list[str]:
    """Read the inline and block ``run:`` values from one workflow."""
    commands: list[str] = []
    lines = path.read_text(encoding="utf-8").splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        block = re.match(r"(\s*)(?:-\s*)?run:\s*[|>]-?\s*$", line)
        if block:
            indent = len(block.group(1))
            index += 1
            body: list[str] = []
            while index < len(lines):
                following = lines[index]
                following_indent = len(following) - len(following.lstrip())
                if following.strip() and following_indent <= indent:
                    break
                body.append(following.strip())
                index += 1
            commands.append("\n".join(body))
            continue
        inline = re.match(r"\s*(?:-\s*)?run:\s*(\S.*?)\s*$", line)
        if inline:
            command = inline.group(1)
            if len(command) >= 2 and command[0] == command[-1] and command[0] in "\"'":
                command = command[1:-1]
            commands.append(command)
        index += 1
    return commands


def _shell_segments(line: str) -> list[list[str]]:
    """Tokenize a shell line into simple commands, discarding comments."""
    try:
        lexer = shlex.shlex(line, posix=True, punctuation_chars=";&|")
        lexer.whitespace_split = True
        lexer.commenters = "#"
        tokens = list(lexer)
    except ValueError:
        return []
    segments: list[list[str]] = [[]]
    for token in tokens:
        if token in SHELL_CONTROL or set(token) <= set(";&|"):
            if segments[-1]:
                segments.append([])
            continue
        segments[-1].append(token)
    return [segment for segment in segments if segment]


def _segment_gate(segment: list[str]) -> str | None:
    """Return the gate executed by one simple shell command, if any."""
    index = 0
    while index < len(segment) and (
        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*=.*", segment[index])
        or segment[index] in {"command", "env", "exec"}
    ):
        index += 1
    if index >= len(segment):
        return None

    executable = segment[index]
    direct = gate_path(executable)
    if direct is not None:
        return direct
    if not PYTHON_COMMAND.fullmatch(Path(executable).name):
        return None
    for argument in segment[index + 1 :]:
        if argument.startswith("-"):
            continue
        return gate_path(argument)
    return None


def workflow_roots(workflows: Path) -> set[str]:
    roots: set[str] = set()
    for workflow in sorted(workflows.glob("*.yml")):
        for command in workflow_run_commands(workflow):
            for line in command.splitlines():
                for segment in _shell_segments(line):
                    target = _segment_gate(segment)
                    if target is not None:
                        roots.add(target)
    return roots


def _literal_gate_references(node: ast.AST) -> set[str]:
    references: set[str] = set()
    for descendant in ast.walk(node):
        if isinstance(descendant, ast.Constant) and isinstance(descendant.value, str):
            reference = gate_path(descendant.value)
            if reference is not None:
                references.add(reference)
    return references


def python_gate_edges(path: Path) -> set[str]:
    """Return gates invoked by one Python gate under repository conventions."""
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    edges: set[str] = set()

    # Aggregators expose commands in a top-level GATES registry.  Requiring a
    # load as well as an assignment prevents an unused example registry from
    # manufacturing coverage.
    gates_is_loaded = any(
        isinstance(node, ast.Name)
        and node.id == "GATES"
        and isinstance(node.ctx, ast.Load)
        for node in ast.walk(tree)
    )
    if gates_is_loaded:
        for statement in tree.body:
            if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
                continue
            targets = (
                statement.targets
                if isinstance(statement, ast.Assign)
                else [statement.target]
            )
            if any(isinstance(target, ast.Name) and target.id == "GATES" for target in targets):
                if statement.value is not None:
                    edges.update(_literal_gate_references(statement.value))

    # Also recognize explicit commands passed to the usual subprocess/wrapper
    # calls.  Only exact string tokens count, so diagnostics which merely name a
    # verifier cannot turn it into an executed gate.
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        function = node.func.attr if isinstance(node.func, ast.Attribute) else (
            node.func.id if isinstance(node.func, ast.Name) else ""
        )
        if function not in RUNNER_CALLS:
            continue
        for argument in (*node.args, *(keyword.value for keyword in node.keywords)):
            edges.update(_literal_gate_references(argument))
    return edges


def gate_graph(gates: set[str], root: Path) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = {}
    for gate in sorted(gates):
        graph[gate] = python_gate_edges(root / gate) & gates
    return graph


def reachable_gates(roots: set[str], graph: dict[str, set[str]]) -> set[str]:
    reached: set[str] = set()
    pending = list(roots)
    while pending:
        gate = pending.pop()
        if gate in reached or gate not in graph:
            continue
        reached.add(gate)
        pending.extend(graph[gate] - reached)
    return reached


def exemption_problems(gates: set[str], reached: set[str]) -> list[str]:
    problems: list[str] = []
    for gate, reason in sorted(CI_GATE_EXEMPTIONS.items()):
        if gate not in gates:
            problems.append(f"{gate}: CI exemption names no existing gate")
        elif not isinstance(reason, str) or not reason.strip():
            problems.append(f"{gate}: CI exemption requires a written justification")
        elif gate in reached:
            problems.append(f"{gate}: stale CI exemption; the gate is now covered")
    return problems


def verify(root: Path) -> list[str]:
    scripts = root / "scripts"
    workflows = root / ".github" / "workflows"
    gates = {
        path.relative_to(root).as_posix()
        for path in scripts.glob("verify_*.py")
        if path.is_file()
    }
    if not gates:
        return ["scripts/verify_*.py: no gate exists; coverage would be vacuous"]
    roots = workflow_roots(workflows)
    if not roots:
        return [
            ".github/workflows/*.yml: no gate invocation found in a run: command"
        ]
    reached = reachable_gates(roots, gate_graph(gates, root))
    problems = exemption_problems(gates, reached)
    exempted = set(CI_GATE_EXEMPTIONS)
    for gate in sorted(gates - reached - exempted):
        problems.append(
            f"{gate}: not reached by any .github/workflows/*.yml run: command. "
            "Add it directly to a workflow or to GATES in a CI-reachable "
            "aggregator such as scripts/verify_preflight.py. If omission is "
            "deliberate, record the gate and a written justification in "
            "CI_GATE_EXEMPTIONS in scripts/verify_ci_covers_gates.py"
        )
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT,
        help=argparse.SUPPRESS,
    )
    arguments = parser.parse_args()
    root = arguments.root.resolve()
    problems = verify(root)
    if problems:
        print("CI gate coverage failed:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    gate_count = sum(1 for path in (root / "scripts").glob("verify_*.py") if path.is_file())
    print(
        f"CI gate coverage verified ({gate_count}/{gate_count} gates reached; "
        f"{len(CI_GATE_EXEMPTIONS)} justified exemptions)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
