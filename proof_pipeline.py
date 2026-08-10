#!/usr/bin/env python3
"""Manage the response -> Aristotle -> Lean CI -> LaTeX publication workflow."""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "pipeline.json"
ARISTOTLE = ROOT / "aristotle"
RESPONSES = ROOT / "responses"
REVIEWS = ROOT / "reviews"
LEAN_SOURCES = ROOT / "lean" / "RMS"
SECTIONS = ROOT / "publication" / "sections"
OUTPUT_TEX = ROOT / "publication" / "main.tex"

# Keep the publication converter reusable as a standalone script while making
# `proof_pipeline.py render` the single command needed by campaign operators.
sys.path.insert(0, str(ROOT / "publication"))
from build_sections import generate_sections  # noqa: E402


def load_manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def save_manifest(data: dict) -> None:
    MANIFEST.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def update_question_fields(qid: str, **fields: str) -> None:
    """Merge one status update into the latest manifest instead of a stale snapshot."""
    lock_path = MANIFEST.with_suffix(".lock")
    with lock_path.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        data = load_manifest()
        question(data, qid).update(fields)
        temporary = MANIFEST.with_suffix(".json.tmp")
        temporary.write_text(
            json.dumps(data, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        temporary.replace(MANIFEST)
        fcntl.flock(lock, fcntl.LOCK_UN)


def question(data: dict, qid: str) -> dict:
    try:
        return data["questions"][qid]
    except KeyError as exc:
        raise SystemExit(f"Unknown question {qid}; add it to pipeline.json first") from exc


def require_file(path: Path) -> str:
    if not path.is_file() or not path.read_text(encoding="utf-8").strip():
        raise SystemExit(f"Required nonempty file is missing: {path.relative_to(ROOT)}")
    return path.read_text(encoding="utf-8")


def lean_executable_text(code: str) -> str:
    """Remove Lean comments and string literals before trust-token checks."""
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(code):
        if block_depth:
            if code.startswith("/-", i):
                block_depth += 1
                i += 2
            elif code.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if code.startswith("/-", i):
            block_depth = 1
            i += 2
            continue
        if code.startswith("--", i):
            end = code.find("\n", i + 2)
            i = len(code) if end < 0 else end
            continue
        if code[i] == '"':
            i += 1
            while i < len(code):
                if code[i] == "\\":
                    i += 2
                elif code[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        out.append(code[i])
        i += 1
    return "".join(out)


def prepare(qid: str) -> None:
    data = load_manifest()
    item = question(data, qid)
    answer = require_file(RESPONSES / f"{qid}.md")
    review = require_file(REVIEWS / f"{qid}-review.md")
    ARISTOTLE.mkdir(exist_ok=True)
    request = f"""# Aristotle formalization request — {qid}

Formalize the mathematical result below in Lean 4 with mathlib.

Canonical problem source: {data['pdf_url']}
Problem identifier: {qid}

Requirements:

- Read the exact statement of {qid} in the canonical PDF.
- Formalize the strongest result that is both claimed in the answer and accepted by the audit.
- Do not formalize a stronger statement merely because it looks plausible.
- Produce one self-contained `.lean` file with all required imports.
- Replace every informal gap with a kernel-checkable proof; do not use `sorry`, `admit`, `axiom`, `unsafe`, or an added unproved hypothesis.
- State any unavoidable mismatch between the printed theorem and the formal theorem.
- Report the exact Lean and mathlib versions used.

## Candidate mathematical answer

{answer}

## Independent audit

{review}
"""
    destination = ARISTOTLE / f"{qid}.md"
    destination.write_text(request, encoding="utf-8")
    item["aristotle_status"] = "request_ready"
    save_manifest(data)
    print(destination.relative_to(ROOT))


def ingest(qid: str, source: Path) -> None:
    data = load_manifest()
    item = question(data, qid)
    code = require_file(source.resolve())
    forbidden = sorted(
        set(re.findall(r"\b(?:sorry|admit|axiom|unsafe)\b", lean_executable_text(code)))
    )
    if forbidden:
        raise SystemExit(f"Refusing Aristotle output containing forbidden tokens: {', '.join(forbidden)}")
    LEAN_SOURCES.mkdir(parents=True, exist_ok=True)
    destination = LEAN_SOURCES / f"{qid}.lean"
    shutil.copyfile(source, destination)
    item["aristotle_status"] = "output_received"
    item["lean_status"] = "awaiting_online_check"
    save_manifest(data)
    print(destination.relative_to(ROOT))


def submit(qid: str) -> None:
    data = load_manifest()
    item = question(data, qid)
    request = ARISTOTLE / f"{qid}.md"
    require_file(request)
    if not os.environ.get("ARISTOTLE_API_KEY"):
        raise SystemExit(
            "ARISTOTLE_API_KEY is missing. Configure it in the shell environment; "
            "never put the key in pipeline.json or pass it on the command line."
        )
    command = [
        "uvx",
        "--from",
        "aristotlelib@latest",
        "aristotle",
        "formalize",
        str(request),
    ]
    update_question_fields(qid, aristotle_status="submitted")
    try:
        completed = subprocess.run(
            command, cwd=ROOT, check=True, text=True, capture_output=True
        )
    except subprocess.CalledProcessError:
        update_question_fields(qid, aristotle_status="submission_failed")
        raise
    if completed.stdout:
        print(completed.stdout, end="")
    if completed.stderr:
        print(completed.stderr, end="", file=sys.stderr)

    combined = completed.stdout + "\n" + completed.stderr
    if re.search(r"(^|\n)\s*ERROR\s*-", combined):
        update_question_fields(qid, aristotle_status="submission_failed")
        raise SystemExit(combined.strip().splitlines()[-1])
    matches = re.findall(
        r"(?:Project created:|Project:)\s*"
        r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})",
        combined,
        flags=re.IGNORECASE,
    )
    if not matches:
        update_question_fields(qid, aristotle_status="submission_failed")
        raise SystemExit("Aristotle returned no project ID; submission not recorded")
    fields = {"aristotle_status": "submitted", "aristotle_project_id": matches[-1]}

    update_question_fields(qid, **fields)
    print(fields.get("aristotle_project_id", "project submitted"))


def record_check(qid: str, source_url: str, check_url: str, passed: bool) -> None:
    data = load_manifest()
    item = question(data, qid)
    require_file(LEAN_SOURCES / f"{qid}.lean")
    item["lean_source_url"] = source_url
    item["typecheck_url"] = check_url
    item["lean_status"] = "verified" if passed else "failed"
    save_manifest(data)


def escape_tex(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def render() -> None:
    data = load_manifest()
    expected = generate_sections(data)
    included = []
    body = []
    for qid in expected:
        item = data["questions"][qid]
        section = SECTIONS / f"{qid}.tex"
        if not section.is_file():
            raise SystemExit(f"Section generator did not create {section.relative_to(ROOT)}")
        if not item["lean_source_url"] or not item["typecheck_url"]:
            raise SystemExit(f"{qid} is verified but its proof/check URLs are missing")
        body.extend(
            [
                rf"\section{{Question {qid}}}",
                rf"\input{{sections/{qid}.tex}}",
                r"\paragraph{Formal verification.}",
                rf"\href{{{item['lean_source_url']}}}{{Lean source}}; "
                rf"\href{{{item['typecheck_url']}}}{{online type-check}}.",
                "",
            ]
        )
        included.append(qid)
        item["publication_status"] = "included"
        item["publication_section"] = f"publication/sections/{qid}.tex"
    for qid, item in data["questions"].items():
        if qid not in included and item.get("publication_status") == "included":
            item["publication_status"] = "missing"
            item.pop("publication_section", None)
    preamble = r"""\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{iftex}
\ifLuaTeX
  \usepackage{fontspec}
  \IfFontExistsTF{Andale Mono}{\setmonofont{Andale Mono}}{%
    \IfFontExistsTF{DejaVu Sans Mono for Powerline}{\setmonofont{DejaVu Sans Mono for Powerline}}{}%
  }
\fi
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage[hidelinks]{hyperref}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\title{Answers to Questions from the RMS}
\author{}
\date{}
\begin{document}
\maketitle
\tableofcontents

"""
    ending = "\\end{document}\n"
    OUTPUT_TEX.parent.mkdir(exist_ok=True)
    OUTPUT_TEX.write_text(preamble + "\n".join(body) + ending, encoding="utf-8")
    save_manifest(data)
    print(f"Rendered {OUTPUT_TEX.relative_to(ROOT)} with {len(included)} verified sections")


def status() -> None:
    data = load_manifest()
    print("ID     review  Aristotle       Lean                   publication")
    for qid, item in data["questions"].items():
        print(
            f"{qid:<7}{item['review_verdict']:<8}"
            f"{item['aristotle_status']:<16}{item['lean_status']:<23}"
            f"{item['publication_status']}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    prepare_parser = commands.add_parser("prepare")
    prepare_parser.add_argument("qid")
    ingest_parser = commands.add_parser("ingest")
    ingest_parser.add_argument("qid")
    ingest_parser.add_argument("source", type=Path)
    submit_parser = commands.add_parser("submit")
    submit_parser.add_argument("qid")
    check_parser = commands.add_parser("record-check")
    check_parser.add_argument("qid")
    check_parser.add_argument("source_url")
    check_parser.add_argument("check_url")
    check_parser.add_argument("--failed", action="store_true")
    commands.add_parser("render")
    commands.add_parser("status")
    args = parser.parse_args()

    if args.command == "prepare":
        prepare(args.qid)
    elif args.command == "ingest":
        ingest(args.qid, args.source)
    elif args.command == "submit":
        submit(args.qid)
    elif args.command == "record-check":
        record_check(args.qid, args.source_url, args.check_url, not args.failed)
    elif args.command == "render":
        render()
    elif args.command == "status":
        status()


if __name__ == "__main__":
    main()
