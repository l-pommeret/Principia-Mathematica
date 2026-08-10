#!/usr/bin/env python3
"""Safe, globally capped Aristotle queue scheduler.

The scheduler is deliberately separate from the editorial pipeline.  It only
updates Aristotle bookkeeping fields in ``pipeline.json`` and never edits Lean,
source, metadata, or site files.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


ACTIVE = {"QUEUED", "IN_PROGRESS"}
FINAL = {
    "COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET", "FAILED", "CANCELED"
}
UUID_RE = re.compile(r"^[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}$", re.I)
STATUSES = "UNKNOWN|QUEUED|IN_PROGRESS|COMPLETE|COMPLETE_WITH_ERRORS|OUT_OF_BUDGET|FAILED|CANCELED"


class SchedulerError(RuntimeError):
    pass


@dataclass(frozen=True)
class Candidate:
    qid: str
    kind: str                 # continuation before new project
    path: Path
    project_id: str | None = None
    manifest_path: str = ""


def parse_tasks(output: str) -> list[dict[str, str]]:
    """Parse every row printed by ``aristotle tasks``, not only the newest."""
    tasks: list[dict[str, str]] = []
    for line in output.splitlines():
        task_id = line[:36]
        status = re.search(rf"({STATUSES})\s*$", line)
        if not UUID_RE.fullmatch(task_id) or not status:
            continue
        middle = line[37:status.start()].rstrip()
        tasks.append({
            "task_id": task_id,
            "created": middle[:20].strip(),
            "name": middle[21:].strip() if len(middle) > 20 else "",
            "status": status.group(1),
        })
    return tasks


def dependency_ids(item: dict) -> list[str]:
    value = item.get("dependencies", item.get("depends_on", []))
    if not isinstance(value, list) or not all(isinstance(v, str) for v in value):
        raise SchedulerError("dependencies must be a list of canonical item IDs")
    return value


def dependencies_checked(question: dict, items: dict) -> bool:
    return all(
        isinstance(items.get(dep), dict) and items[dep].get("status") == "kernel-checked"
        for dep in dependency_ids(question)
    )


def continuation_spec(qid: str, item: dict, root: Path) -> Candidate | None:
    """Accept the explicit singular continuation schema used by the campaign.

    A continuation is pending only with status ``not-submitted``.  Merely
    having an old follow-up path in the manifest never schedules it again.
    """
    path = item.get("aristotle_continuation_path")
    status = item.get("aristotle_continuation_status")
    pid = item.get("aristotle_project_id")
    if status != "not-submitted":
        return None
    if not isinstance(path, str) or not path or not isinstance(pid, str) or not UUID_RE.fullmatch(pid):
        raise SchedulerError(f"{qid}: pending continuation needs a path and valid project ID")
    return Candidate(qid, "continuation", root / path, pid, path)


def candidates(data: dict, root: Path, active_projects: set[str]) -> list[Candidate]:
    result: list[Candidate] = []
    items = data.get("items", {})
    for qid, item in data.get("questions", {}).items():
        if not isinstance(item, dict) or item.get("audit_status") != "A":
            continue
        if not dependencies_checked(item, items):
            continue
        continuation = continuation_spec(qid, item, root)
        if continuation is not None:
            if continuation.project_id not in active_projects:
                result.append(continuation)
            continue
        # A project identity always wins over a stale local status.  This is
        # the central no-duplicate-project invariant.
        pid = item.get("aristotle_project_id")
        if isinstance(pid, str) and UUID_RE.fullmatch(pid):
            continue
        if item.get("aristotle_status") != "not-submitted":
            continue
        prompt = item.get("prompt_path")
        if not isinstance(prompt, str) or not prompt:
            raise SchedulerError(f"{qid}: eligible question has no prompt_path")
        result.append(Candidate(qid, "project", root / prompt, None, prompt))
    return sorted(result, key=lambda c: (c.kind != "continuation", c.qid))


def reconcile(data: dict, list_tasks: Callable[[str], list[dict[str, str]]]) -> tuple[int, set[str]]:
    """Reconcile every known project and count all active remote tasks."""
    active_ids: set[str] = set()
    active_projects: set[str] = set()
    seen_projects: dict[str, str] = {}
    seen_tasks: dict[str, str] = {}
    for qid, item in data.get("questions", {}).items():
        if not isinstance(item, dict):
            continue
        pid = item.get("aristotle_project_id")
        if not isinstance(pid, str) or not UUID_RE.fullmatch(pid):
            continue
        if pid in seen_projects and seen_projects[pid] != qid:
            raise SchedulerError(f"duplicate project ID {pid}: {seen_projects[pid]} and {qid}")
        seen_projects[pid] = qid
        tasks = list_tasks(pid)
        if not tasks:
            item["aristotle_remote_status"] = "NO_TASKS"
            continue
        for task in tasks:
            tid = task["task_id"]
            if tid in seen_tasks and seen_tasks[tid] != qid:
                raise SchedulerError(f"duplicate task ID {tid}: {seen_tasks[tid]} and {qid}")
            seen_tasks[tid] = qid
            if task["status"] in ACTIVE:
                active_ids.add(tid)
                active_projects.add(pid)
        latest = tasks[0]
        item.update({
            "aristotle_latest_task_id": latest["task_id"],
            "aristotle_latest_task_status": latest["status"],
            "aristotle_latest_task_name": latest.get("name", ""),
            "aristotle_latest_task_created": latest.get("created", ""),
            "aristotle_remote_status": latest["status"],
        })
        if latest["status"] in ACTIVE:
            item["aristotle_status"] = "submitted"
            item["aristotle_task_id"] = latest["task_id"]
        elif item.get("aristotle_status") == "submitted" and latest["status"] in FINAL:
            item["aristotle_status"] = "complete" if latest["status"] == "COMPLETE" else "needs-review"
    return len(active_ids), active_projects


def mark_intent(data: dict, candidate: Candidate) -> None:
    item = data["questions"][candidate.qid]
    if candidate.kind == "project":
        item["aristotle_status"] = "submitting"
    else:
        item["aristotle_continuation_status"] = "submitting"


def record_submission(data: dict, candidate: Candidate, result: dict, content: str) -> None:
    item = data["questions"][candidate.qid]
    task = result["task"]
    fields = {
        "aristotle_status": "submitted",
        "aristotle_task_id": task["task_id"],
        "aristotle_latest_task_id": task["task_id"],
        "aristotle_latest_task_status": task["status"],
        "aristotle_remote_status": task["status"],
    }
    if candidate.kind == "project":
        fields.update({
            "aristotle_project_id": result["project_id"],
            "aristotle_request_path": candidate.manifest_path,
            "aristotle_request_sha256": hashlib.sha256(content.encode()).hexdigest(),
        })
    else:
        fields.update({
            "aristotle_continuation_status": "submitted",
            "aristotle_followup_prompt": candidate.manifest_path,
            "aristotle_followup_prompt_sha256": hashlib.sha256(content.encode()).hexdigest(),
        })
    item.update(fields)
