#!/usr/bin/env python3
"""Short, safe commands for the recurring proof-campaign operations."""

from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from urllib.parse import urlsplit

import browser_sync
import aristotle_scheduler as scheduler


ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "pipeline.json"
ACTIVE_TASKS = {"QUEUED", "IN_PROGRESS"}
MAX_BROWSER_TABS = 5
MAX_NEW_QID = 900
ARISTOTLE = ["uvx", "--from", "aristotlelib@latest", "aristotle"]
ARISTOTLE_KEYCHAIN_SERVICE = os.environ.get(
    "ARISTOTLE_KEYCHAIN_SERVICE", "principia-mathematica-aristotle"
)
ARISTOTLE_KEYCHAIN_ACCOUNT = os.environ.get("ARISTOTLE_KEYCHAIN_ACCOUNT", "Aristotle")
UUID_RE = re.compile(r"^[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}$", re.I)
QID_RE = re.compile(r"\bQ\d+\b", re.I)


class CampaignError(RuntimeError):
    pass


def emit(payload: object, *, stream=sys.stdout) -> None:
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True), file=stream)


def redact(text: str) -> str:
    key = os.environ.get("ARISTOTLE_API_KEY", "")
    return text.replace(key, "<redacted>") if key else text


def run(command: list[str], *, cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if completed.returncode:
        detail = redact((completed.stderr or completed.stdout).strip())
        raise CampaignError(detail.splitlines()[-1] if detail else f"command failed: {command[0]}")
    return completed


def manifest() -> dict:
    try:
        return json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignError(f"cannot read {MANIFEST}: {exc}") from exc


def canonical_qid(value: str) -> str:
    qid = value.upper()
    if not re.fullmatch(r"Q\d+", qid):
        raise CampaignError(f"invalid question ID: {value}")
    if qid not in manifest().get("questions", {}):
        raise CampaignError(f"unknown question ID: {qid}")
    return qid


def project_id(qid: str) -> str:
    value = manifest()["questions"][qid].get("aristotle_project_id", "")
    if not isinstance(value, str) or not UUID_RE.fullmatch(value):
        raise CampaignError(f"{qid} has no valid aristotle_project_id in pipeline.json")
    return value


def require_api_key() -> None:
    if os.environ.get("ARISTOTLE_API_KEY"):
        return
    account = ARISTOTLE_KEYCHAIN_ACCOUNT
    if account:
        found = subprocess.run(
            ["security", "find-generic-password", "-a", account,
             "-s", ARISTOTLE_KEYCHAIN_SERVICE, "-w"],
            text=True, capture_output=True,
        )
        if found.returncode == 0 and found.stdout.strip():
            os.environ["ARISTOTLE_API_KEY"] = found.stdout.strip()
            return
    raise CampaignError(
        "ARISTOTLE_API_KEY is missing from both the environment and the configured macOS Keychain item"
    )


def exact_chat_url(url: str) -> str:
    parsed = urlsplit(url)
    if parsed.scheme != "https" or parsed.netloc != "chatgpt.com" or "/c/" not in parsed.path:
        raise CampaignError("expected an exact https://chatgpt.com/.../c/... conversation URL")
    if parsed.username or parsed.password or not parsed.path.rstrip("/").split("/")[-1]:
        raise CampaignError("invalid ChatGPT conversation URL")
    return url


def osa(script: str, *args: str, timeout: int = 20) -> str:
    try:
        completed = subprocess.run(
            ["osascript", "-", *args], input=script, text=True,
            capture_output=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise CampaignError(f"Brave did not answer AppleScript within {timeout} seconds") from exc
    if completed.returncode:
        raise CampaignError((completed.stderr or "AppleScript failed").strip().splitlines()[-1])
    return completed.stdout.strip()


PROBE_JS = r'''(() => {
 const users=[...document.querySelectorAll('[data-message-author-role="user"]')];
 const assistants=[...document.querySelectorAll('[data-message-author-role="assistant"]')];
 const prompt=users.at(-1)?.innerText||'';
 const ids=[...prompt.matchAll(/\bQ\d+\b/gi)].map(m=>m[0].toUpperCase());
 const stop=!!document.querySelector('button[data-testid="stop-button"]');
 return JSON.stringify({state:stop?'active':(assistants.length?'complete':'unknown'),qid:ids[0]||null,turns:assistants.length});
})()'''


LIST_QUEUE_TABS = r'''on run argv
set output to ""
set rowSep to linefeed
tell application "Brave Browser"
 set queueWindow to front window
 set best to -1
 repeat with candidate in windows
  set n to 0
  repeat with candidateTab in tabs of candidate
   if URL of candidateTab starts with "https://chatgpt.com/c/" then set n to n + 1
  end repeat
  if n > best then
   set best to n
   set queueWindow to candidate
  end if
 end repeat
 repeat with t in tabs of queueWindow
   set tabURL to URL of t
   if tabURL starts with "https://chatgpt.com/c/" then
    set output to output & tabURL & rowSep
   end if
 end repeat
end tell
return output
end run'''


PROBE_EXACT = r'''on run argv
set targetURL to item 1 of argv
set probeJS to item 2 of argv
tell application "Brave Browser"
 repeat with w in windows
  repeat with t in tabs of w
   if URL of t is targetURL then return execute t javascript probeJS
  end repeat
 end repeat
end tell
return "{\"state\":\"unknown\",\"qid\":null,\"error\":\"tab disappeared\"}"
end run'''


LIST_ALL_CHAT_URLS = '''on run argv
set output to ""
tell application "Brave Browser"
 repeat with w in windows
  repeat with t in tabs of w
   set tabURL to URL of t
   if tabURL starts with "https://chatgpt.com/c/" then set output to output & tabURL & linefeed
  end repeat
 end repeat
end tell
return output
end run'''


CLOSE_EXACT = '''on run argv
set targetURL to item 1 of argv
tell application "Brave Browser"
 repeat with w in windows
  repeat with ti from (count of tabs of w) to 1 by -1
   if URL of tab ti of w is targetURL then
    close tab ti of w
    return "CLOSED"
   end if
  end repeat
 end repeat
end tell
return "NOT_FOUND"
end run'''


OPEN_EXACT = '''on run argv
set targetURL to item 1 of argv
tell application "Brave Browser"
 set queueWindow to front window
 set best to -1
 repeat with candidate in windows
  set n to 0
  repeat with candidateTab in tabs of candidate
   if URL of candidateTab starts with "https://chatgpt.com/c/" then set n to n + 1
  end repeat
  if n > best then
   set best to n
   set queueWindow to candidate
  end if
 end repeat
 tell queueWindow to make new tab with properties {URL:targetURL}
end tell
return "OPENED"
end run'''


def browser_probe(table: bool) -> None:
    urls = [url for url in osa(LIST_QUEUE_TABS).splitlines() if url]
    rows: list[dict] = []
    for url in urls:
        try:
            payload = osa(PROBE_EXACT, url, PROBE_JS, timeout=4)
            item = json.loads(payload)
        except (CampaignError, json.JSONDecodeError) as exc:
            item = {"state": "unknown", "qid": None, "error": str(exc)}
        item["url"] = url
        rows.append(item)
    rows.sort(key=lambda row: (row.get("state", ""), row.get("qid") or "", row["url"]))
    if table:
        print(f"{'STATE':<10} {'QID':<8} URL")
        for row in rows:
            print(f"{row['state']:<10} {(row.get('qid') or '-'):<8} {row['url']}")
    else:
        emit({"tabs": rows, "totals": {state: sum(r["state"] == state for r in rows) for state in ("active", "complete", "unknown")}})


def unique_exact_tab(url: str) -> None:
    target = exact_chat_url(url)
    count = sum(candidate == target for candidate in osa(LIST_ALL_CHAT_URLS).splitlines())
    if count != 1:
        raise CampaignError(f"expected exactly one matching tab, found {count}: {url}")


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as handle:
        handle.write(text)
        temporary = Path(handle.name)
    temporary.replace(path)


def browser_import(url: str, qid_arg: str, retry: bool, activate: bool) -> None:
    qid = qid_arg.upper()
    if not re.fullmatch(r"Q\d+", qid) or not (ROOT / "prompts" / f"{qid}.md").is_file():
        raise CampaignError(f"unknown question prompt: {qid}")
    unique_exact_tab(url)
    data = browser_sync.extract(url, activate=activate)
    if data.get("stop"):
        raise CampaignError("response is still generating")
    if "answer" not in data:
        raise CampaignError(data.get("error", "answer DOM is not loaded"))
    try:
        prompt = browser_sync.decode(data.get("prompt", ""))
        answer = browser_sync.decode(data["answer"])
    except (ValueError, UnicodeError) as exc:
        raise CampaignError(f"invalid browser payload: {exc}") from exc
    ids = {match.upper() for match in QID_RE.findall(prompt)}
    if qid not in ids:
        raise CampaignError(f"tab prompt does not identify {qid}")
    if len(answer) < 200:
        raise CampaignError("response is unexpectedly short")
    destination = ROOT / ("retry/responses" if retry else "responses") / f"{qid}.md"
    if retry and destination.exists():
        attempt = 2
        while (destination.parent / f"{qid}-retry-{attempt:02d}.md").exists():
            attempt += 1
        destination = destination.parent / f"{qid}-retry-{attempt:02d}.md"
    elif destination.exists():
        raise CampaignError(f"refusing to overwrite existing response: {destination.relative_to(ROOT)}")
    atomic_write(destination, answer.rstrip() + "\n")
    emit({"ok": True, "qid": qid, "url": url, "output": str(destination.relative_to(ROOT)), "chars": len(answer), "turns": data.get("count"), "retry": retry})


def browser_close(url: str) -> None:
    unique_exact_tab(url)
    if osa(CLOSE_EXACT, url) != "CLOSED":
        raise CampaignError(f"tab disappeared before close: {url}")
    emit({"ok": True, "closed": url})


def browser_open(url: str, cap: int) -> None:
    target = exact_chat_url(url)
    if cap < 1 or cap > MAX_BROWSER_TABS:
        raise CampaignError(f"browser cap is {MAX_BROWSER_TABS}; refusing --cap {cap}")
    all_urls = osa(LIST_ALL_CHAT_URLS).splitlines()
    if target in all_urls:
        raise CampaignError(f"refusing duplicate tab: {target}")
    queue_urls = [candidate for candidate in osa(LIST_QUEUE_TABS).splitlines() if candidate]
    if len(queue_urls) >= cap:
        raise CampaignError(f"managed queue already has {len(queue_urls)} tabs (cap {cap})")
    if osa(OPEN_EXACT, target) != "OPENED":
        raise CampaignError("Brave did not confirm the reopened conversation")
    emit({"ok": True, "opened": target, "active_before": len(queue_urls), "cap": cap})


def browser_submit(prompt: Path, cap: int) -> None:
    if cap < 1:
        raise CampaignError("--cap must be positive")
    if not prompt.is_file():
        raise CampaignError(f"prompt file not found: {prompt}")
    match = re.fullmatch(r"Q(\d+)(?:-retry-\d+)?\.md", prompt.name, re.I)
    is_retry = "retry" in prompt.parts
    if match and not is_retry and int(match.group(1)) > MAX_NEW_QID:
        raise CampaignError(
            f"new-problem cutoff is Q{MAX_NEW_QID}; refusing {prompt.name}"
        )
    completed = run([sys.executable, str(ROOT / "browser_submit.py"), str(prompt), "--cap", str(cap)])
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise CampaignError("browser_submit.py returned invalid JSON") from exc
    emit({"ok": True, **result})


def parse_latest_task(output: str) -> dict | None:
    statuses = "UNKNOWN|QUEUED|IN_PROGRESS|COMPLETE|COMPLETE_WITH_ERRORS|OUT_OF_BUDGET|FAILED|CANCELED"
    for line in output.splitlines():
        task_id = line[:36]
        status = re.search(rf"({statuses})\s*$", line)
        if UUID_RE.fullmatch(task_id) and status:
            middle = line[37 : status.start()].rstrip()
            created = middle[:20].strip()
            name = middle[21:].strip() if len(middle) > 20 else ""
            return {"task_id": task_id, "created": created, "name": name, "status": status.group(1)}
    return None


def remote_status(qid: str, pid: str) -> dict:
    try:
        result = run([*ARISTOTLE, "tasks", pid, "--limit", "1"])
        task = parse_latest_task(result.stdout)
        if result.stdout.strip() and task is None:
            raise CampaignError("could not parse Aristotle task status; refusing to infer idleness")
        return {"qid": qid, "project_id": pid, "task": task, "status": task["status"] if task else "NO_TASKS"}
    except CampaignError as exc:
        return {"qid": qid, "project_id": pid, "status": "ERROR", "error": str(exc)}


def aristotle_status(qid_args: list[str]) -> None:
    require_api_key()
    data = manifest()
    qids = [canonical_qid(value) for value in qid_args] if qid_args else list(data["questions"])
    items: list[dict | None] = [None] * len(qids)
    work: list[tuple[int, str, str]] = []
    for index, qid in enumerate(qids):
        pid = data["questions"][qid].get("aristotle_project_id", "")
        if isinstance(pid, str) and UUID_RE.fullmatch(pid):
            work.append((index, qid, pid))
        else:
            items[index] = {"qid": qid, "project_id": None, "status": "NO_PROJECT"}
    # Aristotle may silently return an empty task table under a burst of requests.
    # Keep the monitor deliberately gentle so "NO_TASKS" remains meaningful.
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(3, len(work) or 1)) as pool:
        futures = {pool.submit(remote_status, qid, pid): index for index, qid, pid in work}
        for future in concurrent.futures.as_completed(futures):
            items[futures[future]] = future.result()
    lock_path = MANIFEST.with_suffix(".lock")
    with lock_path.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        current = manifest()
        changed = False
        for remote in items:
            if not remote or remote.get("status") in {"ERROR", "NO_PROJECT"}:
                continue
            item = current["questions"].get(remote["qid"])
            if not isinstance(item, dict):
                continue
            task = remote.get("task")
            fields = {"aristotle_remote_status": remote["status"]}
            if task:
                fields.update({
                    "aristotle_latest_task_id": task["task_id"],
                    "aristotle_latest_task_status": task["status"],
                    "aristotle_latest_task_name": task["name"],
                    "aristotle_latest_task_created": task["created"],
                })
            if remote["status"] in ACTIVE_TASKS:
                fields["aristotle_status"] = "submitted"
                if task:
                    fields["aristotle_task_id"] = task["task_id"]
            for key, value in fields.items():
                if item.get(key) != value:
                    item[key] = value
                    changed = True
        if changed:
            atomic_write(MANIFEST, json.dumps(current, ensure_ascii=False, indent=2) + "\n")
    emit({"projects": items})


def aristotle_submit(qid_arg: str, request_file: Path) -> None:
    """Create one new Aristotle project, recording its identity atomically."""
    require_api_key()
    qid = canonical_qid(qid_arg)
    if not request_file.is_file():
        raise CampaignError(f"request file not found: {request_file}")
    request = request_file.read_text(encoding="utf-8").strip()
    if not request:
        raise CampaignError("Aristotle request is empty")
    lock_path = MANIFEST.with_suffix(".lock")
    with lock_path.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        current = manifest()
        item = current["questions"][qid]
        existing = item.get("aristotle_project_id", "")
        if isinstance(existing, str) and UUID_RE.fullmatch(existing):
            raise CampaignError(f"refusing duplicate project: {qid} already has {existing}")
        submitted = run([*ARISTOTLE, "formalize", str(request_file.resolve())])
        combined = submitted.stdout + "\n" + submitted.stderr
        if re.search(r"(^|\n)\s*ERROR\s*-", combined):
            raise CampaignError(combined.strip().splitlines()[-1])
        matches = re.findall(
            r"(?:Project created:|Project:)\s*"
            r"([0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12})",
            combined,
            flags=re.IGNORECASE,
        )
        if not matches:
            raise CampaignError("Aristotle returned no project ID; project was not recorded")
        pid = matches[-1]
        after = remote_status(qid, pid)
        if after["status"] not in ACTIVE_TASKS:
            raise CampaignError(
                "Aristotle created a project but no active task was found; latest status is "
                f"{after['status']}"
            )
        item.update({
            "aristotle_status": "submitted",
            "aristotle_project_id": pid,
            "aristotle_task_id": after["task"]["task_id"],
            "aristotle_latest_task_id": after["task"]["task_id"],
            "aristotle_latest_task_status": after["task"]["status"],
            "aristotle_remote_status": after["status"],
            "aristotle_request_path": str(request_file),
            "aristotle_request_sha256": hashlib.sha256(request.encode()).hexdigest(),
        })
        atomic_write(MANIFEST, json.dumps(current, ensure_ascii=False, indent=2) + "\n")
    emit({"ok": True, "qid": qid, "project_id": pid, "request_file": str(request_file), "latest": after})


def aristotle_continue(qid_arg: str, prompt_file: Path) -> None:
    require_api_key()
    qid = canonical_qid(qid_arg)
    pid = project_id(qid)
    if not prompt_file.is_file():
        raise CampaignError(f"prompt file not found: {prompt_file}")
    prompt = prompt_file.read_text(encoding="utf-8").strip()
    if not prompt:
        raise CampaignError("continuation prompt is empty")
    lock_path = MANIFEST.with_suffix(".lock")
    with lock_path.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        before = remote_status(qid, pid)
        if before["status"] == "ERROR":
            raise CampaignError(before["error"])
        if before["status"] in ACTIVE_TASKS:
            raise CampaignError(f"refusing duplicate continuation: newest task is {before['status']} ({before['task']['task_id']})")
        submitted = run([*ARISTOTLE, "continue", pid, prompt, "--mode", "instruct"])
        combined = submitted.stdout + "\n" + submitted.stderr
        if re.search(r"(^|\n)\s*ERROR\s*-", combined):
            raise CampaignError(combined.strip().splitlines()[-1])
        after = remote_status(qid, pid)
        if after["status"] not in ACTIVE_TASKS:
            raise CampaignError(
                "Aristotle accepted no continuation task; latest task is still "
                f"{after['status']}"
            )
        current = manifest()
        item = current["questions"][qid]
        item.update({
            "aristotle_status": "submitted",
            "aristotle_task_id": after["task"]["task_id"],
            "aristotle_latest_task_id": after["task"]["task_id"],
            "aristotle_latest_task_status": after["task"]["status"],
            "aristotle_remote_status": after["status"],
            "aristotle_followup_prompt": str(prompt_file),
            "aristotle_followup_prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
        })
        atomic_write(MANIFEST, json.dumps(current, ensure_ascii=False, indent=2) + "\n")
    emit({"ok": True, "qid": qid, "project_id": pid, "prompt_file": str(prompt_file), "latest": after})


def aristotle_download(qid_arg: str, destination: Path) -> None:
    require_api_key()
    qid = canonical_qid(qid_arg)
    pid = project_id(qid)
    destination = destination.resolve()
    if destination.exists():
        raise CampaignError(f"refusing to overwrite existing archive: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    run([*ARISTOTLE, "download", pid, "--destination", str(destination)])
    if not destination.is_file():
        raise CampaignError("Aristotle reported success but created no archive")
    digest = hashlib.sha256(destination.read_bytes()).hexdigest()
    emit({"ok": True, "qid": qid, "project_id": pid, "destination": str(destination), "bytes": destination.stat().st_size, "sha256": digest})


def aristotle_schedule(*, dry_run: bool, cap: int) -> None:
    """Reconcile the whole remote queue and fill it without exceeding ``cap``."""
    if cap < 1 or cap > 15:
        raise CampaignError("Aristotle concurrency cap must be between 1 and 15")
    # Dry-run still performs live reconciliation.  Without credentials the
    # Aristotle CLI may return an empty task table, which must never be
    # mistaken for an idle queue.
    require_api_key()

    def list_tasks(pid: str) -> list[dict[str, str]]:
        result = run([*ARISTOTLE, "tasks", pid, "--limit", "100"])
        tasks = scheduler.parse_tasks(result.stdout)
        if result.stdout.strip() and not tasks:
            raise CampaignError(f"could not parse Aristotle tasks for {pid}")
        return tasks

    lock_path = MANIFEST.with_suffix(".lock")
    with lock_path.open("w") as lock:
        # One process owns reconciliation, decision, submission, and recording.
        # Holding this advisory lock across network calls prevents two campaign
        # operators from consuming the same slot or submitting the same item.
        fcntl.flock(lock, fcntl.LOCK_EX)
        current = manifest()
        active, active_projects = scheduler.reconcile(current, list_tasks)
        queue = scheduler.candidates(current, ROOT, active_projects)
        slots = max(0, cap - active)
        selected = queue[:slots]
        plan = [{"qid": c.qid, "kind": c.kind, "path": str(c.path.relative_to(ROOT))} for c in selected]
        if dry_run:
            emit({"ok": True, "dry_run": True, "cap": cap, "active": active,
                  "free_slots": slots, "eligible": len(queue), "selected": plan})
            return

        # Persist reconciliation before any external mutation.
        atomic_write(MANIFEST, json.dumps(current, ensure_ascii=False, indent=2) + "\n")
        submitted: list[dict] = []
        for candidate in selected:
            if not candidate.path.is_file():
                raise CampaignError(f"request file not found: {candidate.path.relative_to(ROOT)}")
            content = candidate.path.read_text(encoding="utf-8").strip()
            if not content:
                raise CampaignError(f"request file is empty: {candidate.path.relative_to(ROOT)}")
            # Persist intent first: if the CLI creates a remote task and then
            # crashes, a later scheduler cannot blindly duplicate it.
            scheduler.mark_intent(current, candidate)
            atomic_write(MANIFEST, json.dumps(current, ensure_ascii=False, indent=2) + "\n")
            if candidate.kind == "project":
                raw = run([*ARISTOTLE, "formalize", str(candidate.path.resolve())])
                matches = re.findall(
                    r"(?:Project created:|Project:)\s*"
                    r"([0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12})",
                    raw.stdout + "\n" + raw.stderr, flags=re.I,
                )
                if not matches:
                    raise CampaignError("Aristotle returned no project ID; submission remains marked submitting")
                pid = matches[-1]
                owners = [qid for qid, item in current["questions"].items()
                          if qid != candidate.qid and item.get("aristotle_project_id") == pid]
                if owners:
                    raise CampaignError(f"Aristotle returned project ID already owned by {owners[0]}")
            else:
                pid = candidate.project_id or ""
                run([*ARISTOTLE, "continue", pid, content, "--mode", "instruct"])
            tasks = list_tasks(pid)
            if not tasks or tasks[0]["status"] not in ACTIVE_TASKS:
                raise CampaignError(f"Aristotle created no active task for {candidate.qid}; submission remains marked submitting")
            result = {"project_id": pid, "task": tasks[0]}
            scheduler.record_submission(current, candidate, result, content)
            atomic_write(MANIFEST, json.dumps(current, ensure_ascii=False, indent=2) + "\n")
            submitted.append({"qid": candidate.qid, "kind": candidate.kind,
                              "project_id": pid, "task_id": tasks[0]["task_id"]})
        emit({"ok": True, "dry_run": False, "cap": cap, "active_before": active,
              "submitted": submitted, "active_after": active + len(submitted)})


GH_FIELDS = "conclusion,createdAt,databaseId,event,headBranch,headSha,name,status,updatedAt,url,workflowName"


def latest_ci() -> dict:
    completed = run(["gh", "run", "list", "--limit", "1", "--json", GH_FIELDS])
    rows = json.loads(completed.stdout)
    if not rows:
        raise CampaignError("no GitHub Actions runs found")
    return rows[0]


def ci_latest() -> None:
    emit(latest_ci())


def ci_view(run_id: str | None) -> None:
    selected = run_id or str(latest_ci()["databaseId"])
    fields = GH_FIELDS + ",jobs"
    completed = run(["gh", "run", "view", selected, "--json", fields])
    emit(json.loads(completed.stdout))


def ci_logs(run_id: str | None, failed: bool) -> None:
    """Return CI logs through the campaign wrapper for failure diagnosis."""
    selected = run_id or str(latest_ci()["databaseId"])
    command = ["gh", "run", "view", selected, "--log-failed" if failed else "--log"]
    completed = run(command)
    print(completed.stdout, end="")


def book_build() -> None:
    rendered = run([sys.executable, str(ROOT / "proof_pipeline.py"), "render"])
    run(["latexmk", "-lualatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"], cwd=ROOT / "publication")
    pdf = ROOT / "publication/main.pdf"
    if not pdf.is_file():
        raise CampaignError("latexmk succeeded but publication/main.pdf is missing")
    emit({"ok": True, "render": rendered.stdout.strip(), "pdf": str(pdf.relative_to(ROOT)), "bytes": pdf.stat().st_size})


def parser() -> argparse.ArgumentParser:
    top = argparse.ArgumentParser(description=__doc__)
    groups = top.add_subparsers(dest="group", required=True)

    browser = groups.add_parser("browser")
    browser_commands = browser.add_subparsers(dest="command", required=True)
    probe = browser_commands.add_parser("probe")
    probe.add_argument("--table", action="store_true", help="human-readable output (JSON is the default)")
    imported = browser_commands.add_parser("import")
    imported.add_argument("url")
    imported.add_argument("qid")
    imported.add_argument("--retry", action="store_true")
    imported.add_argument("--activate", action="store_true")
    closed = browser_commands.add_parser("close")
    closed.add_argument("url")
    opened = browser_commands.add_parser("open")
    opened.add_argument("url")
    opened.add_argument("--cap", type=int, default=MAX_BROWSER_TABS)
    submitted = browser_commands.add_parser("submit")
    submitted.add_argument("prompt", type=Path)
    submitted.add_argument("--cap", type=int, default=7)

    aristotle = groups.add_parser("aristotle")
    aristotle_commands = aristotle.add_subparsers(dest="command", required=True)
    status = aristotle_commands.add_parser("status")
    status.add_argument("qids", nargs="*")
    submitted = aristotle_commands.add_parser("submit")
    submitted.add_argument("qid")
    submitted.add_argument("request_file", type=Path)
    continued = aristotle_commands.add_parser("continue")
    continued.add_argument("qid")
    continued.add_argument("prompt_file", type=Path)
    downloaded = aristotle_commands.add_parser("download")
    downloaded.add_argument("qid")
    downloaded.add_argument("destination", type=Path)
    scheduled = aristotle_commands.add_parser("schedule")
    scheduled.add_argument("--dry-run", action="store_true")
    scheduled.add_argument("--cap", type=int, default=15)

    ci = groups.add_parser("ci")
    ci_commands = ci.add_subparsers(dest="command", required=True)
    ci_commands.add_parser("latest")
    view = ci_commands.add_parser("view")
    view.add_argument("run_id", nargs="?")
    logs = ci_commands.add_parser("logs")
    logs.add_argument("run_id", nargs="?")
    logs.add_argument("--failed", action="store_true")

    book = groups.add_parser("book")
    book_commands = book.add_subparsers(dest="command", required=True)
    book_commands.add_parser("build")
    return top


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if (args.group, args.command) == ("browser", "probe"):
            browser_probe(args.table)
        elif (args.group, args.command) == ("browser", "import"):
            browser_import(args.url, args.qid, args.retry, args.activate)
        elif (args.group, args.command) == ("browser", "close"):
            browser_close(args.url)
        elif (args.group, args.command) == ("browser", "open"):
            browser_open(args.url, args.cap)
        elif (args.group, args.command) == ("browser", "submit"):
            browser_submit(args.prompt, args.cap)
        elif (args.group, args.command) == ("aristotle", "status"):
            aristotle_status(args.qids)
        elif (args.group, args.command) == ("aristotle", "submit"):
            aristotle_submit(args.qid, args.request_file)
        elif (args.group, args.command) == ("aristotle", "continue"):
            aristotle_continue(args.qid, args.prompt_file)
        elif (args.group, args.command) == ("aristotle", "download"):
            aristotle_download(args.qid, args.destination)
        elif (args.group, args.command) == ("aristotle", "schedule"):
            aristotle_schedule(dry_run=args.dry_run, cap=args.cap)
        elif (args.group, args.command) == ("ci", "latest"):
            ci_latest()
        elif (args.group, args.command) == ("ci", "view"):
            ci_view(args.run_id)
        elif (args.group, args.command) == ("ci", "logs"):
            ci_logs(args.run_id, args.failed)
        elif (args.group, args.command) == ("book", "build"):
            book_build()
        return 0
    except (CampaignError, scheduler.SchedulerError, OSError, UnicodeError,
            json.JSONDecodeError, subprocess.SubprocessError) as exc:
        emit({"ok": False, "error": str(exc)}, stream=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
