import unittest
import json
import subprocess
import tempfile
from pathlib import Path
from unittest import mock

import aristotle_scheduler as scheduler
import campaign


def task(n: int, status: str) -> dict[str, str]:
    return {"task_id": f"00000000-0000-0000-0000-{n:012d}", "status": status,
            "created": "now", "name": f"task {n}"}


class SchedulerTests(unittest.TestCase):
    def test_parse_all_tasks(self):
        text = (
            "00000000-0000-0000-0000-000000000001  1 min ago            Formalize Q1 QUEUED\n"
            "00000000-0000-0000-0000-000000000002  2 mins ago           Old task COMPLETE\n"
        )
        self.assertEqual([t["status"] for t in scheduler.parse_tasks(text)], ["QUEUED", "COMPLETE"])

    def test_reconcile_counts_all_active_tasks_not_projects(self):
        pid = "10000000-0000-0000-0000-000000000001"
        data = {"questions": {"Q1": {"aristotle_project_id": pid}}}
        count, projects = scheduler.reconcile(
            data, lambda _: [task(1, "QUEUED"), task(2, "IN_PROGRESS"), task(3, "COMPLETE")]
        )
        self.assertEqual(count, 2)
        self.assertEqual(projects, {pid})

    def test_continuations_are_prioritized_and_active_project_excluded(self):
        root = Path("/repo")
        p1 = "10000000-0000-0000-0000-000000000001"
        p2 = "10000000-0000-0000-0000-000000000002"
        data = {"items": {"D": {"status": "kernel-checked"}}, "questions": {
            "Q9": {"audit_status": "A", "dependencies": ["D"], "aristotle_status": "not-submitted", "prompt_path": "aristotle/Q9.md"},
            "Q2": {"audit_status": "A", "dependencies": ["D"], "aristotle_project_id": p1,
                   "aristotle_continuation_status": "not-submitted", "aristotle_continuation_path": "aristotle/followups/Q2.md"},
            "Q3": {"audit_status": "A", "dependencies": ["D"], "aristotle_project_id": p2,
                   "aristotle_continuation_status": "not-submitted", "aristotle_continuation_path": "aristotle/followups/Q3.md"},
        }}
        got = scheduler.candidates(data, root, {p2})
        self.assertEqual([(c.qid, c.kind) for c in got], [("Q2", "continuation"), ("Q9", "project")])

    def test_unchecked_dependency_and_existing_project_never_submit(self):
        pid = "10000000-0000-0000-0000-000000000001"
        data = {"items": {"bad": {"status": "not-submitted"}}, "questions": {
            "Q1": {"audit_status": "A", "dependencies": ["bad"], "aristotle_status": "not-submitted", "prompt_path": "a"},
            "Q2": {"audit_status": "A", "dependencies": [], "aristotle_status": "not-submitted", "prompt_path": "b", "aristotle_project_id": pid},
            "Q3": {"audit_status": "B", "dependencies": [], "aristotle_status": "not-submitted", "prompt_path": "c"},
        }}
        self.assertEqual(scheduler.candidates(data, Path("/repo"), set()), [])

    def test_duplicate_remote_identity_is_fatal(self):
        pid = "10000000-0000-0000-0000-000000000001"
        data = {"questions": {"Q1": {"aristotle_project_id": pid}, "Q2": {"aristotle_project_id": pid}}}
        with self.assertRaises(scheduler.SchedulerError):
            scheduler.reconcile(data, lambda _: [])

    def test_intent_removes_project_from_future_candidates(self):
        data = {"items": {}, "questions": {"Q1": {
            "audit_status": "A", "aristotle_status": "not-submitted", "prompt_path": "aristotle/Q1.md"
        }}}
        candidate = scheduler.candidates(data, Path("/repo"), set())[0]
        scheduler.mark_intent(data, candidate)
        self.assertEqual(scheduler.candidates(data, Path("/repo"), set()), [])

    def test_retry_uses_canonical_project_without_a_second_promotion(self):
        pid = "10000000-0000-0000-0000-000000000001"
        data = {"items": {}, "questions": {
            "Q234": {"aristotle_project_id": pid},
            "Q9001": {
                "retry_of": "Q234", "promotion_key": "Q234",
                "canonical_promotion_forbidden": True,
                "aristotle_retry_status": "not-submitted",
                "aristotle_retry_path": "aristotle/followups/Q234.md",
            },
        }}
        candidate = scheduler.candidates(data, Path("/repo"), set())[0]
        self.assertEqual((candidate.qid, candidate.kind, candidate.project_id), ("Q9001", "retry", pid))
        scheduler.mark_intent(data, candidate)
        self.assertEqual(data["questions"]["Q9001"]["aristotle_retry_status"], "submitting")

    def test_retry_cannot_promote_itself(self):
        data = {"items": {}, "questions": {
            "Q234": {"aristotle_project_id": "10000000-0000-0000-0000-000000000001"},
            "Q9001": {"retry_of": "Q234", "promotion_key": "Q9001",
                      "canonical_promotion_forbidden": True,
                      "aristotle_retry_status": "not-submitted", "aristotle_retry_path": "x"},
        }}
        with self.assertRaises(scheduler.SchedulerError):
            scheduler.candidates(data, Path("/repo"), set())

    def test_record_preserves_nested_manifest_path(self):
        pid = "10000000-0000-0000-0000-000000000001"
        data = {"questions": {"Q1": {}}}
        candidate = scheduler.Candidate(
            "Q1", "continuation", Path("/repo/aristotle/followups/Q1.md"), pid,
            "aristotle/followups/Q1.md",
        )
        scheduler.record_submission(data, candidate, {"project_id": pid, "task": task(1, "QUEUED")}, "go")
        self.assertEqual(data["questions"]["Q1"]["aristotle_followup_prompt"],
                         "aristotle/followups/Q1.md")

    def test_campaign_submission_records_active_task(self):
        """Exercise the non-dry-run status guard without any network access."""
        pid = "10000000-0000-0000-0000-000000000001"
        tid = "00000000-0000-0000-0000-000000000001"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = root / "aristotle" / "Q1.md"
            request.parent.mkdir()
            request.write_text("prove Q1\n", encoding="utf-8")
            manifest = root / "pipeline.json"
            manifest.write_text(json.dumps({
                "items": {},
                "questions": {"Q1": {
                    "audit_status": "A", "dependencies": [],
                    "aristotle_status": "not-submitted",
                    "prompt_path": "aristotle/Q1.md",
                }},
            }), encoding="utf-8")
            calls = 0

            def fake_run(command, **_kwargs):
                nonlocal calls
                calls += 1
                if "formalize" in command:
                    output = f"Project created: {pid}\n"
                elif calls == 1:  # reconciliation: the question has no project yet
                    output = ""
                else:
                    output = (
                        f"{tid}  1 min ago            Formalize Q1.md QUEUED\n"
                    )
                return subprocess.CompletedProcess(command, 0, output, "")

            with mock.patch.object(campaign, "ROOT", root), \
                 mock.patch.object(campaign, "MANIFEST", manifest), \
                 mock.patch.object(campaign, "require_api_key"), \
                 mock.patch.object(campaign, "run", side_effect=fake_run), \
                 mock.patch.object(campaign, "emit"):
                campaign.aristotle_schedule(dry_run=False, cap=15)
            recorded = json.loads(manifest.read_text(encoding="utf-8"))["questions"]["Q1"]
            self.assertEqual(recorded["aristotle_project_id"], pid)
            self.assertEqual(recorded["aristotle_latest_task_status"], "QUEUED")

    def test_campaign_dry_run_counts_two_remote_active_projects(self):
        pids = [
            "10000000-0000-0000-0000-000000000001",
            "10000000-0000-0000-0000-000000000002",
        ]
        tids = [
            "00000000-0000-0000-0000-000000000001",
            "00000000-0000-0000-0000-000000000002",
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / "pipeline.json"
            manifest.write_text(json.dumps({
                "items": {},
                "questions": {
                    "Q1": {"aristotle_project_id": pids[0]},
                    "Q2": {"aristotle_project_id": pids[1]},
                },
            }), encoding="utf-8")
            statuses = dict(zip(pids, zip(tids, ["QUEUED", "IN_PROGRESS"])))

            def fake_run(command, **_kwargs):
                pid = command[command.index("tasks") + 1]
                tid, status = statuses[pid]
                output = f"{tid}  1 min ago            Formalize {pid} {status}\n"
                return subprocess.CompletedProcess(command, 0, output, "")

            emitted = []
            with mock.patch.object(campaign, "ROOT", root), \
                 mock.patch.object(campaign, "MANIFEST", manifest), \
                 mock.patch.object(campaign, "require_api_key") as require_key, \
                 mock.patch.object(campaign, "run", side_effect=fake_run), \
                 mock.patch.object(campaign, "emit", side_effect=emitted.append):
                campaign.aristotle_schedule(dry_run=True, cap=15)
            require_key.assert_called_once_with()
            self.assertEqual(emitted[-1]["active"], 2)
            self.assertEqual(emitted[-1]["free_slots"], 13)


if __name__ == "__main__":
    unittest.main()
