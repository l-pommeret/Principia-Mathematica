import importlib.util
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "verify_anomaly_registry", ROOT / "scripts/verify_anomaly_registry.py")
anomalies = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(anomalies)


class AnomalyRegistryTests(unittest.TestCase):
    def test_registry_is_generated_and_backfills_required_cases(self):
        payload = anomalies.verify_registry()
        entries = {entry["id"]: entry for entry in payload["entries"]}
        self.assertIn("PM1-ANOM-Q220-ASSOCIATION-GAP", entries)
        self.assertIn("PM1-ANOM-Q221-FIRST-ARCHIVE-FIDELITY-GAP", entries)
        self.assertEqual(entries["PM1-ANOM-Q222-ASSOCIATION-GAP"]["minimal_relaxation"], ["PM1:✱2·32"])
        self.assertEqual(
            entries["PM1-ANOM-Q222-RELAXED-ARCHIVE-UNCOVERED-CITATIONS"]
            ["resolution_status"],
            "blocked-awaiting-targeted-fidelity-continuation",
        )
        chain = entries["PM1-ANOM-Q222-CHAIN-COMPOSITION-GAP"]
        self.assertEqual(chain["category"], "incomplete-printed-citation")
        self.assertFalse(chain["strict"])
        self.assertEqual(chain["relaxation_use"][0]["uses"], 2)
        self.assertEqual(
            entries["PM1-ANOM-Q222-RETRY03-AUDITED-RELAXED-OUTPUT"]["resolution_status"],
            "resolved-clean-output-kernel-checked",
        )
        q223 = entries["PM1-ANOM-Q223-IMPLICIT-COMPOSITION-GAP"]
        self.assertEqual(q223["category"], "incomplete-printed-citation")
        self.assertFalse(q223["strict"])
        self.assertEqual([use["target"] for use in q223["relaxation_use"]], ["PM1:✱3·27", "PM1:✱3·31"])
        self.assertGreaterEqual(sum(entry["category"] == "digital-witness-error" for entry in entries.values()), 1)
        incidents = {incident["id"]: incident for incident in payload["infrastructure_incidents"]}
        q226 = incidents["PM1-INFRA-Q226-ARISTOTLE-HTTP500"]
        self.assertEqual(q226["authoritative_status"], "IN_PROGRESS confirmed by repeated polling")
        self.assertEqual(q226["classification"], "infrastructure-transport-failure")
        self.assertIn("neither a PM source anomaly", q226["pm_or_reconstruction_impact"])

    def test_registry_cannot_drop_an_attested_digital_witness_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ("metadata/anomalies", "metadata/apparatus", "metadata/errata", "metadata/schema"):
                shutil.copytree(ROOT / relative, root / relative)
            path = root / "metadata/anomalies/PM1-anomaly-register.json"
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["entries"] = [entry for entry in payload["entries"] if entry["category"] != "digital-witness-error"]
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(SystemExit):
                anomalies.verify_registry(root)

    def test_q222_cannot_claim_a_strict_reconstruction(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ("metadata/anomalies", "metadata/apparatus", "metadata/errata", "metadata/schema"):
                shutil.copytree(ROOT / relative, root / relative)
            path = root / "metadata/anomalies/manual/PM1-reconstruction-gaps.json"
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["entries"][2]["minimal_relaxation"] = []
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(SystemExit):
                anomalies.verify_registry(root)


if __name__ == "__main__":
    unittest.main()
