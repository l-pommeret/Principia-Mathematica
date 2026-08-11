import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from pm_batch_audit import audit_batch
from pm_constraint_manifest import compile_batch_manifest
from pm_proof_skeleton import parse_demonstration


def item(identifier, declaration):
    return {
        "id": identifier,
        "declaration": declaration,
        "lean_path": "unused.lean",
        "normalized_dependencies": [],
        "formal_status": "kernel-checked",
    }


class BatchAuditTests(unittest.TestCase):
    def test_strict_and_relaxed_targets_are_classified_independently(self):
        registry = {
            "PM1:✱1·2": item("PM1:✱1·2", "PM.Base.star_1_2"),
            "PM1:✱1·3": item("PM1:✱1·3", "PM.Base.star_1_3"),
            "PM1:✱1·11": item("PM1:✱1·11", "PM.Derivation.star_1_11"),
        }
        first = parse_demonstration("✱8·1. ⊢ : p [✱1·2]", current_item="PM1:✱8·1")
        second = parse_demonstration("✱8·2. ⊢ : p [✱8·1]", current_item="PM1:✱8·2")
        batch = compile_batch_manifest(
            [first, second], registry,
            {"PM1:✱8·1": "PM.Batch.star_8_1", "PM1:✱8·2": "PM.Batch.star_8_2"},
        )
        source = """namespace PM.Batch
theorem star_8_1 : True := by exact PM.Base.star_1_2
theorem star_8_2 : True := by exact star_8_1; exact PM.Base.star_1_3
end PM.Batch
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Result.lean"
            path.write_text(source, encoding="utf-8")
            result = audit_batch(batch, path, registry, {"lean_realizations": {}})
        self.assertEqual(result["target_audits"][0]["classification"], "strict-closure")
        self.assertEqual(result["target_audits"][1]["classification"], "relaxed-closure")
        self.assertEqual(result["target_audits"][1]["added_beyond_print"], ["PM1:✱1·3"])
        self.assertFalse(result["all_targets_strict"])


if __name__ == "__main__":
    unittest.main()
