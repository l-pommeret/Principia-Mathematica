import copy
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_dependencies as dependencies


class DependencyAuditTests(unittest.TestCase):
    def test_pm_decimal_order_is_not_filename_order(self):
        self.assertLess(dependencies.pm_order("PM1:✱2·08"), dependencies.pm_order("PM1:✱2·1"))
        self.assertLess(dependencies.pm_order("PM1:✱2·1"), dependencies.pm_order("PM1:✱2·11"))
        self.assertLess(dependencies.pm_order("PM1:✱2·11"), dependencies.pm_order("PM1:✱2·33"))

    def test_current_kernel_checked_corpus_is_covered(self):
        graph = dependencies.audit(ROOT)
        checked = graph["coverage"]["audited_items"]
        expected_checked = sum(node["formal_status"] == "kernel-checked" for node in graph["nodes"])
        self.assertEqual(checked, expected_checked)
        self.assertGreaterEqual(checked, 17)
        self.assertTrue(graph["historical_graph"]["edges"])
        self.assertTrue(graph["lean_graph"]["edges"])

    def test_detach_resolves_to_printed_function_rule(self):
        items = {item["id"]: item for item in dependencies.load_items(ROOT)}
        item = items["PM1:✱2·06"]
        declarations = {candidate["declaration"]: candidate["id"] for candidate in items.values()}
        actual = dependencies.extract_lean_dependencies(item, declarations, ROOT)
        normalized = dependencies.normalize(item, actual, declarations, ROOT)
        self.assertIn("PM1:✱1·11", normalized)
        self.assertNotIn("PM1:✱1·1", normalized)

    def test_unjustified_definition_bridge_is_rejected(self):
        items = {item["id"]: item for item in dependencies.load_items(ROOT)}
        item = copy.deepcopy(items["PM1:✱2·01"])
        item["dependency_justifications"][0]["evidence"] = ""
        declarations = {candidate["declaration"]: candidate["id"] for candidate in items.values()}
        actual = dependencies.extract_lean_dependencies(item, declarations, ROOT)
        with self.assertRaises(dependencies.DependencyError):
            dependencies.normalize(item, actual, declarations, ROOT)

    def test_unindexed_qualified_reference_is_rejected(self):
        item = {"id": "PM1:TEST"}
        with self.assertRaises(dependencies.DependencyError):
            dependencies.reject_unindexed_references(
                item, "theorem test : True := Classical.choice h", set()
            )


if __name__ == "__main__":
    unittest.main()
