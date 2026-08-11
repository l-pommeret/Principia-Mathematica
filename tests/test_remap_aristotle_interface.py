import io
import json
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from remap_aristotle_interface import batch_plan, run_remap, scan_declarations, sha256_bytes


def write_archive(path: Path, members: dict[str, str]) -> None:
    with tarfile.open(path, "w:gz") as archive:
        for name, text in members.items():
            raw = text.encode("utf-8")
            info = tarfile.TarInfo(name)
            info.size = len(raw)
            archive.addfile(info, io.BytesIO(raw))


class AristotleInterfaceRemapTests(unittest.TestCase):
    def test_q296_has_exact_one_to_one_insertion_plan(self):
        plan = batch_plan(ROOT, "Q296")
        self.assertTrue(plan["requires_one_to_one_kernel_remap"])
        self.assertTrue(plan["canonical_integration_forbidden"])
        self.assertEqual(len(plan["targets"]), 1)
        target = plan["targets"][0]
        self.assertEqual(target["id"], "PM1:✱14·01")
        self.assertEqual(
            target["source"], "PM.DescriptionSyntax.Formula.star_14_01"
        )
        self.assertEqual(target["canonical"], target["source"])
        self.assertTrue(target["insertion_target"])

    def test_q228_plan_is_exact_and_non_promotional(self):
        plan = batch_plan(ROOT, "Q228")
        self.assertEqual([target["id"] for target in plan["targets"]], [
            "PM1:✱4·11", "PM1:✱4·14", "PM1:✱4·15", "PM1:✱4·2",
        ])
        self.assertTrue(plan["canonical_integration_forbidden"])
        self.assertTrue(all(len(target["signature_sha256"]) == 64 for target in plan["targets"]))

    def test_q259_targets_are_insertions_with_exact_signatures(self):
        plan = batch_plan(ROOT, "Q259")
        self.assertEqual([target["id"] for target in plan["targets"]], [
            "PM1:✱9·3", "PM1:✱9·31", "PM1:✱9·32", "PM1:✱9·33",
        ])
        self.assertTrue(all(target["insertion_target"] for target in plan["targets"]))
        self.assertEqual(plan["archive_sha256"],
                         "71fca398baa073201f5975ff632c75de1d8659b504de0c858ae90c2b7d0e0b6e")

    def test_q259_clean_four_target_fixture_is_transplantable_at_canonical_names(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Principia").mkdir()
            archive = root / "result.tar.gz"
            source = "\n".join([
                "namespace PM.Local",
                *[f"theorem target_{index} : True := by trivial" for index in range(4)],
                "end PM.Local", "",
            ])
            write_archive(archive, {"Targets.lean": source})
            targets = []
            for index in range(4):
                signature = f"theorem target_{index} : True\n"
                targets.append({
                    "id": f"fixture-{index}", "source": f"PM.Local.target_{index}",
                    "canonical": f"PM.Canonical.target_{index}", "signature": signature,
                    "signature_sha256": __import__("hashlib").sha256(
                        signature.encode("utf-8")).hexdigest(), "insertion_target": True,
                })
            plan = {"kind": "pm-interface-kernel-remap-plan", "batch": "Q259",
                    "archive_sha256": sha256_bytes(archive.read_bytes()), "targets": targets}
            transplant = root / "candidate.lean"
            with patch("remap_aristotle_interface.batch_plan", return_value=plan):
                report = run_remap(root, "Q259", archive, transplant=transplant)
            self.assertEqual(report["status"], "transplantable-interface-only")
            self.assertEqual(transplant.read_text(encoding="utf-8").count("namespace PM.Canonical"), 4)

    def test_unavailable_archive_produces_machine_readable_block(self):
        report = run_remap(ROOT, "Q229")
        self.assertEqual(report["status"], "blocked")
        self.assertIn("terminal archive unavailable", report["reasons"])
        self.assertTrue(report["policy"]["canonical_integration_forbidden"])

    def test_unmapped_helper_and_axiom_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / "result.tar.gz"
            write_archive(archive, {
                "Result.lean": """namespace PM.Local
axiom imported_interface : True
theorem target : True := by trivial
def helper : Nat := 0
end PM.Local
""",
            })
            # The Q300 archive has no registered digest and its canonical
            # target is intentionally absent; independently, the report must
            # make the local declarations visible as unmapped.
            report = run_remap(ROOT, "Q300", archive)
            self.assertEqual(report["status"], "blocked")
            joined = "\n".join(report["reasons"])
            self.assertIn("unmapped local declarations", joined)
            self.assertIn("PM.Local.imported_interface", joined)
            self.assertIn("PM.Local.helper", joined)
            self.assertIn("Q300 forbids archive-local declarations", joined)

    def test_q300_target_is_an_insertion_not_a_missing_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Principia").mkdir()
            archive = root / "result.tar.gz"
            write_archive(archive, {"Target.lean": """namespace PM.Local
theorem target : True := by trivial
end PM.Local
"""})
            signature = "theorem target : True\n"
            plan = {
                "kind": "pm-interface-kernel-remap-plan", "batch": "Q300",
                "archive_sha256": sha256_bytes(archive.read_bytes()),
                "targets": [{"id": "PM1:✱9·21", "source": "PM.Local.target",
                             "canonical": "PM.Canonical.target", "signature": signature,
                             "signature_sha256": __import__("hashlib").sha256(
                                 signature.encode("utf-8")).hexdigest(),
                             "insertion_target": True}],
            }
            transplant = root / "candidate.lean"
            with patch("remap_aristotle_interface.batch_plan", return_value=plan):
                report = run_remap(root, "Q300", archive, transplant=transplant)
            self.assertEqual(report["status"], "transplantable-interface-only")
            self.assertFalse(report["canonical_declarations"][0]["exists"])
            self.assertEqual(report["canonical_declarations"][0]["role"], "target-insertion")
            rendered = transplant.read_text(encoding="utf-8")
            self.assertIn("namespace PM.Canonical", rendered)
            self.assertIn("end PM.Canonical", rendered)

    def test_exact_bijective_remap_emits_only_an_interface_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            canonical = root / "Principia/Canonical.lean"
            canonical.parent.mkdir()
            canonical.write_text("""namespace PM.Canonical
theorem target : True := by trivial
end PM.Canonical
""", encoding="utf-8")
            archive = root / "result.tar.gz"
            write_archive(archive, {"Result.lean": """namespace PM.Local
theorem target : True := by trivial
end PM.Local
"""})
            signature = "theorem target : True\n"
            plan = {
                "kind": "pm-interface-kernel-remap-plan", "batch": "fixture",
                "archive_sha256": sha256_bytes(archive.read_bytes()),
                "targets": [{"id": "fixture", "source": "PM.Local.target",
                             "canonical": "PM.Canonical.target", "signature": signature,
                             "signature_sha256": __import__("hashlib").sha256(
                                 signature.encode("utf-8")).hexdigest()}],
            }
            transplant = root / "candidate.lean"
            with patch("remap_aristotle_interface.batch_plan", return_value=plan):
                report = run_remap(root, "fixture", archive, transplant=transplant)
            self.assertEqual(report["status"], "transplantable-interface-only")
            self.assertTrue(report["transplant"]["requires_independent_remote_kernel_check"])
            self.assertIn("not a canonical integration", transplant.read_text(encoding="utf-8"))

    def test_scanner_preserves_exact_header_hashes(self):
        source = """namespace A.B
-- comment
theorem theorem_name {α : Type} (x : α) : x = x := by rfl
end A.B
"""
        declarations = scan_declarations(source, "fixture.lean")
        self.assertEqual(declarations[0]["qualified"], "A.B.theorem_name")
        self.assertEqual(declarations[0]["signature"],
                         "theorem theorem_name {α : Type} (x : α) : x = x\n")
        self.assertEqual(len(declarations[0]["signature_sha256"]), 64)

    def test_scanner_keeps_a_dotted_declaration_in_its_namespace(self):
        declarations = scan_declarations("""namespace PM
theorem Defn.sound : True := by trivial
end PM
""", "fixture.lean")
        self.assertEqual(declarations[0]["qualified"], "PM.Defn.sound")

    def test_q300_terminal_archive_is_rejected_without_treating_insertion_as_missing(self):
        archive = ROOT / "aristotle/results/Q300-final.tar.gz"
        report = run_remap(ROOT, "Q300", archive)
        self.assertEqual(report["status"], "blocked")
        self.assertEqual(report["canonical_declarations"][0]["role"], "target-insertion")
        if not archive.is_file():
            self.assertFalse(report["archive"]["present"])
            self.assertTrue(report["reasons"])
            return
        self.assertEqual(report["archive"]["sha256"],
                         "15b9639c4cbff8d2e2066999f33c0fd06b572cc84fdbaa0eac2f03ef269ba065")
        self.assertNotIn("missing canonical declaration", "\n".join(report["reasons"]))
        self.assertIn("forbidden Classical", "\n".join(report["reasons"]))
        self.assertIn("Q300 forbids archive-local declarations", "\n".join(report["reasons"]))

    def test_q259_terminal_archive_is_rejected_without_missing_target_blocker(self):
        archive = ROOT / "aristotle/results/Q259-final.tar.gz"
        report = run_remap(ROOT, "Q259", archive)
        self.assertEqual(report["status"], "blocked")
        self.assertTrue(all(record["role"] == "target-insertion"
                            for record in report["canonical_declarations"]))
        if not archive.is_file():
            self.assertFalse(report["archive"]["present"])
            self.assertTrue(report["reasons"])
            return
        self.assertEqual(report["archive"]["sha256"],
                         "71fca398baa073201f5975ff632c75de1d8659b504de0c858ae90c2b7d0e0b6e")
        reasons = "\n".join(report["reasons"])
        self.assertNotIn("missing canonical declaration", reasons)
        self.assertIn("forbidden Classical", reasons)
        self.assertIn("Q259 forbids archive-local declarations", reasons)

    def test_bad_mapping_schema_is_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            mapping = Path(directory) / "mapping.json"
            mapping.write_text(json.dumps({"declarations": [{"source": "A"}]}), encoding="utf-8")
            report = run_remap(ROOT, "Q228", mapping_path=mapping)
            self.assertEqual(report["status"], "blocked")
            self.assertTrue(any(reason.startswith("terminal archive unavailable")
                                for reason in report["reasons"]))


if __name__ == "__main__":
    unittest.main()
