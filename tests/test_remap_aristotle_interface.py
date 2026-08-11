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
    def test_q228_plan_is_exact_and_non_promotional(self):
        plan = batch_plan(ROOT, "Q228")
        self.assertEqual([target["id"] for target in plan["targets"]], [
            "PM1:✱4·11", "PM1:✱4·14", "PM1:✱4·15", "PM1:✱4·2",
        ])
        self.assertTrue(plan["canonical_integration_forbidden"])
        self.assertTrue(all(len(target["signature_sha256"]) == 64 for target in plan["targets"]))

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
