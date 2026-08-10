import io
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_aristotle_archive as archive_audit


def write_archive(path: Path, members: dict[str, str]) -> None:
    with tarfile.open(path, "w:gz") as archive:
        for name, source in members.items():
            raw = source.encode("utf-8")
            info = tarfile.TarInfo(name)
            info.size = len(raw)
            archive.addfile(info, io.BytesIO(raw))


class AristotleArchiveAuditTests(unittest.TestCase):
    def test_clean_archive_reports_immutable_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Q-test-final.tar.gz"
            write_archive(path, {"RequestProject/Main.lean": "theorem ok : True := by trivial\n"})
            report = archive_audit.audit_archive(path)
            self.assertEqual(len(report["archive_sha256"]), 64)
            self.assertEqual(report["lean_files"][0]["path"], "RequestProject/Main.lean")
            self.assertEqual(report["forbidden_constructs"], [])
            self.assertEqual(report["scoped_exceptions"], [])

    def test_placeholder_and_new_axiom_are_rejected(self):
        for source in ("theorem bad : True := by sorry\n", "axiom bad : True\n"):
            with self.subTest(source=source), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "bad.tar.gz"
                write_archive(path, {"Bad.lean": source})
                with self.assertRaises(archive_audit.ArchiveAuditError):
                    archive_audit.audit_archive(path)

    def test_path_traversal_and_links_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "traversal.tar.gz"
            write_archive(path, {"../Escape.lean": "theorem ok : True := by trivial\n"})
            with self.assertRaises(archive_audit.ArchiveAuditError):
                archive_audit.audit_archive(path)
            link_path = Path(directory) / "link.tar.gz"
            with tarfile.open(link_path, "w:gz") as archive:
                info = tarfile.TarInfo("Link.lean")
                info.type = tarfile.SYMTYPE
                info.linkname = "/etc/passwd"
                archive.addfile(info)
            with self.assertRaises(archive_audit.ArchiveAuditError):
                archive_audit.audit_archive(link_path)

    def test_classical_is_only_tolerated_and_reported_in_generated_harness(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "harness.tar.gz"
            write_archive(path, {
                "Result/RequestProject/Main.lean": "open scoped Classical\n",
                "Result/Target.lean": "theorem ok : True := by trivial\n",
            })
            report = archive_audit.audit_archive(path)
            self.assertEqual(report["scoped_exceptions"][0]["scope"],
                             "generated-compilation-harness-only")
            bad_path = Path(directory) / "target-classical.tar.gz"
            write_archive(bad_path, {"Result/Target.lean": "open scoped Classical\n"})
            with self.assertRaises(archive_audit.ArchiveAuditError):
                archive_audit.audit_archive(bad_path)


if __name__ == "__main__":
    unittest.main()
