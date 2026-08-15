import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_dependencies as dependencies


class TransparentWrapperSelfReferenceTests(unittest.TestCase):
    def test_wrapper_name_does_not_turn_audited_declaration_into_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "metadata").mkdir()
            (root / "metadata/dependency_aliases.json").write_text(
                json.dumps({"lean_realizations": {}}), encoding="utf-8"
            )
            (root / "Fixture.lean").write_text(
                """namespace PM
theorem audited : True := by
  exact PM.fixture_wrapper

theorem fixture_wrapper : True := by
  exact True.intro
end PM
""",
                encoding="utf-8",
            )
            item = {
                "id": "PM1:TEST",
                "kind": "derived-proposition",
                "lean_path": "Fixture.lean",
                "declaration": "PM.audited",
            }
            declarations = {"PM.audited": item["id"]}
            wrappers = {
                "PM.fixture_wrapper": ("Fixture.lean", "PM.fixture_wrapper")
            }

            with patch.object(
                dependencies, "TRANSPARENT_DEPENDENCY_WRAPPERS", wrappers
            ):
                actual = dependencies.extract_lean_dependencies(
                    item, declarations, root
                )

            self.assertEqual(actual, [])


if __name__ == "__main__":
    unittest.main()
