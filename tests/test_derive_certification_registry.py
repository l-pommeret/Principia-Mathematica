"""The stored certification tier must be reproducible, never editable."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from io import StringIO
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import derive_certification_registry as registry  # noqa: E402


class CertificationRegistryCheckTests(unittest.TestCase):
    def test_check_rejects_a_falsified_item_tier(self) -> None:
        expected = {
            "kind": "pm-derived-certification-registry",
            "items": [
                {
                    "id": "PM1:✱2·01",
                    "certification_tier": "awaiting-ci",
                }
            ],
        }
        falsified = json.loads(registry.render(expected))
        falsified["items"][0]["certification_tier"] = "kernel-checked"

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "certification_registry.json"
            path.write_text(registry.render(falsified), encoding="utf-8")
            stderr = StringIO()
            with patch.object(registry, "derive_registry", return_value=expected):
                with redirect_stderr(stderr):
                    result = registry.main(
                        ["--check", "--registry", str(path)]
                    )

        self.assertEqual(result, 1)
        self.assertIn("certification registry drift", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
