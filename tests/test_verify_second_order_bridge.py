"""The ramified ✱9 bridge has a genuine kernel-checked 1→2 instance."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class SecondOrderBridgeTests(unittest.TestCase):
    def test_ramified_first_to_second_order_bridge(self) -> None:
        gate = subprocess.run(
            [sys.executable, str(ROOT / "scripts/verify_second_order_bridge.py")],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        self.assertEqual(gate.returncode, 0, gate.stderr)
        self.assertIn("Ramified 1→2 Star 9 bridge checks passed", gate.stdout)

        witness = """import Principia.Deduction.Star9Derived

namespace PM.RamifiedSyntax

theorem test_first_to_second_order_bridge
    (universal : signature.Universal (.proposition 1) 1)
    (body : Formula signature real [.proposition 1] 1)
    (line1 : Star9Assertion
      (body.weakenReal.instantiate
        (.real (.zero : Var (.proposition 1 :: real) (.proposition 1))))) :
    Derivation (.assertion
      (show Formula signature real [] 2 from .always universal body)) := by
  exact star_9_13 universal body line1

end PM.RamifiedSyntax
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "SecondOrderBridge.lean"
            source.write_text(witness, encoding="utf-8")
            checked = subprocess.run(
                ["lake", "env", "lean", str(source)],
                cwd=ROOT, capture_output=True, text=True, check=False,
            )
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)


if __name__ == "__main__":
    unittest.main()
