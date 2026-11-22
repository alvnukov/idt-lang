"""Run conditional transfer and spectrum controls against their countermodels."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class SlotTests(unittest.TestCase):
    def test_transfer_and_matter_fixtures(self) -> None:
        for filename in ("probe_signed_slot_transfers.py", "probe_five_slot_charge.py"):
            with self.subTest(probe=filename):
                result = subprocess.run(
                    [sys.executable, "-O", str(ROOT / "scripts" / filename)],
                    cwd=ROOT.parent,
                    text=True,
                    capture_output=True,
                    timeout=30,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
