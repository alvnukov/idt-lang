"""Replay distinct single-record and independent-source controls."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class ParityAndCompositionTests(unittest.TestCase):
    def test_record_controls(self) -> None:
        for filename in (
            "probe_parity_capacity.py",
            "probe_independent_edge_composition.py",
        ):
            with self.subTest(probe=filename):
                result = subprocess.run(
                    [sys.executable, "-O", str(ROOT / "scripts" / filename)],
                    cwd=ROOT.parent,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
