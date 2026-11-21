"""Replay detector capacity and loss controls on every archived cube channel."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class CubeDetectorTests(unittest.TestCase):
    def test_candidates(self) -> None:
        for filename in (
            "probe_endpoint_tetra_detector.py",
            "probe_erased_bit_readouts.py",
        ):
            with self.subTest(probe=filename):
                run = subprocess.run(
                    [sys.executable, "-O", str(ROOT / "scripts" / filename)],
                    cwd=ROOT.parent,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
