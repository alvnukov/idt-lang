"""Replay the supplied sample, scalar-composition, and two-mark-shell controls."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class PhaseColorTests(unittest.TestCase):
    def test_phase_controls(self) -> None:
        for filename in (
            "probe_positive_square_readout.py",
            "probe_composed_phase_colors.py",
            "probe_two_mark_shell.py",
        ):
            with self.subTest(probe=filename):
                run = subprocess.run(
                    [sys.executable, "-O", str(ROOT / "scripts" / filename)],
                    cwd=ROOT.parent,
                    capture_output=True,
                    text=True,
                    timeout=30,
                    check=False,
                )
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
