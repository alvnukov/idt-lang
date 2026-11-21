"""Replay shutter controls as model comparisons, not claims of physical confirmation."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class ShutterCandidateProbeTests(unittest.TestCase):
    def replay(self, filename: str) -> None:
        result = subprocess.run(
            [sys.executable, "-O", str(ROOT / "scripts" / filename)],
            cwd=ROOT.parent,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_native_shutters_and_independent_wave_control(self) -> None:
        self.replay("probe_two_arm_shutters.py")

    def test_three_paths_and_repeated_arm_holdout(self) -> None:
        self.replay("probe_cyclic_shutter_holdout.py")

    def test_hidden_arm_word_certificates(self) -> None:
        self.replay("probe_hidden_arm_certificates.py")

    def test_native_eight_label_phase_plate(self) -> None:
        self.replay("probe_eight_label_interferometer.py")
