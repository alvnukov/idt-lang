"""Keep literal and memory-bearing exchange candidates in the finite history."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class TwoParticleCapacityTests(unittest.TestCase):
    def test_iid_and_correlated_capacity_controls(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                "-O",
                str(ROOT / "scripts" / "probe_two_particle_capacity.py"),
            ],
            cwd=ROOT.parent,
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
