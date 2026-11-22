"""Replay lattice transport, shared clocks/cones, chirality and phase frames."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class TransportTests(unittest.TestCase):
    def test_replay(self) -> None:
        for module in (
            "integer_transport_walk",
            "weyl_walk_chirality",
            "shared_cone_origin",
            "universal_clock_rescaling",
            "phase_comparison_links",
            "link_phase_harmonics",
        ):
            with self.subTest(probe=module):
                run = subprocess.run(
                    [sys.executable, "-B", "-O", "-m", f"scripts.probe_{module}"],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    timeout=30,
                    check=False,
                )
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
