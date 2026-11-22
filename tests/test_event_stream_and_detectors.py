"""Replay independent temporal, memory, empirical and shutter controls."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class EventStreamTests(unittest.TestCase):
    def test_replay(self) -> None:
        for module in (
            "rotor_event_stream",
            "trigger_alignment",
            "interferometer_benchmark",
            "native_absorber_memory",
            "transparency_shutter",
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
