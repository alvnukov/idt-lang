"""Replay the stock selection, tagged-event experiments, and recurrence controls."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class RoutedEventTests(unittest.TestCase):
    def test_replay(self) -> None:
        for module in (
            "raw_gate_reconstruction",
            "separable_event_stock",
            "port_stock_origin",
            "coset_address_transport",
            "spectator_stock_bridge",
            "cancellation_event_router",
            "ranked_event_routing",
            "routed_pair_bell",
            "integer_phase_orbit",
            "paired_rail_encoding",
            "native_recurrence_witness",
        ):
            with self.subTest(probe=module):
                run = subprocess.run(
                    [
                        sys.executable,
                        "-O",
                        str(ROOT / "scripts" / f"probe_{module}.py"),
                    ],
                    cwd=ROOT.parent,
                    capture_output=True,
                    text=True,
                    timeout=90,
                    check=False,
                )
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
