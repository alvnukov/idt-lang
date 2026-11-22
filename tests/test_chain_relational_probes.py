"""Replay both conditional mechanisms; an alternative is not a rejected theory."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class ChainRelationalProbeTests(unittest.TestCase):
    def replay(self, name: str) -> None:
        result = subprocess.run(
            [sys.executable, "-O", str(ROOT / "scripts" / name)],
            cwd=ROOT.parent,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_all_reference_chain_and_local_densities(self) -> None:
        self.replay("probe_chain_relational_charge.py")

    def test_prepared_references_and_weight_tradeoff(self) -> None:
        self.replay("probe_reference_weight_tradeoff.py")

    def test_closed_middle_order_and_readout_symmetry(self) -> None:
        self.replay("probe_middle_order_echo.py")

    def test_native_path_record_and_disturbance(self) -> None:
        self.replay("probe_native_path_record.py")
