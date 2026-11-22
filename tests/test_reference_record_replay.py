"""Replay exact conditional fixtures, not physical confirmation or universal proofs."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class ReferenceRecordReplayTests(unittest.TestCase):
    def replay(self, script_name: str) -> None:
        result = subprocess.run(
            [sys.executable, "-O", str(ROOT / "scripts" / script_name)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=60,
            check=False,
        )
        self.assertEqual(
            result.returncode,
            0,
            msg=f"{script_name} failed:\n{result.stdout}\n{result.stderr}",
        )

    def test_ball_weight_record_order(self) -> None:
        self.replay("probe_ball_weight_record_order.py")

    def test_record_information_visibility(self) -> None:
        self.replay("probe_record_information_visibility.py")

    def test_reference_fanout(self) -> None:
        self.replay("probe_reference_fanout.py")
