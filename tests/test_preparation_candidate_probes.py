"""Keep exploratory preparations replayable without promoting them to claims."""

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class PreparationCandidateTests(unittest.TestCase):
    def test_candidate_history(self) -> None:
        for name in (
            "probe_phase_return_walk.py",
            "probe_hemisphere_candidate.py",
            "probe_mid_edge_majority_walk.py",
            "probe_cyclic_ballot_preparation.py",
        ):
            with self.subTest(probe=name):
                result = subprocess.run(
                    [sys.executable, "-O", str(ROOT / "scripts" / name)],
                    cwd=ROOT.parent,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
