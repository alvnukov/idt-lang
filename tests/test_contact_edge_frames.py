"""Regression checks for the finite shared-edge contact probe."""

import json
import subprocess
import sys
import unittest
from functools import cache
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
MODULE = "scripts.probe_contact_edge_frames"


@cache
def _run_probe(*options: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-B", *options, "-m", MODULE],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        timeout=10,
    )


class ContactEdgeFrameTests(unittest.TestCase):
    def _report(self) -> dict[str, object]:
        result = _run_probe()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, "")
        return cast(dict[str, object], json.loads(result.stdout))

    def test_overlapping_stars_recheck_guards_and_distinguish_snapshot_union(
        self,
    ) -> None:
        overlaps = cast(
            dict[str, list[dict[str, int]]], self._report()["overlapping_stars"]
        )
        self.assertEqual(set(overlaps), {"common", "opposite"})
        for frame, rows in overlaps.items():
            with self.subTest(frame=frame):
                self.assertEqual([row["shared_edges"] for row in rows], [0, 1, 2, 3, 4])
                self.assertEqual(
                    [row["states"] for row in rows], [256, 128, 64, 32, 16]
                )
                self.assertEqual(
                    [row["jointly_legal"] for row in rows], [36, 18, 10, 6, 6]
                )
                self.assertEqual(
                    [row["both_serial_legal"] for row in rows], [36, 0, 8, 0, 6]
                )
                self.assertEqual(
                    [row["exactly_one_serial_legal"] for row in rows], [0] * 5
                )
                self.assertEqual(
                    [row["serial_output_disagreements"] for row in rows], [0] * 5
                )
                self.assertEqual(
                    [row["serial_output_not_preguarded_xor"] for row in rows], [0] * 5
                )
                self.assertEqual(
                    [row["snapshot_not_preguarded_xor"] for row in rows],
                    [0, 18, 10, 6, 6],
                )
                self.assertEqual(
                    [row["snapshot_not_both_legal_serials"] for row in rows],
                    [0, 0, 8, 0, 6],
                )
                self.assertEqual([row["nonreversible_moves"] for row in rows], [0] * 5)

    def test_doubled_triangle_separates_the_frames(self) -> None:
        triangle = cast(
            dict[str, dict[str, object]], self._report()["doubled_triangle"]
        )
        common = triangle["common"]
        opposite = triangle["opposite"]
        for frame in (common, opposite):
            self.assertEqual(frame["states"], 64)
            self.assertEqual(frame["nonreversible_moves"], 0)
        self.assertEqual(common["all_live_starts"], 8)
        self.assertEqual(common["always_preserving_starts"], 8)
        self.assertEqual(common["always_only_fired_live_starts"], [])
        self.assertEqual(opposite["all_live_starts"], 10)
        self.assertEqual(opposite["always_preserving_starts"], 8)
        self.assertEqual(
            opposite["always_only_fired_live_starts"], ["001100", "110011"]
        )
        self.assertEqual(
            opposite["witness_after_a"], {"word": "110011", "populations": [2, 4, 0]}
        )

    def test_k5_choices_can_change_the_number_of_offers_without_losing_reversibility(
        self,
    ) -> None:
        k5 = cast(dict[str, object], self._report()["common_k5_half_filling"])
        self.assertEqual(k5["states"], 252)
        self.assertEqual(k5["offer_count_choice_sensitive_starts"], 120)
        self.assertEqual(k5["nonreversible_moves"], 0)
        self.assertEqual(k5["half_filling_violations"], 0)
        self.assertEqual(
            k5["choice_witness"],
            {
                "word": "0111110000",
                "offers_after": {
                    "B": ["B", "E"],
                    "C": ["A", "C", "E"],
                    "D": ["A", "D", "E"],
                },
            },
        )

    def test_all_enabled_k5_starts_are_centers_of_nonbacktracking_dead_ends(
        self,
    ) -> None:
        k5 = cast(dict[str, object], self._report()["common_k5_half_filling"])
        self.assertEqual(k5["fully_enabled_starts"], 12)
        self.assertEqual(k5["fully_enabled_first_fires"], 60)
        self.assertEqual(k5["first_fires_with_nonbacktracking_continuation"], 0)

    def test_optimized_and_ordinary_reports_match(self) -> None:
        normal = _run_probe()
        optimized = _run_probe("-O")
        self.assertEqual(normal.returncode, 0, normal.stderr)
        self.assertEqual(optimized.returncode, 0, optimized.stderr)
        self.assertEqual(optimized.stderr, "")
        self.assertEqual(normal.stdout, optimized.stdout)


if __name__ == "__main__":
    unittest.main()
