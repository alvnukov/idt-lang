"""Regression controls for the finite raw packet matching fixture."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path
from typing import ClassVar

ROOT = Path(__file__).resolve().parents[1]
PROBE = ROOT / "scripts" / "probe_packet_matching_order.py"


class PacketMatchingOrderTests(unittest.TestCase):
    normal: ClassVar[subprocess.CompletedProcess[str]]
    optimized: ClassVar[subprocess.CompletedProcess[str]]

    @classmethod
    def setUpClass(cls) -> None:
        if not PROBE.is_file():
            return  # Missing feature is reported by each test, not an import error.
        cls.normal = subprocess.run(
            (sys.executable, str(PROBE)), check=False, capture_output=True, text=True
        )
        cls.optimized = subprocess.run(
            (sys.executable, "-O", str(PROBE)),
            check=False,
            capture_output=True,
            text=True,
        )

    def setUp(self) -> None:
        self.assertTrue(PROBE.is_file(), "raw packet matching order probe is missing")
        self.assertEqual(self.normal.returncode, 0, self.normal.stderr)

    def test_matching_controls(self) -> None:
        rows = json.loads(self.normal.stdout)["connected"]
        self.assertEqual([row["m"] for row in rows], [1, 2, 3, 4, 5, 6, 8])
        for row in rows:
            m = row["m"]
            with self.subTest(m=m):
                self.assertEqual(row["ab_order"], m)
                self.assertEqual(row["initial_sites"], 2 * m)
                self.assertEqual(row["words_per_site"], 511)
                self.assertEqual(row["elementary_commutator_central"], m in (1, 2, 4))
                self.assertEqual(row["elementary_commutator_nontrivial"], m > 2)
                self.assertEqual(
                    row["central_nontrivial_elementary_commutator"], m == 4
                )

    def test_raw_h_is_four_bit_complement_exactly_on_two_occupied_bits(self) -> None:
        from scripts.probe_packet_matching_order import eligible, raw_step

        for local in range(16):
            with self.subTest(local=f"{local:04b}"):
                # The contact acts on sites 0 and 2; site 1 must be untouched.
                mask = (local & 3) | ((local >> 2) << 4) | (0b10 << 2)
                legal = local.bit_count() == 2
                self.assertEqual(eligible(mask, (0, 2)), legal)
                if legal:
                    self.assertEqual(raw_step(mask, ((0, 2),)), mask ^ 0b110011)
                else:
                    with self.assertRaisesRegex(
                        ArithmeticError, "exactly one eligible contact"
                    ):
                        raw_step(mask, ((0, 2),))
        with self.assertRaisesRegex(ArithmeticError, "exactly one eligible contact"):
            raw_step(0b00110011, ((0, 1), (2, 3)))

    def test_octagon_echo_contrast_and_rooted_spur(self) -> None:
        octagon = json.loads(self.normal.stdout)["octagon"]
        self.assertEqual(octagon["abab"], [4, 5, 6, 7, 0, 1, 2, 3])
        self.assertEqual(octagon["abba"], list(range(8)))
        self.assertEqual(octagon["abababab"], list(range(8)))
        self.assertEqual(octagon["contrast_dimension"], 4)
        self.assertTrue(octagon["z_negates_contrast"])
        self.assertTrue(octagon["ab_negates_ba_contrast"])
        self.assertTrue(octagon["all_involutive_scalar_character_checks_trivial"])
        spur = octagon["rooted_spur"]
        self.assertEqual(spur["preparations_checked"], 16)
        self.assertEqual(spur["words_per_preparation"], 511)
        self.assertTrue(spur["never_eligible"])
        self.assertEqual(spur["distances"], {"AB": 3, "BA": 3, "ABBA": 1, "ABAB": 5})

    def test_disconnected_minimum_and_other_mechanisms(self) -> None:
        report = json.loads(self.normal.stdout)
        for row in report["disconnected"]["controls"]:
            with self.subTest(components=row["components_m"]):
                self.assertEqual(row["ab_order"], row["expected_lcm"])
                self.assertEqual(
                    row["central_nontrivial_elementary_commutator"],
                    row["ab_order"] == 4,
                )
        self.assertEqual(report["disconnected"]["global_minimum_packet_sites"], 8)
        self.assertFalse(report["disconnected"]["fewer_sites_hit"])
        self.assertTrue(
            report["other_mechanisms"]["m6_central_nontrivial_rotation_cubed"]
        )
        self.assertTrue(
            report["other_mechanisms"]["m8_periodic_contrast_has_ab_negates_ba"]
        )

    def test_optimized_mode_replays_same_checks(self) -> None:
        self.assertEqual(self.optimized.returncode, 0, self.optimized.stderr)
        self.assertEqual(self.optimized.stdout, self.normal.stdout)


if __name__ == "__main__":
    unittest.main()
