import json
import subprocess
import sys
import unittest
from fractions import Fraction as F
from itertools import product
from pathlib import Path

from scripts import probe_packet_setting_dependence as probe
from scripts.probe_raw_packet_phase_quotients import (
    ACTIVE,
    BOB,
    SETTINGS,
    bob_axis_signs,
)
from scripts.probe_two_source_phase_network import AXIS_PAIRS, functional


class PacketSettingDependence(unittest.TestCase):
    def test_both_native_instruments_decode_a_setting_fixed_class_map(self) -> None:
        report = probe.run_probe()
        self.assertEqual(report.raw_addresses, 256)
        self.assertEqual(report.strategy_multiplicities, {8: 32})
        self.assertEqual(report.active_win_counts_per_address, (9,))
        self.assertEqual(report.active_winning_address_counts, (192,))
        self.assertEqual(report.independent_setting_ceiling, 6)
        self.assertEqual(set(report.instruments), {"H", "D"})
        for instrument in report.instruments.values():
            self.assertEqual(instrument.class_rails, 64)
            self.assertEqual(instrument.exact_forward_records, 256)
            self.assertEqual(instrument.classes_per_bob_outcome, (16,) * 4)
            self.assertEqual(instrument.addresses_per_bob_outcome, (64,) * 4)

    def test_all_eighteen_outcome_tables_are_exact_and_ab_bc_marginals_are_uniform(
        self,
    ) -> None:
        readers = probe.make_packet_readers()
        p = F(7, 8)
        rows = probe.make_records(readers, probe.make_sampling(readers, p))
        self.assertEqual(set(rows), set(SETTINGS))
        self.assertEqual(functional(rows), 9)
        self.assertEqual(len(ACTIVE), 12)
        for (x, z), row in rows.items():
            self.assertEqual(sum(row.values()), 1)
            self.assertEqual(len(row), 16)
            ab: dict[tuple[int, int, int], F] = {}
            bc: dict[tuple[int, int, int], F] = {}
            for (a, b1, b2, c), q in row.items():
                if (x, z) in ACTIVE:
                    signed = ACTIVE[x, z] * a * bob_axis_signs((b1, b2))[x] * c
                    self.assertEqual(q, (p if signed == 1 else 1 - p) / 8)
                else:
                    self.assertEqual(q, F(1, 16))
                ab[a, b1, b2] = ab.get((a, b1, b2), F(0)) + q
                bc[b1, b2, c] = bc.get((b1, b2, c), F(0)) + q
            self.assertEqual(set(ab), {(a, *b) for a, b in product((-1, 1), BOB)})
            self.assertEqual(set(bc), {(*b, c) for b, c in product(BOB, (-1, 1))})
            self.assertEqual(set(ab.values()) | set(bc.values()), {F(1, 8)})

    def test_source_independence_given_settings_does_not_imply_side_locality(
        self,
    ) -> None:
        readers = probe.make_packet_readers()
        rows = probe.make_sampling(readers, F(7, 8))
        address_prior = dict.fromkeys(readers.strategies, F(0))
        for row in rows.values():
            self.assertEqual(sum(row.values()), 1)
            self.assertEqual(len(row), 256)
            right = [sum(row[i, j] for i in range(16)) for j in range(16)]
            for (i, j), q in row.items():
                self.assertEqual(q, right[j] / 16)
                address_prior[i, j] += q / 18
        self.assertEqual(set(address_prior.values()), {F(1, 256)})
        witnesses = []
        for plaque, (x0, x1) in enumerate(AXIS_PAIRS):
            z = 2 * plaque
            for point in readers.strategies:
                det = (
                    rows[x0, z][point] * rows[x1, z + 1][point]
                    - rows[x1, z][point] * rows[x0, z + 1][point]
                )
                witnesses.append(abs(det))
        self.assertEqual(len(witnesses), 768)
        self.assertEqual(set(witnesses), {F(7, 1536) * (F(7, 1536) - F(1, 512))})

    def test_sampling_is_parametric_and_output_readout_never_repairs_missing_mass(
        self,
    ) -> None:
        readers = probe.make_packet_readers()
        p = F(4, 5)
        rows = probe.make_sampling(readers, p)
        self.assertEqual(functional(probe.make_records(readers, rows)), F(36, 5))
        setting = next(iter(ACTIVE))
        point = next(iter(readers.strategies))
        raw_weight = rows[setting][point]
        rows[setting][point] = F(0)
        with self.assertRaisesRegex(ValueError, "non-unit mass"):
            probe.make_records(readers, rows)
        rows[setting][point] = raw_weight
        del rows[setting][point]
        with self.assertRaisesRegex(ValueError, "raw address is missing"):
            probe.make_records(readers, rows)

    def test_endpoint_controls_and_information_cost_labels(self) -> None:
        null, witness, full = probe.run_probe().samples
        for sample, p, score, determinant in (
            (null, "3/4", "6", "0"),
            (witness, "7/8", "9", "7/589824"),
            (full, "1", "12", "1/36864"),
        ):
            self.assertEqual(sample.win_probability, p)
            self.assertEqual(sample.score, score)
            self.assertEqual(sample.setting_mass, ("1",))
            self.assertEqual(sample.complete_settings, 18)
            self.assertTrue(sample.no_postselection)
            self.assertTrue(sample.observable_nonsignaling)
            self.assertTrue(sample.conditionally_independent_sources)
            self.assertTrue(sample.uniform_raw_address_prior_active_and_all)
            self.assertEqual(sample.equality_plaquette_checks, 768)
            self.assertEqual(sample.equality_abs_determinant, determinant)
            self.assertEqual(sample.side_local_factorization, sample is null)
            self.assertAlmostEqual(
                sample.all_settings_information_bits_approx,
                2 * sample.active_information_bits_approx / 3,
                places=14,
            )
        self.assertEqual(null.active_information_bits_approx, 0)
        self.assertAlmostEqual(
            witness.active_information_bits_approx, 0.06959336866939204, places=14
        )
        self.assertAlmostEqual(
            full.active_information_bits_approx, 0.41503749927884376, places=14
        )
        with self.assertRaises(ValueError):
            probe.make_sampling(probe.make_packet_readers(), F(1, 2))
        with self.assertRaises(ValueError):
            probe.make_sampling(probe.make_packet_readers(), F(9, 8))

    def test_cli_is_json_and_survives_python_optimized_mode(self) -> None:
        completed = subprocess.run(
            [
                sys.executable,
                "-B",
                "-E",
                "-O",
                "-m",
                "scripts.probe_packet_setting_dependence",
            ],
            cwd=Path(__file__).resolve().parents[1],
            check=True,
            capture_output=True,
            text=True,
            timeout=20,
        )
        payload = json.loads(completed.stdout)
        self.assertEqual(payload["samples"][1]["score"], "9")
        self.assertEqual(payload["samples"][1]["equality_plaquette_checks"], 768)
        self.assertEqual(completed.stderr, "")


if __name__ == "__main__":
    unittest.main()
