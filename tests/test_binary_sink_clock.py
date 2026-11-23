"""Finite controls for an edge-reversal schedule on the supplied cycle."""

import unittest
from math import comb

from scripts import probe_binary_sink_clock as probe
from scripts.probe_binary_cycle_solitons import Cycle


class BinarySinkClockTests(unittest.TestCase):
    def test_only_sinks_fire_and_only_local_bits_change(self):
        n = 6
        arrows = probe.even_sink_arrows(n)
        self.assertEqual(arrows, 0b101010)
        self.assertEqual(probe.ready_sites(n, arrows), (0, 2, 4))
        self.assertEqual(probe.fire(n, arrows, 2, 0), (0b001011, 3))
        self.assertEqual(probe.fire(n, arrows, 0, 0), (0b001011, 0))
        with self.assertRaisesRegex(ValueError, "not a sink"):
            probe.fire(n, arrows, 2, 1)

    def test_check_all_transitions_and_ready_pairs_at_matched_cuts(self):
        for n, cuts, transitions, pairs in ((4, 13, 16, 4), (6, 38, 66, 33), (8, 117, 264, 200)):
            with self.subTest(n=n):
                cycle = Cycle(n)
                row = probe.cut_inventory(n)
                self.assertEqual(row["cuts"], cuts)
                self.assertEqual(row["transitions"], transitions)
                self.assertEqual(row["ready_pairs"], pairs)
                self.assertEqual(row["joining_transitions"], transitions - cuts + 1)
                self.assertEqual(row["payloads_per_cut"], 1 << n)
                self.assertEqual(row["terminal_cuts"], 1)
                self.assertEqual(row["complete_counts"], (2,) * n)
                self.assertEqual(row["complete_arrows"], probe.even_sink_arrows(n))
                expected = []
                for payload in range(1 << n):
                    for phase in (0, 1, 0, 1):
                        payload = cycle.half_step(payload, phase)
                    expected.append(payload)
                self.assertEqual(row["complete_payload_map"], tuple(expected))

    def test_different_cuts_need_not_have_the_same_raw_payload_snapshot(self):
        arrows = probe.even_sink_arrows(4)
        self.assertEqual(probe.fire(4, arrows, 2, 0)[1], 3)
        self.assertEqual(probe.fire(4, arrows, 2, 2)[1], 6)

    def test_unguarded_one_pass_orders_disagree(self):
        self.assertEqual(probe.unguarded_control(), {
            "n": 6,
            "initial_payload": 1,
            "ascending": 63,
            "reverse": 62,
            "even_odd": 35,
        })

    def test_all_small_orientations_preserve_tilt_and_active_class(self):
        for n in range(3, 9):
            with self.subTest(n=n):
                row = probe.orientation_inventory(n)
                self.assertEqual(row["orientations"], 1 << n)
                self.assertEqual(row["deadlocks"], (0, (1 << n) - 1))
                self.assertEqual(row["active_orientations"], (1 << n) - 2)
                balanced = comb(n, n // 2) if n % 2 == 0 else 0
                self.assertEqual(row["periodic_height_slices"], balanced)
                self.assertEqual(row["active_tilted_orientations"], (1 << n) - 2 - balanced)
                self.assertEqual(row["transitions"], n * (1 << (n - 2)))
                self.assertLessEqual(row["max_v_free_events"], n * n // 4)
        self.assertEqual(probe.periodic_height(4, 0b1010), (0, -1, 0, -1))
        self.assertIsNone(probe.periodic_height(4, 0b0001))

    def test_event_gap_bound_is_attained_after_zero_fires(self):
        for n in range(4, 17, 2):
            with self.subTest(n=n):
                witness = probe.sharp_gap(n)
                initial = (1 << (n // 2)) - 1
                arrows, payload = probe.fire(n, witness["before_zero_fire"], 0, 0)
                self.assertEqual(arrows, initial)
                self.assertEqual(witness["after_zero_fire"], initial)
                observed = [0] * n
                for site in witness["zero_free_order"]:
                    self.assertNotEqual(site, 0)
                    arrows, payload = probe.fire(n, arrows, payload, site)
                    observed[site] += 1
                self.assertEqual(tuple(observed), tuple(min(i, n - i) for i in range(n)))
                self.assertEqual(witness["counts"], tuple(observed))
                self.assertEqual(len(witness["zero_free_order"]), n * n // 4)
                self.assertEqual(witness["events"], n * n // 4)
                self.assertEqual(probe.ready_sites(n, arrows), (0,))


if __name__ == "__main__":
    unittest.main()
