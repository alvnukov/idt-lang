import unittest

from scripts import probe_staggered_raw_charge as probe


class StaggeredRawChargeTests(unittest.TestCase):
    def test_every_frozen_triple_has_the_same_three_weight_types(self):
        for x, y in ((1, 0), (0, 1), (3, -2)):
            for edge in (0, 1):
                w = probe.local_weights(edge, x, y)
                for tri in probe.TRIPLES_BY_PHASE[edge]:
                    self.assertEqual(sorted(w[i] for i in tri), sorted((x, y, -x - y)))

    def test_single_event_current_matches_every_cut_of_every_raw_link(self):
        report = probe.current_check()
        self.assertEqual(report["links_by_phase"], (4, 32))
        self.assertEqual(report["oriented_events"], 72)
        self.assertEqual(report["cut_violations"], 0)
        self.assertEqual(report["occupancy_hop_violations"], 0)

    def test_charge_values_on_every_clean_word_both_phases(self):
        self.assertEqual(probe.clean_check(6), (1458, 0))

    def test_separation_trace_is_composed_of_literal_enabled_global_events(self):
        for n in range(2, 11):
            cert = probe.four_states(n)
            self.assertEqual(cert["path"][0], cert["V"])
            self.assertEqual(cert["path"][-1], cert["D"])
            for x, y, mask in zip(cert["path"][:-1], cert["path"][1:], cert["moves"]):
                self.assertEqual(x ^ y, mask)
                self.assertIn(x & mask, (0, mask))
                self.assertIn(mask, probe.global_moves(n, 1))
            self.assertEqual(len(cert["path"]), 2 + 2 * (n - 2))
            self.assertEqual(
                [probe.charge(cert[k], n, 1) for k in ("V", "P", "H", "D")],
                [0, 1, -1, 0],
            )

    def test_arbitrary_local_tables_cancel_until_first_joint_support(self):
        for n in range(2, 9):
            cert = probe.four_states(n)
            sep = 2 * (n - 1) - 1
            self.assertEqual(
                probe.table_obstruction(cert, sep - 1)["uncancelled_intervals"], 0
            )
            self.assertGreater(
                probe.table_obstruction(cert, sep)["uncancelled_intervals"], 0
            )

    def test_nonlocal_positive_and_positive_background_controls(self):
        row = probe.report(7)
        self.assertEqual(row["truncated_nonlocal_VPHD"], [0, 1, 0, 0])
        self.assertEqual(row["positive_occupancy_VPHD"], [7, 8, 6, 7])
        self.assertEqual(row["baseline"], 7)

    def test_repeated_emitters_force_arbitrarily_large_background_for_fixed_range(self):
        for m, k in ((1, 3), (2, 4), (4, 3)):
            cert = probe.repeated_four_states(m, k)
            n = 2 * m * k
            self.assertEqual(cert["n"], n)
            self.assertEqual(
                [probe.charge(cert[s], n, 1) for s in ("V", "P", "H", "D")],
                [0, k, -k, 0],
            )
            self.assertEqual(cert["path"][-1], cert["D"])
            for x, y, mask in zip(cert["path"][:-1], cert["path"][1:], cert["moves"]):
                self.assertEqual(x ^ y, mask)
                self.assertIn(x & mask, (0, mask))
                self.assertIn(mask, probe.global_moves(n, 1))
            self.assertEqual(
                probe.table_obstruction(cert, 2 * m - 2)["uncancelled_intervals"], 0
            )
            self.assertGreater(
                probe.table_obstruction(cert, 2 * m - 1)["uncancelled_intervals"], 0
            )
