"""Regression checks for the raw three-mark sector and its scheduler boundary."""

import unittest

from scripts import probe_three_link_translation as probe


class ThreeLinkTranslationTest(unittest.TestCase):
    def test_raw_view_and_readouts(self):
        g = probe.cycle_square(11)
        mask = probe.packet(g, 4)
        self.assertEqual(
            {e for e, bit in g.edge_bits.items() if mask & bit},
            {(2, 4), (3, 4), (3, 5)},
        )
        self.assertEqual(probe.support_core(g, mask), ({2, 3, 4, 5}, {3, 4}))
        shell = probe.RawShell(g)
        self.assertEqual(shell.view(mask, 4), ((0, 1, 1, 0), 3))
        self.assertEqual(
            shell.offers(mask, 16), {3: probe.packet(g, 3), 4: probe.packet(g, 5)}
        )
        with self.assertRaises(ValueError):
            probe.cycle_square(4)

    def test_orbit_and_finite_separation(self):
        for n in (5, 6, 7, 8, 11, 16, 31):
            with self.subTest(n=n):
                row = probe.check_sector(n)
                self.assertEqual(row.raw_states, n)
                self.assertEqual(row.directed_events, 2 * n)
                self.assertEqual(row.event_diameter, n // 2)
                self.assertEqual(row.core_separations, tuple(range((n // 2) // 2 + 1)))
                self.assertEqual(row.oriented_periods, (n, n))
                self.assertTrue(row.reflection_swaps_offers)

    def test_nonundo_uses_last_event_only(self):
        # The law neither accepts nor consults positions, labels or a direction.
        self.assertEqual(probe.nonundo({9: 41, 3: 72}, 3), (9, 41))
        with self.assertRaises(ValueError):
            probe.nonundo({4: 1}, 4)
        with self.assertRaises(ValueError):
            probe.nonundo({4: 1, 6: 2}, 3)
        with self.assertRaises(ValueError):
            probe.nonundo({4: 1, 6: 2, 9: 3}, 4)

    def test_corpus_alias_is_sector_only(self):
        for n in (5, 11):
            matching, idle = probe.census(n)
            self.assertEqual(matching, tuple(f for f in range(256) if f & 16))
            self.assertEqual(idle, tuple(f for f in range(256) if not f & 16))

    def test_contact_separates_single_packet_aliases(self):
        sample = probe.pair_control()
        self.assertEqual(sample["raw_states"], 72)
        self.assertEqual(sample["outdegree_counts"], {2: 16, 4: 56})
        self.assertEqual(sample["contact_offers_16"], [4, 15])
        self.assertEqual(sample["contact_offers_18"], [0, 3, 4, 15])
        self.assertEqual(sample["isolated_aliases_remaining_on_pair_rows"], 64)


if __name__ == "__main__":
    unittest.main()
