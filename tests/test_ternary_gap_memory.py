import unittest
from collections import Counter
from itertools import product
from math import comb

from scripts import probe_ternary_gap_memory as gap
from scripts import probe_undriven_ternary_ring as ring


class TernaryGapMemoryTests(unittest.TestCase):
    def test_gap_orientation_and_unlabelled_signature(self):
        self.assertEqual(gap.reduce_word("TbabTaaa"), ((0, 2), (4, 0)))
        self.assertEqual(gap.reduce_word("TbaaTbaa"), ((0, 1), (4, 1)))
        # An empty gap, a wraparound gap, and reversal of an even gap.
        self.assertEqual(gap.reduce_word("bTTaa"), ((1, 0), (2, 1)))
        word = "TbbabTTbabTbaa"
        key = gap.memory(gap.reduce_word(word))
        for orientation in (word, word[::-1]):
            for i in range(len(word)):
                self.assertEqual(gap.memory(gap.reduce_word(orientation[i:] + orientation[:i])), key)

    def test_boundary_moves_and_multiplicities_against_all_raw_edges(self):
        for n in range(3, 8):
            counts = Counter()
            targets = {}
            edges = ring.ring_edges(n)
            for raw in map("".join, product("Tab", repeat=n)):
                if "T" not in raw:
                    continue
                key = gap.reduce_word(raw)
                sites = tuple(p for p, _ in key)
                for L, (_, h) in zip(gap.lengths(n, sites), key):
                    self.assertGreaterEqual(L, max(0, 2 * abs(h) - 1))
                counts[key] += 1
                reachable = targets.setdefault(key, set())
                for _, other in ring.active_moves(raw, edges):
                    nxt = gap.reduce_word(other)
                    if nxt != key:
                        reachable.add(nxt)
                    self.assertEqual(gap.memory(nxt), gap.memory(key))
            for key in counts:
                self.assertEqual(gap.multiplicity(n, key), counts[key])
                self.assertEqual(set(gap.hops(n, key)), targets[key])

    def test_literal_and_reduced_component_partitions(self):
        for n in range(4, 9):
            for t in range(1, 4):
                with self.subTest(n=n, t=t):
                    row = gap.census(n, t)
                    self.assertEqual(row["raw_states"], comb(n, t) * 2 ** (n - t))
                    self.assertLessEqual(row["components"], row["reduced_states"])
                    self.assertTrue(row["exact_partition_match"])

    def test_matched_preparations_disagree_on_adjacency(self):
        r, s = gap.matched_pair()
        self.assertEqual(r["tag_sites"], s["tag_sites"])
        self.assertEqual(r["initial_b_count"], s["initial_b_count"])
        self.assertEqual(r["initial_even_ring_K"], s["initial_even_ring_K"])
        for row, expected in ((r, (100, 48, 3)), (s, (92, 0, None))):
            self.assertEqual((row["orbit_size"], row["adjacent_states"],
                              row["min_changing_contacts"]), expected)
        self.assertEqual(r["absolute_gap_memory"], [0, 2])
        self.assertEqual(s["absolute_gap_memory"], [1, 1])

    def test_same_fiber_is_not_a_transition_rate_model(self):
        row = gap.rate_control()
        self.assertTrue(row["same_reduced_source"])
        self.assertEqual(row["offered_edges_to_same_target"], [1, 0])


if __name__ == "__main__":
    unittest.main()
