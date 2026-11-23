import unittest
from collections import Counter
from itertools import product
from math import comb

from scripts import probe_ternary_active_readout as cs
from scripts import probe_undriven_ternary_ring as p


class UndrivenTernaryRingTests(unittest.TestCase):
    def test_raw_enabled_edges_agree_with_the_native_contact(self):
        edges = p.ring_edges(4)
        for raw in map("".join, product("abT", repeat=4)):
            expected = {}
            for edge in edges:
                state = list(raw)
                cs.step(state, edge)
                if list(raw) != state:
                    expected[edge] = "".join(state)
            self.assertEqual(dict(p.active_moves(raw, edges)), expected)

    def test_h_changes_sign_only_on_hops(self):
        self.assertEqual(p.charge("Tabab"), -2)
        self.assertEqual(p.charge("Tbaab"), 0)
        for n in (3, 4, 5, 6, 7):
            edges = p.ring_edges(n)
            for raw in p.one_token_states(n):
                for _, nxt in p.active_moves(raw, edges):
                    flip = n % 2 == 1 and raw.index("T") != nxt.index("T")
                    self.assertEqual(p.charge(nxt), (-1 if flip else 1) * p.charge(raw))

    def test_dimer_reflection_and_even_or_open_controls(self):
        for n in range(3, 14, 2):
            raw = "T" + "ab" * (n // 2)
            (edge, after), = p.active_moves(raw, p.ring_edges(n))
            self.assertEqual(edge, (0, 1))
            self.assertEqual(list(p.active_moves(after, p.ring_edges(n))), [(edge, raw)])
            self.assertEqual(after, "".join(raw[(1 - i) % n] for i in range(n)))
        self.assertEqual(list(p.active_moves("Tbabab", p.ring_edges(6))), [])
        self.assertEqual(len(list(p.active_moves("Tababa", p.ring_edges(6)))), 2)
        control = p.interface_control()
        self.assertEqual(control["active_bond_each_phase"], [0, 1])
        self.assertEqual(control["alternating_tails"], ["...ab", "ba..."])

    def test_exhaustive_components_and_edge_counts(self):
        for n in range(3, 13):
            with self.subTest(n=n):
                row = p.census(n)
                m = n // 2
                self.assertEqual(row["states"], n * 2 ** (n - 1))
                # Each edge sees 2*2^(n-2) hopping states plus
                # 2*(n-2)*2^(n-3) ordinary-recolour states; divide by two.
                self.assertEqual(row["edges"], n * n * 2 ** (n - 3))
                sizes = Counter(row["component_sizes"])
                if n % 2:
                    want = [2] * n + [n * comb(2 * m, m)]
                    want += [2 * n * comb(2 * m, m + h) for h in range(1, m)]
                    self.assertEqual(row["reflected_dimers"], n)
                else:
                    want = [1] * n + [m * comb(n, k) for k in range(1, n)]
                    self.assertEqual(row["reflected_dimers"], 0)
                self.assertEqual(sizes, Counter(want))
                self.assertEqual(sum(row["active_degree_histogram"].values()), row["states"])

    def test_two_clock_control_has_no_forced_relative_phase(self):
        row = p.bridged_control()
        self.assertEqual(row["reachable_states"], 4)
        self.assertEqual(row["active_edges_per_state"], 2)
        self.assertEqual(row["reachable_distance_pairs"], [[1, 2], [1, 3], [2, 2], [2, 3]])
        self.assertTrue(row["bridge_inert_throughout"])


if __name__ == "__main__":
    unittest.main()
