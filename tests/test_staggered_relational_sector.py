"""Independent raw/relational controls for the selected open-path encoding."""

import importlib
import unittest
from itertools import product


class RelationalSectorTests(unittest.TestCase):
    def setUp(self):
        name = "scripts.probe_staggered_relational_sector"
        self.assertIsNotNone(importlib.util.find_spec(name), "missing relational probe")
        self.p = importlib.import_module(name)

    def test_relations_are_global_not_sitewise_complements(self):
        for phase in range(2):
            for anchored in (False, True):
                graph = self.p.layout(3, phase, anchored)
                full = (1 << graph.width) - 1
                seen = set()
                for s in range(full + 1):
                    key = graph.observe(s)
                    self.assertEqual(graph.observe(s ^ full), key)
                    seen.add(key)
                    got = set(graph.neighbors(key))
                    want = {graph.observe(s ^ m) for m in graph.moves if s & m in (0, m)}
                    self.assertEqual(got, want)
                self.assertEqual(len(seen), 1 << (graph.width - 1))
        g = self.p.layout(2, 0)
        self.assertNotEqual(g.observe(0), g.observe(3))  # complement just one home
        self.assertEqual(len({(s & 1) ^ (s >> 1) for s in range(4)}), 2)

    def test_charge_at_raw_links_and_complemented_clean_endpoints(self):
        for n in range(2, 6):
            for phase in range(2):
                graph = self.p.layout(n, phase)
                delta = 1-phase
                self.assertEqual(sum(graph.weights), delta)
                for m in graph.moves:
                    self.assertEqual(graph.charge(m), 0)
                for w in map("".join, product("Tab", repeat=n)):
                    c = graph.clean(w)
                    self.assertEqual(graph.charge(c), w.count("T"))
                    self.assertEqual(graph.charge(graph.clean(w, 1)), delta-w.count("T"))
                    self.assertEqual(graph.observe(c), graph.observe(graph.clean(w, 1)))

    def test_moving_zero_stock_does_not_supply_a_stable_reference(self):
        g = self.p.layout(2, 1)
        self.assertEqual((g.width, g.clean("ab"), g.clean("ba", 1)), (6, 8, 60))
        self.assertIn(g.observe(g.clean("ba")), set(g.neighbors(g.observe(g.clean("ab")))))
        # A one-T preparation is an ENDPOINT restriction, not a raw conservation law.
        route = (1, 53, 4)
        self.assertEqual((g.clean("Ta"), g.clean("aT")), (route[0], route[-1]))
        for a, b in zip(route, route[1:]):
            self.assertIn(a ^ b, g.moves)
            self.assertIn(a & (a ^ b), (0, a ^ b))
        self.assertEqual(tuple(g.charge(x) for x in route), (1, 1, 1))
        self.assertEqual(((53 & 3), (53 >> 2 & 3), 53 >> 4), (1, 1, 3))

    def test_unrestricted_and_fixed_one_clean_comparisons(self):
        expected_unordered_extra = {2: (5, 1), 3: (22, 10), 4: (93, 17)}
        for n, extras in expected_unordered_extra.items():
            for phase, excess in enumerate(extras):
                row = self.p.census(n, phase)
                self.assertEqual(row["all"], {"missing": 0, "extra": excess})
                self.assertEqual(row["one_T"], {"missing": 0, "extra": 0})
                self.assertEqual(self.p.census(n, phase, True)["all"], {"missing": 0, "extra": 0})

    def test_reference_is_an_unoffered_site_and_an_actual_comparison(self):
        graph = self.p.layout(2, 0, True)
        self.assertEqual(graph.width, 5)
        self.assertTrue(all(m < 16 for m in graph.moves))
        self.assertEqual(graph.edges[-1], (0, 4))
        self.assertEqual(graph.observe(graph.clean("Ta")), graph.observe(graph.clean("Ta", 1)))
        self.assertNotEqual(graph.observe(graph.clean("Ta")), graph.observe(graph.clean("bb")))
        bare = self.p.layout(2, 0)
        self.assertEqual(bare.observe(bare.clean("Ta")), bare.observe(bare.clean("bb")))


if __name__ == "__main__":
    unittest.main()
