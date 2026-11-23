"""Changing an untraversed corridor cannot modulate another path's mass."""

import importlib
import importlib.util
import unittest
from fractions import Fraction as F

from scripts import probe_raw_bond_junction_rates as base


class IndependentArmDelays(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_independent_arm_delays"
        cls.rows = None
        if importlib.util.find_spec(name):
            data = importlib.import_module(name).report()
            cls.transfer = data["transfer"]
            cls.jams = {(r["mask"], r["input"]): F(r["jam"]) for r in data["rows"]}
            cls.rows = {(r["mask"], r["input"]): {k: F(v) for k, v in r["joint"].items()}
                        for r in data["rows"]}

    def setUp(self):
        self.assertIsNotNone(self.rows, "independent four-corridor census missing")

    def test_all_logged_paths_and_losses(self):
        self.assertEqual(set(self.rows), {(m, i) for m in range(16) for i in range(4)})
        for (mask, i), joint in self.rows.items():
            expected = {}
            for j in set(range(4)) - {i}:
                exits = set(range(4)) - {j}
                if mask & 1 << j:
                    exits = {j ^ 1}
                    expected[f"{j}:jam"] = F(2, 9)
                expected.update({f"{j}:{k}": F(1, 9) for k in exits})
            self.assertEqual(joint, expected, (mask, i))
            self.assertEqual(self.jams[mask, i], F(2, 9) * (mask & ~(1 << i)).bit_count())

    def test_positive_alternate_paths_and_zero_mixed_response(self):
        for i in range(4):
            for m in range(16):
                joint = self.rows[m, i]
                for key in joint:
                    j = int(key[0])
                    for bit in set(range(4)) - {j}:
                        self.assertEqual(joint[key], self.rows[m ^ (1 << bit), i][key])
                for key in set.union(*(set(self.rows[s, i]) for s in range(16))):
                    if m.bit_count() >= 2:
                        diff = sum((-1)**((m ^ s).bit_count()) * self.rows[s, i].get(key, 0)
                                   for s in range(16) if (s & m) == s)
                        self.assertEqual(diff, 0, (m, i, key))

    def test_uniform_lengths_reproduce_original_literal_graph(self):
        for mask, length in ((0, 14), (15, 15)):
            graph, point = base.two_crossings(length)
            seeds = [base.phase_a(point, axis, side*6, -side) for axis, side in base.ARMS]
            trans, terminals = base.event_graph(base.FreeAlternatives(graph), seeds,
                base.gates(point, 0), base.gates(point, length, far=True))
            reference, _ = base.first_event(trans, terminals)
            for i, seed in enumerate(seeds):
                self.assertEqual(self.rows[mask, i], reference[None, seed])

    def test_mixed_length_transfer(self):
        self.assertEqual(self.transfer["lengths"], [21, 24, 19, 28])
        for r in self.transfer["rows"]:
            self.assertEqual({k: F(v) for k, v in r["joint"].items()},
                             self.rows[5, r["input"]])
        self.assertEqual([r["input"] for r in self.transfer["rows"]], list(range(4)))
