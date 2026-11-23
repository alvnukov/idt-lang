"""Frozen first-detector kernels; no conditioning away jams or traps."""

import importlib
import importlib.util
import unittest
from unittest.mock import patch
from collections import Counter
from fractions import Fraction as F


class JunctionRates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_raw_bond_junction_rates"
        if importlib.util.find_spec(name):
            cls.module = importlib.import_module(name)
            cls.result = cls.module.report()
        else:
            cls.module = None

    def setUp(self):
        self.assertIsNotNone(self.module, "raw first-event junction rates not implemented")

    def test_finite_wedge_first_outcomes(self):
        rows = self.result["isolated"]
        self.assertEqual(len(rows), 32)
        for row in rows:
            i = row["input"]
            masses = tuple(map(F, row["mass"]))
            expected = [F(0)] * 6
            if row["law"] == "line":
                expected[i ^ 1] = F(1)
            else:
                expected[i ^ 1] = F(1, 3)
                if row["offset"] == 7:
                    expected[4] = F(2, 3)
                else:
                    expected[i ^ 2] = expected[i ^ 3] = F(1, 3)
            self.assertEqual(masses, tuple(expected), row)

    def test_closed_recurrence_and_multiplicity_are_not_postselected(self):
        # Geometric self-loop and repeated distinct offers with the same destination.
        trans = {"s": ("s", "s", "u", "u", "v"), "u": ("u",), "v": ()}
        masses, _ = self.module.first_event(trans, {"v": "jam"})
        self.assertEqual(masses["s"], {"trap": F(2, 3), "jam": F(1, 3)})

    def test_trapped_after_the_first_hit_keeps_that_arm(self):
        module = self.module
        graph, point = module.two_crossings(14)

        def late_trap(rule, seeds, first, second):
            trapped = ("2", frozenset())
            rows = {(None, s): (trapped,) for s in seeds}
            rows[trapped] = (trapped,)
            return rows, {}

        with patch.object(module, "event_graph", late_trap):
            rows = module.run_fixture(graph, point, second={})
        self.assertTrue(rows)
        for row in rows:
            self.assertEqual(row["joint"], {"2:trap": "1"})
            self.assertEqual(row["mass"][-1], "1")

    def test_reset_and_supplied_coherent_comparator(self):
        rows = self.result["comparison"]
        for i in range(4):
            independent = [F(x) for x in rows["independent_reset"][i]]
            coherent = [F(x) for x in rows["supplied_coherent"][i]]
            self.assertEqual(independent, [F(1, 3) if i == j else F(2, 9)
                                          for j in range(4)])
            self.assertEqual(coherent, [F(int(i == j)) for j in range(4)])

    def test_literal_two_junctions_include_unread_outcomes(self):
        rows = self.result["literal"]
        self.assertEqual(len(rows), 32)
        for row in rows:
            self.assertEqual(sum(map(F, row["mass"])), 1)
            self.assertEqual(sum(F(m) for m in row["joint"].values()), 1)
            if row["law"] == "line":
                self.assertEqual(F(row["mass"][row["input"]]), 1)
                continue
            i = row["input"]
            # All four corridor names use the zero-end convention at *both* ends.
            # On a 14 corridor the outgoing phase parity persists; on 15 it flips.
            odd1 = row["offset"] == 7
            odd2 = odd1 != (row["length"] == 15)
            joint = {}
            if odd1:
                joint["jam"] = F(2, 3)
            for first in range(4):
                if first == i or (odd1 and first != i ^ 1):
                    continue
                if odd2:
                    joint[f"{first}:jam"] = F(2, 9)
                for second in range(4):
                    if second != first and (not odd2 or second == first ^ 1):
                        joint[f"{first}:{second}"] = F(1, 9)
            self.assertEqual(joint, {k: F(v) for k, v in row["joint"].items()})

    def test_raw_forward_paths_independently_bound_literal_joint(self):
        """No SCCs, linear solver, production detector map, or product-graph builder."""
        from scripts.probe_bond_carrier_geometry import FreeAlternatives

        for length in (14, 15):
            graph, point = self.module.two_crossings(length)
            rule = FreeAlternatives(graph)

            def marks(axis, start, heading, point=point):
                p, q, r = (point(axis, start + d*heading) for d in (0, 2, 3))
                return frozenset((frozenset((p, q)), frozenset((q, r))))

            detect = {}
            for axis in (0, 1):
                for side in (-1, 1):
                    corridor = 2*axis + int(side == 1)
                    for distance in (4, 5):
                        detect[0, marks(axis, side*distance, side)] = corridor
                        detect[1, marks(axis, length-side*distance, -side)] = corridor
            move_cache = {}
            for offset in (6, 7):
                arrived = Counter()
                frontier = {(marks(0, -offset, +1), None): F(1)}
                for _ in range(120):
                    pending = Counter()
                    for (state, first), weight in frontier.items():
                        if first is not None and (1, state) in detect:
                            arrived[f"{first}:{detect[1, state]}"] += weight
                            continue
                        if first is None:
                            first = detect.get((0, state))
                        if state not in move_cache:
                            move_cache[state] = tuple(m.apply(state) for m in rule.offers(state))
                        targets = move_cache[state]
                        if not targets:
                            arrived["jam" if first is None else f"{first}:jam"] += weight
                        for target in targets:
                            pending[target, first] += weight / len(targets)
                    frontier = pending
                remaining = sum(frontier.values())
                self.assertEqual(remaining + sum(arrived.values()), 1)
                self.assertLess(remaining, F(1, 10000000))
                row, = (r for r in self.result["literal"] if r["input"] == 0
                        and r["law"] == "free" and r["length"] == length and r["offset"] == offset)
                exact = {k: F(v) for k, v in row["joint"].items()}
                for k in arrived.keys() | exact.keys():
                    self.assertLessEqual(arrived[k], exact.get(k, 0))
                    self.assertLessEqual(exact.get(k, 0), arrived[k] + remaining)
