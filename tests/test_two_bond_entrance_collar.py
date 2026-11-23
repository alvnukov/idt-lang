"""The same input and contact time can hide inequivalent two-bond states."""

import importlib
import importlib.util
import unittest
from collections import Counter, defaultdict
from fractions import Fraction as F

from scripts import probe_raw_bond_junction_rates as base
from scripts.probe_conserved_bond_gait import cycle_square
from scripts.probe_independent_arm_delays import fixture


class TwoBondEntranceCollarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_two_bond_entrance_collar"
        cls.probe = importlib.import_module(name) if importlib.util.find_spec(name) else None
        cls.data = cls.probe.report() if cls.probe else None

    def setUp(self):
        self.assertIsNotNone(self.probe, "two-bond entrance collar replay missing")

    def test_isolated_first_touch_predecessors_are_exhausted_in_both_directions(self):
        raw = base.FreeAlternatives(cycle_square(71))
        census = self.data["isolated_first_touch"]
        self.assertEqual(census["q_avoiding_pairs"], 138 * 137 // 2)
        self.assertEqual(Counter(row["phase"] for row in census["transitions"]),
                         {"A": 2, "B": 2})
        for h in [-1, 1]:
            def state(*edges):
                return frozenset(base.link(32 + h*a, 32 + h*b) for a, b in edges)

            actual = [row for row in census["transitions"] if row["direction"] == h]
            expected = {
                "A": (state((-3, -1), (-2, -1)), state((-3, -1), (-1, 0))),
                "B": (state((-4, -2), (-2, -1)), state((-4, -2), (-1, 0))),
            }
            for row in actual:
                before, after = expected[row["phase"]]
                self.assertNotIn(32, set().union(*before))
                self.assertEqual({m.apply(before) for m in raw.offers(before)}, {after})
                self.assertEqual(frozenset(map(frozenset, row["before"])), before)
                self.assertEqual(frozenset(map(frozenset, row["after"])), after)

    def test_each_input_has_same_arrival_time_but_distinct_exact_full_laws(self):
        rows = self.data["rows"]
        fixtures = {(31, 37), (47, 53), (21, 24, 19, 28)}
        self.assertCountEqual(
            [(tuple(r["lengths"]), r["input"], r["phase"]) for r in rows],
            [(sizes, i, phase) for sizes in fixtures for i in range(4) for phase in "AB"],
        )
        for row in rows:
            i, phase = row["input"], row["phase"]
            self.assertEqual(row["first_contact_time"], 0)
            self.assertEqual(row["first_junction_touch_time"], 9)
            self.assertEqual(row["line"]["atoms"], [[21 if phase == "A" else 20, str(i ^ 1), "1"]])
            free = row["free"]
            if phase == "A":
                self.assertEqual(free["atoms"], [[11, "jam", "2/3"], [21, str(i ^ 1), "1/3"]])
            else:
                self.assertEqual(free["geometric"]["outcomes"],
                                 [str(j) for j in range(4) if i != j])
                self.assertEqual(free["geometric"]["start"], 20)
                self.assertEqual(F(free["geometric"]["first_mass"]), F(1, 9))
                self.assertEqual(F(free["geometric"]["ratio"]), F(2, 3))
                self.assertEqual(free["checked_through"],
                                 free["geometric"]["start"] + free["transient_states"])
                self.assertEqual(free["residual_steps"], free["transient_states"])

    def test_far_fixture_keeps_corridor_labels_and_tail_beyond_certificate(self):
        graph, near, far = fixture((21, 24, 19, 28))
        axis, near_side = base.ARMS[2]
        # At the far end, local plus on axis 1 runs back down corridor 2.
        self.assertEqual(far(axis, 19), near(axis, 0))
        self.assertNotEqual(far(axis, -19), near(axis, 0))
        self.assertEqual(near_side, -1)
        seed = self.probe.preparation(far, 2, "B", far=True)
        self.assertEqual(seed, frozenset((base.link(far(axis, 10), far(axis, 8)),
                                          base.link(far(axis, 7), far(axis, 6)))))
        raw = base.FreeAlternatives(graph)
        correct = base.gates(far, 0, far=True)
        swapped = base.gates(far, 0, far=False)
        self.assertEqual(set(correct), set(swapped))
        self.assertTrue(all(int(correct[s]) ^ 1 == int(swapped[s]) for s in correct))
        # Independent raw propagation, outside the report's finite certificate window.
        row = next(r for r in self.data["rows"] if r["fixture"] == "far_junction"
                   and r["input"] == 2 and r["phase"] == "B")
        time = row["free"]["checked_through"] + 7
        current = {seed: F(1)}
        for t in range(time + 1):
            later, exits = defaultdict(F), defaultdict(F)
            for state, weight in current.items():
                if state in correct:
                    exits[correct[state]] += weight
                    continue
                moves = raw.offers(state)
                self.assertTrue(moves, (t, state))
                for move in moves:
                    later[move.apply(state)] += weight / len(moves)
            current = later
        self.assertEqual(exits, {str(j): F(1, 9) * F(2, 3)**(time - 20)
                                 for j in [0, 1, 3]})

    def test_exact_certifier_rejects_late_non_geometric_exit(self):
        # The first hit agrees with the proposed tail; a delayed trap would be
        # missed by just checking that hit and normalizing the proposed formula.
        trans = {"seed": ("out", "wait"), "wait": ("later",), "later": ("jam",),
                 "out": (), "jam": ()}
        terminal = {"out": "0", "jam": "jam"}
        with self.assertRaisesRegex(ArithmeticError, "first-hit law"):
            self.probe.certify_geometric(trans, terminal, "seed",
                                         start=1, outcomes=("0",), first=F(1, 2), ratio=F(1, 2))

    def test_distinct_offers_with_same_target_both_count(self):
        # Rows are tuples of offered moves' targets, not sets of destinations.
        trans = {"seed": ("out", "out", "jam"), "out": (), "jam": ()}
        hits, live = self.probe.propagate(trans, {"out": "1", "jam": "jam"}, "seed", 1)
        self.assertEqual(hits, {(1, "1"): F(2, 3), (1, "jam"): F(1, 3)})
        self.assertEqual(live, 0)
