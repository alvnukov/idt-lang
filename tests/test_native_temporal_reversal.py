"""Independent address and common-history controls for the finite probe."""

import importlib
import importlib.util
import unittest
from fractions import Fraction as Q
from itertools import product

from scripts.probe_conserved_bond_gait import Ports, cycle_square, link, offers


def address_fixture(names, midpoint, heading, phase):
    """Only the test oracle uses ring addresses."""
    n = len(names)

    def at(k):
        return names[(midpoint + k * heading) % n]

    start = {"A": 1, "B": 2, "C": 0}[phase]
    return frozenset((link(at(-1), at(1)), link(at(start), at(start + 1))))


class TemporalReversalTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(
            importlib.util.find_spec("scripts.probe_native_temporal_reversal"),
            "the native reversal probe is not implemented",
        )
        self.p = importlib.import_module("scripts.probe_native_temporal_reversal")

    def test_local_reversal_and_real_transition_on_opaque_vertices(self):
        for n in (9, 10, 13):
            names = [object() for _ in range(n)]
            graph = {
                names[v]: frozenset(names[w] for w in ws)
                for v, ws in reversed(tuple(cycle_square(n).items()))
            }
            ports = Ports.from_graph(graph)
            for m, h, phase in product(range(n), (-1, 1), "ABC"):
                s = address_fixture(names, m, h, phase)
                reading = self.p.decode(graph, ports, s)
                self.assertEqual((reading.midpoint, reading.phase), (names[m], phase))
                j = address_fixture(names, m, -h, {"A": "A", "B": "C", "C": "B"}[phase])
                self.assertEqual(reading.reversed_state, j)
                self.assertEqual(self.p.decode(graph, ports, j).reversed_state, s)
                (move,) = offers(ports, s)
                successor = move.apply(s)
                self.assertEqual(
                    successor,
                    address_fixture(
                        names,
                        m + 2 * h * (phase == "B"),
                        h,
                        {"A": "B", "B": "C", "C": "A"}[phase],
                    ),
                )
                (reversed_move,) = offers(
                    ports, self.p.decode(graph, ports, successor).reversed_state
                )
                self.assertEqual(
                    reversed_move.apply(
                        self.p.decode(graph, ports, successor).reversed_state
                    ),
                    j,
                )

    def test_native_returns_and_history_sample_sizes(self):
        for n in (9, 10, 13):
            r = self.p.audit_sector(n)
            self.assertEqual(r["active_states"], 6 * n)
            self.assertEqual(r["ordinary_reverse_edges"], 0)
            self.assertLess(r["same_center_under_J"], 6 * n)
            self.assertEqual(r["long_neighbor_reader"]["return_counts"], [12, 4, 2, 6])
            self.assertEqual(r["long_neighbor_reader"]["conditioned_on"], 12)
            self.assertEqual(
                r["outer_touch_reader"]["return_counts"], [2 * n, 0, 0, 2 * n]
            )
            self.assertEqual(r["outer_touch_reader"]["conditioned_on"], 2 * n)
            self.assertEqual(
                r["outer_touch_memory_control"],
                {
                    "P_A_next_given_A": "0",
                    "P_A_next_given_not_A": "1/2",
                    "one_step_fit_lag2": "1/2",
                    "actual_lag2": "0",
                },
            )
            pivot = r["pivot_traces"]
            self.assertEqual(pivot["unsupported_reversals_by_length"], [0, 0, 4 * n])
            self.assertEqual(pivot["distinct_triples"], 6 * n)
            self.assertEqual(
                (pivot["first_is_long_midpoint"], pivot["last_is_long_midpoint"]),
                (2 * n, 0),
            )
            history = r["passive_histories"]
            self.assertEqual(
                history["reader_clock_cases"], (n + 8) * len(history["clock_gaps"])
            )
            self.assertEqual(
                history["histories_counted"], 6 * n * history["reader_clock_cases"]
            )
            self.assertEqual(sum(history["example"]["triple_counts"].values()), 6 * n)
            self.assertLessEqual(Q(history["max_K"]), 1)
            self.assertGreaterEqual(Q(history["min_K"]), -3)

    def test_joint_histories_and_supplied_cost_witnesses(self):
        for q0, q1, q2 in product((-1, 1), repeat=3):
            r = self.p.pair_correlations({(q0, q1, q2): 3})
            self.assertEqual(r, (q0 * q1, q1 * q2, q0 * q2))
            self.assertLessEqual(r[0] + r[1] - r[2], 1)
        with self.assertRaises(ValueError):
            self.p.pair_correlations({(1, 1, 1): 2, (-1, 1, -1): -1})
        supplied = self.p.supplied_target()
        target = (Q(1, 2), Q(1, 2), Q(-1, 2))
        rows = supplied["signed_witness"]
        self.assertEqual(sum(Q(row["weight"]) for row in rows), 1)
        self.assertEqual(
            tuple(
                sum(Q(row["weight"]) * row["products"][i] for row in rows)
                for i in range(3)
            ),
            target,
        )
        self.assertEqual(
            sum(-Q(row["weight"]) for row in rows if Q(row["weight"]) < 0),
            Q(supplied["min_negative_mass"]),
        )
        self.assertEqual(Q(supplied["min_negative_mass"]), Q(1, 8))
        contextual = supplied["pair_context_mixture"]
        self.assertEqual(sum(Q(row["weight"]) for row in contextual), 1)
        self.assertEqual(
            tuple(
                sum(Q(row["weight"]) * row["products"][i] for row in contextual)
                for i in range(3)
            ),
            target,
        )
        self.assertEqual(Q(supplied["min_pair_context_fraction"]), Q(1, 4))
        self.assertEqual(
            sum(Q(r["weight"]) for r in contextual if r["kind"] == "pair_context"),
            Q(1, 4),
        )
