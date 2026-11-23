"""Exact raw support, clock, readout and tail checks for the open analyzer."""

import importlib
import importlib.util
import unittest
from collections import Counter
from fractions import Fraction as F
from functools import reduce
from itertools import permutations, product

from scripts import probe_colorless_packet_arms as frozen


class UndrivenColorlessAnalyzerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_undriven_colorless_analyzer"
        if importlib.util.find_spec(name):
            cls.p = importlib.import_module(name)
            cls.report = cls.p.verify()
        else:
            cls.p = None

    def setUp(self):
        self.assertIsNotNone(self.p, "undriven colorless analyzer probe is missing")

    def test_preparations_stop_at_frozen_plate_and_cover_every_unfiltered_seed(self):
        p = self.p
        self.assertEqual(set(self.report.rows), set(product(frozen.ARMS, frozen.SWITCHES)))
        self.assertIs(p.four_label_contact, frozen.four_label_contact)
        for (source, plates), row in self.report.rows.items():
            samples = p.prepared_states(source, plates)
            self.assertEqual(samples, tuple(frozen.run_trial(source, seed, (0, 0), plates,
                                                             (True, True)).plated
                                            for seed in frozen.SOURCE_SEEDS))
            self.assertEqual(p.read(row.initial, self.report.states).arms, (F(1, 2), F(1, 2)))
            self.assertEqual(row.correct_arm, source ^ plates[0] ^ plates[1])
            mirror = p.prepared_states(1 - source, plates[::-1])
            self.assertEqual(mirror, tuple(frozen.mirror(samples[frozen.SOURCE_SEEDS.index(seed[::-1])])
                                           for seed in frozen.SOURCE_SEEDS))

    def test_twelve_raw_states_are_reachable_and_have_exactly_one_token(self):
        p = self.p
        states = self.report.states
        self.assertEqual(p.CONTACTS, ((0, 1), (3, 4), (2, 1), (5, 4), (1, 4)))
        self.assertEqual(len(states), 12)
        todo = list(p.prepared_states(0, (False, False)))
        reached = set(todo)
        while todo:
            state = todo.pop()
            for edge in p.CONTACTS:
                outcome = frozen.replay(state, ((edge,),))[-1]
                if outcome not in reached:
                    todo.append(outcome)
                    reached.add(outcome)
        self.assertEqual(set(states), reached)
        self.assertEqual(set(map(frozen.mirror, states)), reached)
        for state in states:
            self.assertEqual(state.count(frozen.TOKEN), 1)
            self.assertIn(state.index(frozen.TOKEN), {0, 1, 3, 4})
            self.assertEqual((state[2], state[5], *state[6:]), (0, 0, 1, 0, 1, 0))

    def test_clock_matrices_are_exact_averages_with_named_units_and_invariant_laws(self):
        p = self.p
        report = self.report
        self.assertEqual({name: (clock.unit, clock.operations_per_tick)
                          for name, clock in report.clocks.items()}, {
            "attempted_edges": ("attempted edge", 1),
            "active_offers": ("active edge offer", 1),
            "permutation_sweeps": ("complete five-edge permutation sweep", 5),
        })
        n = len(report.states)
        for name, clock in report.clocks.items():
            degrees = []
            for i, state in enumerate(report.states):
                offers = [frozen.replay(state, ((edge,),))[-1] for edge in p.CONTACTS]
                active = [after for after in offers if after != state]
                degrees.append(len(active))
                if name == "permutation_sweeps":
                    offers = [reduce(lambda raw, edge: frozen.replay(raw, ((edge,),))[-1], order, state)
                              for order in permutations(p.CONTACTS)]
                elif name == "active_offers":
                    offers = active
                counts = Counter(offers)
                self.assertEqual(clock.matrix[i], tuple(F(counts[after], len(offers))
                                                         for after in report.states))
            expected = (tuple(F(degree, sum(degrees)) for degree in degrees) if name == "active_offers"
                        else (F(1, n),) * n)
            self.assertEqual(clock.stationary, expected)
            self.assertEqual(p.advance(clock.stationary, clock.matrix), clock.stationary)
            self.assertEqual(p.read(clock.stationary, report.states).arms, (F(1, 2), F(1, 2)))

    def test_arm_lift_is_not_fixed_detector_lift_or_click_postselection(self):
        left = self.report.rows[0, (False, False)].trajectories["attempted_edges"].prefix[1].readout
        self.assertEqual(left.sites, (F(3, 10), F(1, 4), F(3, 10), F(3, 20)))
        self.assertEqual(left.arms, (F(11, 20), F(9, 20)))
        self.assertEqual(left.fixed_detector, (F(3, 10), F(3, 10), F(2, 5)))
        self.assertEqual(left.correct_given_detector_click(0), F(1, 2))
        self.assertEqual(self.p.Readout((F(0), F(1, 2), F(0), F(1, 2))).
                         correct_given_detector_click(0), None)

    def test_every_setting_has_its_global_exact_max_certified_by_tv(self):
        expected = {
            "attempted_edges": (F(11, 20), (1, 2)),
            "active_offers": (F(7, 12), (1,)),
            "permutation_sweeps": (F(1297, 2304), (2,)),
        }
        p = self.p
        for (source, plates), row in self.report.rows.items():
            reflected = self.report.rows[1 - source, plates[::-1]]
            for name, result in row.trajectories.items():
                with self.subTest(source=source, plates=plates, clock=name):
                    maximum, times = expected[name]
                    self.assertEqual((result.maximum, result.maximizing_ticks), (maximum, times))
                    clock = self.report.clocks[name]
                    distribution = row.initial
                    for tick, sample in enumerate(result.prefix):
                        self.assertEqual(sample.readout, p.read(distribution, self.report.states))
                        other = reflected.trajectories[name].prefix[tick].readout
                        self.assertEqual(sample.readout.sites, other.sites[2:] + other.sites[:2])
                        distribution = p.advance(distribution, clock.matrix)
                    self.assertEqual(len(result.prefix) - 1, 4)
                    exact_tv = sum(abs(a - b) for a, b in zip(result.prefix[-1].distribution,
                                                             clock.stationary, strict=True)) / 2
                    self.assertEqual(result.tail_tv, exact_tv)
                    self.assertLess(F(1, 2) + result.tail_tv, maximum)

    def test_complete_sweep_clock_has_a_late_dip_below_even(self):
        p = self.p
        row = self.report.rows[0, (False, False)]
        sweeps = self.report.clocks["permutation_sweeps"]
        distribution = row.initial
        for _ in range(38):
            distribution = p.advance(distribution, sweeps.matrix)
        self.assertLess(p.read(distribution, self.report.states).arms[0], F(1, 2))
        self.assertEqual(self.report.sweep_dip_tick, 38)


if __name__ == "__main__":
    unittest.main()
