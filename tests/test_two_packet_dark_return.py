"""Separate passive reachability, consuming readout and the one-body control."""

import importlib
import importlib.util
import unittest
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations
from types import SimpleNamespace


class TwoPacketDarkReturn(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        name = "scripts.probe_two_packet_dark_return"
        cls.p = importlib.import_module(name) if importlib.util.find_spec(name) else None

    def setUp(self):
        self.assertIsNotNone(self.p, "two-packet dark return probe is missing")

    def test_zero_first_hit_does_not_forbid_a_later_unmetered_return(self):
        fixture = self.p.Wedge((31, 37))
        layer = {fixture.packet(0)}
        seen = set(layer)
        for event in range(127):
            if any(fixture.gates.get(state) == "0" for state in layer):
                self.assertEqual(event, 126)
                return
            following = {move.apply(state) for state in layer
                         for move in fixture.rule.offers(state)} - seen
            seen.update(following)
            layer = following
        self.fail("unmetered no-return assumption was not counterchecked")

    def test_passive_witness_replays_all_ordered_source_pairs(self):
        p = self.p
        self.assertEqual(p.WITNESS_SIZES, (101, 103))
        self.assertGreaterEqual(min(p.HELDOUT_SIZES), 139)
        control_menus = {}
        for sizes in (p.WITNESS_SIZES, p.HELDOUT_SIZES):
            fixture = p.Wedge(sizes)
            for returning, other in permutations(range(4), 2):
                with self.subTest(sizes=sizes, returning=returning, other=other):
                    witness = p.passive_witness(fixture, returning, other)
                    self.assertEqual(len(witness.degrees), 29)
                    self.assertEqual(witness.prefix_mass, F(1, 24_461_180_928))
                    self.assertEqual(witness.joint_only_steps, (10,))
                    self.assertEqual(witness.final, fixture.packet(returning, 4, outward=True)
                                     | fixture.packet(returning, 10, outward=True))
                    self.assertEqual(len(witness.final & fixture.rule.shorts), 2)
                    self.assertEqual(len(witness.final & fixture.rule.longs), 2)
                    # Across the two line-incidence classes, compare menus
                    # within class, including moves not chosen on the itinerary.
                    same_line = (returning ^ other) == 1
                    menus = control_menus.setdefault(same_line, witness.offer_menus)
                    self.assertEqual(witness.offer_menus, menus)

    def test_one_body_control_is_the_same_fixture_not_fitted_to_pair_data(self):
        p = self.p
        rows = p.one_body_rows(p.Wedge(p.INSTRUMENT_SIZES))
        self.assertEqual(rows, tuple(tuple(F(i != j, 3) for j in range(4))
                                     for i in range(4)))
        for inputs in combinations(range(4), 2):
            outcomes = p.independent_pair(rows, inputs)
            self.assertEqual(sum(outcomes.values()), 1)
            for port in inputs:
                self.assertEqual(outcomes[port, port], 0)
            for port in set(range(4)) - set(inputs):
                self.assertEqual(outcomes[port, port], F(1, 9))

    def test_consuming_instrument_bounds_dark_returns_without_conditioning(self):
        p = self.p
        fixture = p.Wedge(p.INSTRUMENT_SIZES)
        self.assertEqual(fixture.sizes, (31, 37))
        for inputs in combinations(range(4), 2):
            with self.subTest(inputs=inputs):
                terminal = p.consuming_row(fixture, inputs, horizon=24)
                self.assertEqual(sum(terminal.values()), 1)
                self.assertTrue(any(mass for (status, _), mass in terminal.items()
                                    if status == "unresolved"))
                self.assertTrue(any(mass for (status, _), mass in terminal.items()
                                    if status == "jam"))
                self.assertFalse(any(mass for (status, _), mass in terminal.items()
                                     if status == "overlap"))
                for port in inputs:
                    self.assertEqual(terminal["detected", (port, port)],
                                     F(11262469367, 10749542400000))

    def test_overlapping_removals_are_an_explicit_outcome(self):
        p = self.p
        fixture = p.Wedge(p.INSTRUMENT_SIZES)
        first, second = fixture.packet(0), fixture.packet(2)
        shared = frozenset((next(iter(first)), next(iter(second))))
        alternative = SimpleNamespace(gates={first: "0", shared: "2"})
        self.assertEqual(p.absorbing_successors(alternative, first | second, ()),
                         (("overlap", ()), ()))

    def test_integer_propagation_matches_literal_fraction_paths(self):
        p = self.p
        fixture = p.Wedge(p.INSTRUMENT_SIZES)
        inputs = (0, 2)
        seed = fixture.packet(0) | fixture.packet(2)
        frontier = {(seed, ()): F(1)}
        outcomes = defaultdict(F)
        horizon = 24
        for time in range(horizon + 1):
            pending = defaultdict(F)
            for (state, ports), weight in frontier.items():
                matches = [(gate, int(arm)) for gate, arm in fixture.gates.items()
                           if gate <= state]
                bonds = frozenset().union(*(gate for gate, _ in matches))
                self.assertEqual(len(bonds), 2 * len(matches))
                ports = tuple(sorted(ports + tuple(arm for _, arm in matches)))
                state -= bonds
                offers = fixture.rule.offers(state)
                if len(ports) == 2:
                    outcomes["detected", ports] += weight
                elif not offers:
                    outcomes["jam", ports] += weight
                elif time == horizon:
                    outcomes["unresolved", ports] += weight
                else:
                    for move in offers:
                        pending[move.apply(state), ports] += weight / len(offers)
            frontier = pending
        self.assertGreater(outcomes["detected", (0, 0)], 0)
        self.assertGreater(outcomes["detected", (2, 2)], 0)
        self.assertEqual(p.consuming_row(fixture, inputs, horizon=horizon), dict(outcomes))


if __name__ == "__main__":
    unittest.main()
