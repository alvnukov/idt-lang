from __future__ import annotations

import unittest
from fractions import Fraction as F

from scripts import probe_complement_collision_mixer as mixer
from scripts import probe_uncolored_cycle_carrier as graph
from scripts import probe_unsigned_background_readout as detector
from scripts import probe_unsigned_collision_search as rules
from scripts import probe_unsigned_neutral_motifs as marks
from scripts import probe_unsigned_pair_tickets as tickets


class UnsignedResearchRoutes(unittest.TestCase):
    def test_label_neutrality_is_stronger_than_darkness(self) -> None:
        self.assertEqual(marks.hidden_weight((1, 0, 1, 0)), 0)
        self.assertEqual(marks.gaussian((1, 0, 0, 0)), marks.gaussian((2, 0, 1, 0)))
        self.assertEqual(
            (marks.hidden_weight((1, 0, 0, 0)), marks.hidden_weight((2, 0, 1, 0))),
            (2, 10),
        )

    def test_abelianization_loses_information_in_both_turn_conventions(self) -> None:
        loop: tuple[int, ...] = (1, 2, -1, -2)
        for _ in range(4):
            self.assertEqual(graph.net(loop), (0, 0))
            self.assertEqual(len(graph.reduce_word(loop)), 4)
            loop = graph.turn(loop)
        self.assertEqual(loop, (1, 2, -1, -2))

    def test_exhaustive_contract_not_just_first_hit(self) -> None:
        s = rules.search()
        self.assertEqual(
            (s.counts["all"], s.counts["raw_echo"], s.counts["transparent_root"]),
            (46656, 4, 2),
        )
        self.assertEqual(s.counts["coarse_transparent"], 8)
        self.assertTrue(all(rules.check_table(f)["square_stock"] for f in s.roots))
        self.assertFalse(rules.check_table(s.coarse_nonraw)["raw_echo"])
        with self.assertRaises(ValueError):
            rules.check_table((0, 1, 2, 3, 4, True))

    def test_pairing_refinements_and_blank_input_obstruction(self) -> None:
        self.assertEqual(mixer.counts(mixer.pairing((3, 1, 2, 2))), (3, 1, 2, 2))
        for e in ((2, 0, 0, 0), (1, 1, 1, 0)):
            with self.assertRaises(ValueError):
                mixer.pairing(e)
        n, next_input = tickets.zero_background(5)
        self.assertEqual(n, (0, 5, 5, 0))
        with self.assertRaises(ValueError):
            mixer.pairing(next_input)
        a, b = mixer.reversible_history_cost(3)
        self.assertEqual((a, b), (F(2, 5), 3))

    def test_ticket_tie_changes_trajectory_not_count(self) -> None:
        p = ((0, 1), (0, 1), (1, 3))
        start = tickets.tickets(p)
        a = {tickets.route(p, t) for t in start}
        b = {tickets.route(p, t, reverse_tie=True) for t in start}
        self.assertEqual(a, b)
        self.assertEqual(a, tickets.tickets(tickets.turned(p)))
        self.assertNotEqual(
            tickets.route(p, (0, 1, 0)), tickets.route(p, (0, 1, 0), reverse_tie=True)
        )

    def test_absolute_rate_cost_not_postselected_brightness(self) -> None:
        rows = detector.atoms(8, 2, 3, False)
        self.assertEqual(detector.minimum_dark(rows, F(1, 4)), F(103, 620))
        self.assertGreater(detector.minimum_dark(rows, F(1, 4)), F(7, 60))
