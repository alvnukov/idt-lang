"""Finite scheduler contracts, not a physical clock or probability law."""

from fractions import Fraction
from functools import cache
import unittest

from scripts.probe_packet_scheduler_fairness import scheduler_fairness

probe = cache(scheduler_fairness)


class PacketSchedulerFairnessTest(unittest.TestCase):
    def test_bounded_proposals_are_not_firings(self):
        tour = probe()["bounded_proposals"]
        self.assertEqual(tour["centers"], (*range(16), 1))
        self.assertEqual(tour["supports"], ((0,), (0, 1)))
        self.assertEqual(tour["fired_labels"], (1,))
        self.assertFalse(tour["target_contact"])
        self.assertTrue(tour["closed"])

    def test_all_permutation_words_including_intermediate_states(self):
        sweep = probe()["permutation_sweeps"]
        self.assertEqual(sweep["histogram_singletons_raw_orders"], (
            (4, 8, 3360), (6, 12, 6720), (8, 16, 3360), (8, 18, 26880),
        ))
        self.assertEqual(sweep["orders"], 40320)
        self.assertEqual(sweep["hit_target"], 33600)
        self.assertEqual(probe()["conjugate_state_center_checks"], 20 * 16)

    def test_label_fair_tour_omits_state_specific_firings(self):
        tour = probe()["label_fair"]
        self.assertEqual(len(tour["centers"]), 12)
        self.assertTrue(tour["closed"])
        self.assertEqual(tour["supports"], ((0,), (0, 1), (0, 3), (0, 4),
                                            (1,), (1, 2), (1, 5)))
        self.assertEqual(tour["enabled_labels"], (0, 1, 2, 3, 4, 5))
        self.assertEqual(tour["fired_labels"], tour["enabled_labels"])
        self.assertEqual(tour["taken_state_actions"], 12)
        self.assertEqual(tour["missed_state_actions"], 4)
        self.assertFalse(tour["target_contact"])
        self.assertFalse(tour["target_singleton"])

    def test_event_fair_recurring_tour_covers_whole_graph(self):
        tour = probe()["state_transition_fair"]
        self.assertTrue(tour["closed"])
        self.assertEqual(len(tour["supports"]), 20)
        self.assertEqual(tour["taken_state_actions"], 48)
        self.assertEqual(tour["missed_state_actions"], 0)
        self.assertTrue(tour["target_singleton"])

    def test_exact_means_apply_to_different_sampling_units(self):
        law = probe()["opposite_singleton"]
        self.assertEqual(law["shortest_enabled_events"], 6)
        self.assertEqual(law["shortest_to_first_contact"], 5)
        self.assertEqual(Fraction(law["mean_enabled_events"]), 40)
        self.assertEqual(Fraction(law["mean_all_center_proposals"]), Fraction(800, 3))


if __name__ == "__main__":
    unittest.main()
