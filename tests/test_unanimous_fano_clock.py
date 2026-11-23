import unittest
from itertools import combinations

from scripts import probe_unanimous_fano_clock as p


class UnanimousFanoClock(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = p.verify()

    def test_five_site_complete_control(self):
        # Every two-colouring of five sites has a monochromatic triple.
        masks = tuple(sum(1 << i for i in e) for e in combinations(range(5), 3))
        self.assertEqual(p.covering_families(5, 10), (masks,))
        self.assertEqual(p.covering_families(5, 9), ())

    def test_search_starts_from_all_triples(self):
        r = self.report
        self.assertEqual(r["search"]["labelled_candidate_counts"], {6: 1623160, 7: 6724520})
        self.assertEqual(r["search"]["survivors"], {6: 0, 7: 30})
        self.assertTrue(r["search"]["all_and_only_fano_relabellings"])
        self.assertEqual(r["delete_one_line"]["jammed_states_per_deletion"], [10] * 7)

    def test_exact_partition_and_degree_identity(self):
        r = self.report["dynamics"]
        self.assertEqual(r["components"], {"K1,7": 2, "K1,4": 14, "C6": 7})
        self.assertEqual(r["empty_sectors"], [[0, 2]])
        self.assertEqual(r["states_matched_to_exact_sector"], 128)
        self.assertEqual(r["states_matching_degree_formula"], 128)

    def test_the_clock_is_only_a_per_event_sector_readout(self):
        r = self.report["clock"]
        self.assertEqual(r["states_by_persistent_point"], {i: 6 for i in range(1, 8)})
        self.assertEqual(r["enabled_directed_events_flipping_persistent_point"], 84)
        self.assertEqual(r["phase_reversing_complements_in_same_sector"], 42)
        self.assertEqual(r["states_without_persistent_component_point"], 86)

    def test_global_parity_is_a_weaker_nonlocal_control(self):
        # On each of seven lines, two uniform settings times 2^4 spectators.
        self.assertEqual(self.report["dynamics"].get("active_events_flipping_global_parity"),
                         7 * 2 * 16)

    def test_restored_transport_obstruction(self):
        r = self.report["transport"]
        self.assertTrue(r["all_line_xors_zero"])
        # Each unordered site pair, both directions, 2^5 spectator settings.
        self.assertEqual(r["directed_restored_moves_excluded"], 21 * 2 * 32)


if __name__ == "__main__":
    unittest.main()
