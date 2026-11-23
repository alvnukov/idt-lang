import unittest
from collections import Counter
from itertools import combinations

from scripts import probe_binary_unanimous_triples as raw
from scripts import probe_relational_unanimous_clock as p


class RelationalClock(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = p.verify()

    def test_offers_intertwine_with_the_actual_raw_operation(self):
        model = p.Relations(7, p.FANO)
        lifts = Counter(model.gradient(s) for s in range(128))
        self.assertEqual(set(lifts.values()), {2})
        for s in range(128):
            for i, t in enumerate(p.FANO):
                mask = sum(1 << v for v in t)
                before = model.gradient(s)
                self.assertEqual(model.enabled(before, i), raw.offer(s, mask) != s)
                self.assertEqual(model.offer(before, i), model.gradient(raw.offer(s, mask)))

    def test_disconnected_components_can_be_complemented_independently(self):
        model = p.Relations(6, ((0, 1, 2), (3, 4, 5)))
        self.assertEqual(Counter(Counter(model.gradient(s) for s in range(64)).values()), {4: 16})
        self.assertEqual(set(model.local_states()), {model.gradient(s) for s in range(64)})

    def test_smaller_supports_have_no_extra_local_states(self):
        for n in range(7):
            triples = tuple(combinations(range(n), 3))
            limit = len(triples) if n <= 4 else min(2, len(triples))
            for k in range(limit + 1):
                for family in combinations(triples, k):
                    model = p.Relations(n, family)
                    self.assertEqual(set(model.local_states()),
                                     {model.gradient(s) for s in range(1 << n)})

    def test_minimal_jam_is_locally_unanimity_indistinguishable_from_a_lift(self):
        control = self.report["minimal_control"]
        self.assertEqual(control["triples"], ((0, 1, 2), (0, 1, 3), (2, 3, 4)))
        self.assertEqual(control["direct_vs_via_zero"], (1, 0))
        self.assertEqual(control["liftable_control_direct_vs_via_zero"], (0, 0))
        self.assertTrue(control["both_jammed"])
        self.assertTrue(control["local_but_no_lift"])

    def test_fano_sector_and_component_enumeration(self):
        r = self.report["fano"]
        self.assertEqual((r["links"], r["cycle_rank"], r["local_check_rank"],
                          r["local_states"], r["gradient_states"]), (21, 15, 7, 16384, 64))
        self.assertEqual(r["sector_size_histogram"], {64: 256})
        self.assertEqual(r["jam_counts_per_sector"], {0: 1, 5: 21, 7: 42, 8: 24, 9: 140, 12: 28})
        self.assertTrue(r["only_gradient_sector_jam_free"])
        self.assertEqual(r["component_sizes"], {1: 2187, 2: 224, 3: 49, 5: 189,
                                                6: 644, 7: 927, 8: 288})
        self.assertEqual((r["line_cut_span_rank"], r["unconditional_move_packets"]), (3, 2048))
        self.assertTrue(r["every_transition_preserves_holonomy"])

    def test_raw_complement_quotient_and_conditional_native_readout(self):
        r = self.report["clock"]
        self.assertEqual(r["global_shapes"], {"C3": 7, "K1,4": 7, "K1,7": 1})
        self.assertEqual(r["raw_shape_to_quotient"], {"C6->C3": 7, "K1,4->K1,4": 14,
                                                      "K1,7->K1,7": 2})
        self.assertEqual(r["raw_components_fixed_by_complement"], 7)
        self.assertEqual(r["clock_states_by_persistent_vertex"], {i: 3 for i in range(7)})
        self.assertEqual(r["all_clock_events_changing_readiness"], 42)
        self.assertEqual(r["triangles_with_no_snapshot_binary_phase"], 7)
        self.assertEqual(r["isolated_triangle"], {"enabled": True, "unchanged": True})
        self.assertEqual(r["least_greatest_firings_seen_by_fixed_clock_reference"], (2, 2))

    def test_fano_no_jam_is_a_preparation_property(self):
        r = self.report["fano"]
        self.assertEqual(r.get("active_states"), 16384 - 3**7)
        self.assertIs(r.get("active_moves_have_enabled_inverse"), True)
        self.assertEqual(r.get("links_toggled_per_enabled_move"), [12])
        self.assertEqual(r.get("extra_cycle_checks_for_global_lift"), 8)

    def test_overlapping_offers_transmit_readiness_without_an_absolute_reference(self):
        c = self.report.get("overlap_control", {})
        self.assertEqual(c.get("triples"), ((0, 1, 2), (1, 2, 3)))
        self.assertIs(c.get("reference_offer_stutters_before_first"), True)
        self.assertIs(c.get("reference_offer_changes_state_after_first"), True)
        self.assertTrue(c.get("first_offer_changes_only_links_to_reference"))
