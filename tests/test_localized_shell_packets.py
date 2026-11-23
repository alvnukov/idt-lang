"""Finite controls for localization, including non-identifying preparations."""

import unittest
from functools import cache

from scripts import probe_localized_shell_packets as packet


@cache
def report() -> packet.Report:
    return packet.localized_shell_packets()


class LocalizedPacketsTest(unittest.TestCase):
    def test_raw_singleton_component_equals_incidence_subdivision(self):
        for name, n in (
            ("cube", 8),
            ("prism_c5", 10),
            ("petersen", 10),
            ("heawood", 14),
        ):
            with self.subTest(name=name):
                row = report().orbits[name]
                self.assertEqual(row.rule, 32)
                self.assertEqual(
                    (row.states, row.undirected_events), (5 * n // 2, 3 * n)
                )
                self.assertEqual(row.recovered_matchings, row.states)
                self.assertEqual(row.ordered_distances, n * n)
                self.assertEqual(row.metrics[0], (0, 0, 0, 0))
                for d, first_local, first_free, singleton_time in row.metrics[1:]:
                    self.assertEqual(
                        (first_local, first_free, singleton_time), (2 * d - 1, d, 2 * d)
                    )
        self.assertEqual(report().orbits["k4"].rule, 2)

    def test_all_256_rules_scanned_against_all_required_and_forbidden_events(self):
        scans = report().scans
        for name, count in {
            "cube": 32,
            "prism_c5": 16,
            "petersen": 64,
            "k4": 128,
            "k33": 0,
            "triangle_prism": 0,
            "heawood": 64,
        }.items():
            self.assertEqual(len(scans[name].rules), count, name)
        self.assertNotIn(32, scans["triangle_prism"].rules)
        self.assertNotIn(32, scans["k4"].rules)
        self.assertIn(2, scans["k4"].rules)
        for name in ("k4", "k33", "triangle_prism"):
            self.assertIsNotNone(scans[name].flag32_mismatch)
        self.assertIsNone(scans["cube"].flag32_mismatch)

    def test_all_upper_cuts_and_alternate_two_layer_preparations(self):
        result = report()
        self.assertEqual(result.common_cut_aliases, (32, 33, 48, 49))
        for name, n in (("cube", 8), ("prism_c5", 10), ("petersen", 10)):
            row = result.upper_cuts[name]
            self.assertEqual(row.states, 2**n)
            self.assertEqual(row.visible_flags, 238)
        splits = {r.extra: r.firing_rules for r in result.cube_interventions}
        self.assertEqual(splits, {8: (48, 49), 10: (33, 49)})

    def test_multiseed_can_grow_a_three_vertex_component(self):
        witness = report().three_roots
        self.assertEqual(tuple(map(len, witness.subsets)), (3, 4, 5))
        self.assertEqual(witness.component_sizes[0], (1, 1, 1))
        self.assertEqual(witness.component_sizes[-1], (1, 1, 3))

    def test_two_roots_need_not_remain_independent_even_after_clean_first_step(self):
        results = report().two_roots
        far = results["prism_c6_far"]
        self.assertEqual(
            (far.distance, len(far.initial_offers), far.raw_component), (4, 6, 489)
        )
        self.assertEqual(far.initial_offers, far.union_solo_offers)
        self.assertIn((2, 5), far.component_profiles)
        self.assertEqual(len(far.shortest_enlargement or ()), 2)
        self.assertEqual(results["cube_antipodes"].raw_component, 1)
        self.assertEqual(results["k33_twins"].raw_component, 1)
        near = results["cube_near"]
        self.assertEqual(
            (len(near.union_solo_offers), len(near.initial_offers), near.raw_component),
            (4, 2, 3),
        )

    def test_decoder_has_no_access_to_supplied_layer_or_matching(self):
        base = packet.fixtures()["cube"]
        raw, rungs = packet.lift(base)
        n = len(base.stars)
        image = tuple((3 * v + 5) % (2 * n) for v in range(2 * n))
        scrambled = packet.Incidence.from_edges(
            2 * n, ((image[u], image[v]) for u, v in raw.edge_bits), 4
        )
        for vertices in ((0,), (0, 1)):
            matching = sum(
                scrambled.edge_bits[packet.edge(image[v], image[v + n])]
                for v in range(n)
            )
            state = scrambled.prepare(matching, (image[v] for v in vertices))
            decoded, background = packet.decode(scrambled, state)
            self.assertEqual(background, matching)
            self.assertEqual(decoded, frozenset(image[v] for v in vertices))
        self.assertEqual(len(rungs), n)
