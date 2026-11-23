"""Raw-edge controls for the conditional facilitated signal metric."""

import unittest
from dataclasses import asdict
from itertools import product

from scripts import probe_facilitated_forest_signal as metric
from scripts.probe_anonymous_shell_rules import local_image


class FacilitatedSignalMetricTest(unittest.TestCase):
    report: metric.SignalMetricReport

    @classmethod
    def setUpClass(cls) -> None:
        cls.report = metric.facilitated_signal_metric()

    def test_raw_singletons_trees_and_first_arrivals(self) -> None:
        rows = self.report.carriers
        self.assertEqual(
            {
                name: (row.singleton_raw_states, row.singleton_raw_edges)
                for name, row in rows.items()
            },
            {
                "k4": (10, 12),
                "k33": (39, 72),
                "triangle_prism": (33, 54),
                "cube": (100, 192),
                "prism_c5": (275, 600),
                "prism_c6": (678, 1608),
            },
        )
        for row in rows.values():
            n = row.carrier_vertices
            self.assertEqual(row.ordered_singleton_and_arrival_comparisons, n * n)
            self.assertEqual(
                row.relabelled_raw_states,
                row.singleton_raw_states + row.pair_raw_states,
            )
            self.assertEqual(row.preparation_added_marks, 2)
            self.assertEqual(row.enabled_background_centers, 0)
            self.assertGreater(row.checked_fundamental_cycles, 0)
        self.assertEqual(rows["k33"].singleton_event_histogram, ((2, 9), (4, 6)))
        self.assertEqual(
            rows["triangle_prism"].singleton_event_histogram, ((2, 9), (4, 6))
        )

    def test_pair_raw_sectors_and_infinities_not_fixed_by_metric_histogram(
        self,
    ) -> None:
        rows = self.report.carriers
        self.assertEqual(
            {
                name: (row.independent_pairs, row.pair_raw_states)
                for name, row in rows.items()
            },
            {
                "k4": (0, 0),
                "k33": (6, 6),
                "triangle_prism": (6, 12),
                "cube": (16, 78),
                "prism_c5": (30, 355),
                "prism_c6": (48, 1347),
            },
        )
        self.assertEqual(rows["k33"].pair_sector_raw_sizes, (1,) * 6)
        self.assertEqual(rows["k33"].unreachable_ordered_pair_comparisons, 30)
        self.assertEqual(rows["triangle_prism"].pair_sector_raw_sizes, (12,))
        self.assertEqual(rows["triangle_prism"].unreachable_ordered_pair_comparisons, 0)
        for row in rows.values():
            self.assertEqual(row.ordered_pair_comparisons, row.independent_pairs**2)

    def test_matching_background_is_a_resource_on_same_graph(self) -> None:
        control = self.report.same_graph_matching_control
        self.assertEqual(control.vertical_matching_root_component, (10, 4))
        self.assertEqual(
            control.root_component_histogram,
            ((10, 4, 1), (30, 8, 6), (40, 8, 3), (42, 8, 6)),
        )
        self.assertEqual(control.all_matchings, 16)
        self.assertEqual(control.ordered_two_event_comparisons, 16 * 8 * 7)
        self.assertEqual(
            control.additional_4regular_graph_matchings,
            (("k44", 24, 24 * 8 * 7), ("octahedron", 8, 8 * 6 * 5)),
        )

    def test_raw_local_action_matches_frozen_rule_255(self) -> None:
        for scores in product(range(4), repeat=4):
            for marked in range(16):
                expected = local_image(255, scores, marked)
                # The same four bits can occupy arbitrary places in the raw word.
                ports = (2, 8, 16, 256)
                remote_mark = 1024
                packed = remote_mark + sum(
                    p for i, p in enumerate(ports) if marked >> i & 1
                )
                after = remote_mark + sum(
                    p for i, p in enumerate(ports) if expected >> i & 1
                )
                self.assertEqual(
                    metric.half_filled_star_step(packed, sum(ports)), after
                )

    def test_report_names_external_resources_without_claiming_dimension(self) -> None:
        record = asdict(self.report)
        self.assertIn("external", record["scope"])
        self.assertIn("not", record["scope"])
        self.assertIn("dimension", record["scope"])
