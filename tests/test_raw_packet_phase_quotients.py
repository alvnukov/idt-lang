import unittest
from collections import Counter
from fractions import Fraction as F

from scripts.probe_raw_packet_phase_quotients import (
    pointwise_histogram,
    run_probe,
)


class RawPacketPhaseQuotients(unittest.TestCase):
    def test_six_positive_partitions_have_distinct_rooted_cells(self) -> None:
        report = run_probe().quotient
        self.assertEqual(report.raw_addresses, 256)
        self.assertEqual(
            {name: (row.cells, row.cell_size) for name, row in report.census.items()},
            {
                "I": (256, 1),
                "S": (128, 2),
                "H": (64, 4),
                "D": (64, 4),
                "join": (32, 8),
                "independent": (16, 16),
            },
        )
        self.assertEqual(len(report.distinct_pairs), 15)
        self.assertEqual(
            len({(row.left, row.right) for row in report.distinct_pairs}), 15
        )
        self.assertTrue(all(row.equal_roots == 0 for row in report.distinct_pairs))
        self.assertEqual(report.generator_order, ("S", "H", "D", "L"))
        self.assertEqual(report.generator_root_checks, 6 * 4 * 256)
        self.assertEqual(
            report.signatures,
            dict(
                zip(
                    ("I", "S", "H", "D", "join", "independent"),
                    ("0000", "1000", "1100", "1010", "1110", "1111"),
                    strict=True,
                )
            ),
        )
        self.assertEqual(report.matchings_commuting_with_w, 6)
        self.assertEqual(report.descended_matchings, dict.fromkeys(report.census, 6))
        for name, row in report.census.items():
            self.assertEqual(row.raw_local_address_constant, (name == "I", name == "I"))

    def test_exact_pushforward_is_not_positive_counting(self) -> None:
        report = run_probe().contrast
        self.assertEqual(report.basis_pairs, 256)
        self.assertEqual(report.odd_action_checks, {"H=-K": 256, "D=K": 256})
        self.assertEqual(report.pushforward_checks, {"H": 256, "D": 256})
        self.assertEqual(report.selected_eigenvalue, {"H": -1, "D": 1})
        self.assertEqual(report.mirror_checks, {"left": 256, "right": 256})
        self.assertEqual(report.positive_count_controls, {"H": 256, "D": 256})
        self.assertEqual(report.signed_coefficients_on_sample, (2, -2))
        self.assertEqual(report.positive_counts_on_same_sample, (2, 2))

    def test_complete_deterministic_network_tables_have_pointwise_ceiling(self) -> None:
        counts = {-6: 256, -2: 768, 2: 768, 6: 256}
        self.assertEqual(pointwise_histogram(), Counter(counts))
        report = run_probe().network
        self.assertEqual(report.pointwise_tables, 2048)
        self.assertEqual(report.pointwise_histogram, counts)
        self.assertEqual(report.normalized_mixture_ceiling, 6)
        self.assertFalse(report.requires_independent_source_measures)

    def test_physical_contact_coarse_readers_saturate_on_complete_mixtures(
        self,
    ) -> None:
        report = run_probe().network
        for name in ("H", "D"):
            row = report.contact_completions[name]
            self.assertEqual(row.class_rails, 64)
            self.assertEqual(row.relabel_class_counts, (16, 16, 16, 16))
            self.assertEqual(row.outcome_address_counts, (64, 64, 64, 64))
            self.assertEqual(row.exact_forward_records, 256)
            self.assertEqual(row.setting_pairs, 18)
            self.assertEqual(row.setting_mass, ("1",))
            self.assertEqual(row.score, "6")

    def test_leak_and_postselection_are_not_complete_setting_independent_readers(
        self,
    ) -> None:
        report = run_probe().network
        self.assertEqual(report.leaky_score, "12")
        self.assertEqual(report.leaky_setting_mass, ("1",))
        self.assertGreater(report.leaky_distinct_b_outcomes, 1)
        self.assertFalse(report.leaky_in_completion_class)
        self.assertEqual(report.postselected_score, "12")
        self.assertEqual(report.original_unfiltered_score, "0")
        self.assertEqual(F(report.postselected_acceptance), F(1, 2))
        self.assertGreater(report.postselected_distinct_acceptance_sets, 1)
        self.assertFalse(report.postselected_in_completion_class)
        self.assertIsNone(report.unassigned_discard_score)


if __name__ == "__main__":
    unittest.main()
