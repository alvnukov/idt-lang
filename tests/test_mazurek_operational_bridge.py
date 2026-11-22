"""Pin the labelled raw comparison and guard its exact minimax calculation."""

from __future__ import annotations

import unittest
from fractions import Fraction as F
from itertools import product

from scripts import probe_mazurek_operational_bridge as bridge
from theory_experiments.mazurek_primary import load_counts
from theory_experiments.primitive_screen import object_fields


class MazurekOperationalBridgeTests(unittest.TestCase):
    def test_fixed_lab_mapping_and_preidentified_alternative(self) -> None:
        self.assertEqual(bridge.LAB_DESIGN_ROWS, (0, 3, 4, 1, 2, 5, "+", "-"))
        self.assertEqual(bridge.IDEAL_COUNTS, (
            (4, 1, 1, 2), (0, 3, 3, 2), (1, 4, 1, 2), (3, 0, 3, 2),
            (1, 1, 4, 2), (3, 3, 0, 2), (2, 2, 2, 4), (2, 2, 2, 0),
        ))
        family = bridge.catalog()
        self.assertEqual(family.alternate_counts, bridge.IDEAL_COUNTS)
        self.assertEqual((len(family.fourth_axis), len(family.pole_stock_trine_counts)), (480, 240))
        self.assertEqual(bridge.deterministic_minimax(family, bridge.quarters(bridge.IDEAL_COUNTS)), (F(1, 4), 84))

    def test_factored_minimax_agrees_with_explicit_joint_search(self) -> None:
        frozen = tuple(row[:3] for row in bridge.IDEAL_COUNTS[:6])
        trine = ((1, 2, 3), (2, 2, 2), (4, 2, 0))
        maps = (((2,) * 6, (4, 2, 0)), ((1, 1, 2, 2, 1, 2), (0, 2, 3)))
        family = bridge.Catalog(frozen, trine, maps, bridge.IDEAL_COUNTS)
        ideal = bridge.quarters(bridge.IDEAL_COUNTS)
        observed = (*ideal[:6], (F(1, 3), F(1, 2), F(7, 9), F(17, 20)),
                    (F(6, 7), F(1, 2), F(1, 7), F(4, 19)))
        by_map = []
        for equator, poles in maps:
            fixed = tuple(row + (n,) for row, n in zip(frozen, equator, strict=True))
            assignments = (fixed + (trine[p] + (poles[p],), trine[m] + (poles[m],))
                           for p, m in product(range(len(trine)), repeat=2))
            by_map.append(min(bridge.sup_error(bridge.quarters(table), observed) for table in assignments))
        best = min(by_map)
        self.assertEqual(bridge.deterministic_minimax(family, observed), (best, by_map.count(best)))

    def test_original_sources_disagree_and_are_not_relabeled(self) -> None:
        result = bridge.report(load_counts())
        source = object_fields(result["original_source_orientation"])
        self.assertIs(source["permutation_applied"], False)
        self.assertEqual(source["mismatched_count_cells"], 16)
        self.assertIs(source["first_six_rows_agree"], True)
        self.assertIs(source["fourth_pair_row_exchange_would_reconcile_but_is_not_applied"], True)
        pooled = object_fields(result["per_run_workbook_pooled_counts_as_labelled"])
        aggregate = object_fields(result["aggregate_workbook_counts_as_labelled"])
        for receipt, delta, location in ((pooled, F(100463, 7676254), (7, 0)),
                                         (aggregate, F(7639117, 7640366), (6, 3))):
            with self.subTest(delta=delta):
                self.assertEqual(receipt["delta_to_fixed_ideal_linf"], bridge.exact(delta))
                cells = receipt["max_discrepancy_cells"]
                if not isinstance(cells, list):
                    self.fail("expected discrepancy locations")
                self.assertEqual(len(cells), 1)
                cell = object_fields(cells[0])
                self.assertEqual((cell["row_index"], cell["column_index"]), location)
                self.assertEqual(receipt["deterministic_fixed_center_empirical_minimax_linf"],
                                 bridge.exact(F(1820895, 7673224)))
                self.assertEqual(receipt["number_of_native_analyzer_maps_attaining_minimum"], 6)
                self.assertEqual(receipt["preidentified_exact_ideal_alternate_witness_empirical_linf"],
                                 bridge.exact(delta))
                bounds = object_fields(receipt["fixed_center_rigorous_lower_bounds_from_ideal_gaps"])
                for name, gap in (("deterministic", F(1, 4)), ("random_words", F(7, 71)),
                                  ("random_words_with_component_flips", F(1, 12))):
                    entry = object_fields(bounds[name])
                    self.assertEqual(entry["known_ideal_gap"], bridge.exact(gap))
                    self.assertEqual(entry["signed_gap_minus_delta"], bridge.exact(gap - delta))
                    self.assertEqual(entry["nonnegative_distance_lower_bound"], bridge.exact(max(F(0), gap - delta)))
        polarity = F(29354154085231, 29364638867930)
        self.assertEqual(pooled["fourth_axis_polarity_control_observed_P4_0_minus_P4_1"], bridge.exact(polarity))
        self.assertEqual(aggregate["fourth_axis_polarity_control_observed_P4_0_minus_P4_1"], bridge.exact(-polarity))


if __name__ == "__main__":
    unittest.main()
