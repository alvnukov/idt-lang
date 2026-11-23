import json
import subprocess
import sys
import unittest
from fractions import Fraction as F

from scripts.probe_weak_parity_reversal import (
    Cell,
    IsotropicCalibrator,
    calibration_check,
    estimate,
    fixture_control,
    relabel,
    spatial_parity,
    synthetic_table,
)


class WeakParityReversal(unittest.TestCase):
    def test_background_subtraction_and_per_cell_exposure(self) -> None:
        cells = ((Cell(25, 7, 2), Cell(34, 4, 5)), (Cell(19, 1, 3), Cell(18, 2, 4)))
        report = estimate(cells)
        self.assertEqual(report.corrected_rates, ((F(9), F(6)), (F(6), F(4))))
        self.assertEqual(report.ratio, F(1))
        self.assertEqual(report.exact_contrast, F(0))
        self.assertTrue(report.matches_contrast(F(0)))

    def test_invalid_or_missing_cells_are_inconclusive_not_null(self) -> None:
        good = Cell(5, 1, 2)
        bad_cells = (
            (None, "missing_cell"),
            (Cell(None, 0, 1), "missing_input"),
            (Cell(5, None, 1), "missing_input"),
            (Cell(5, 0, None), "missing_input"),
            (Cell(5, 0, 0), "nonpositive_live_time"),
            (Cell(5, 0, -1), "nonpositive_live_time"),
            (Cell(5, 5, 1), "nonpositive_net_count"),
            (Cell(4, 5, 1), "nonpositive_net_count"),
            (Cell(-1, 0, 1), "negative_observed_or_background"),
            (Cell(5, -1, 1), "negative_observed_or_background"),
        )
        for invalid, reason in bad_cells:
            with self.subTest(invalid=invalid):
                report = estimate(((good, invalid), (good, good)))
                self.assertEqual(report.status, "inconclusive")
                self.assertEqual(report.problems, {"d+s-": reason})
                self.assertIsNone(report.ratio)
                self.assertIsNone(report.exact_contrast)
                self.assertIsNone(report.approximate_contrast)
                self.assertFalse(report.matches_contrast(F(0)))

    def test_non_square_and_extreme_ratios_use_exact_checks(self) -> None:
        one = Cell(1, 0, 1)
        report = estimate(((Cell(2, 0, 1), one), (one, one)))
        self.assertEqual(report.ratio, F(2))
        self.assertIsNone(report.exact_contrast)
        approximation = report.approximate_contrast
        if approximation is None:
            self.fail("missing approximate rendering of an irrational contrast")
        self.assertAlmostEqual(approximation, (1 - 2**0.5) / (1 + 2**0.5))
        self.assertFalse(report.matches_contrast(F(1, 5)))

        extreme = estimate(((Cell(10**500, 0, 1), one), (one, one)))
        self.assertEqual(extreme.ratio, F(10**500))
        self.assertEqual(extreme.exact_contrast, F(1 - 10**250, 1 + 10**250))
        self.assertEqual(extreme.approximate_contrast, -1.0)
        self.assertFalse(extreme.matches_contrast(F(-1)))
        mild = estimate(((Cell(10**25 + 1, 0, 1), one), (one, Cell(10**25, 0, 1))))
        self.assertIsNotNone(mild.approximate_contrast)
        self.assertLess(mild.approximate_contrast or 0, 0)

    def test_exact_controls_and_label_reversal(self) -> None:
        expected = (
            (F(0), ((600, 400), (300, 200))),
            (F(1, 5), ((480, 480), (360, 160))),
            (F(-1, 5), ((720, 320), (240, 240))),
        )
        for contrast, counts in expected:
            with self.subTest(contrast=contrast):
                cells = synthetic_table(contrast)
                self.assertEqual(
                    tuple(
                        tuple(
                            cell.observed - cell.background
                            for cell in row
                            if cell is not None
                            and cell.observed is not None
                            and cell.background is not None
                        )
                        for row in cells
                    ),
                    counts,
                )
                base = estimate(cells)
                self.assertEqual(base.status, "evaluated")
                self.assertEqual(base.exact_contrast, contrast)
                self.assertTrue(base.matches_contrast(contrast))
                for flip_d, flip_s in ((True, False), (False, True), (True, True)):
                    toggled = estimate(relabel(cells, flip_d=flip_d, flip_s=flip_s))
                    self.assertTrue(
                        toggled.matches_contrast(
                            -contrast if flip_d ^ flip_s else contrast
                        )
                    )

    def test_nonfactorizing_counterfeit_and_calibrator_requirements(self) -> None:
        delta = F(1, 5)
        candidate = synthetic_table(delta)
        counterfeit = synthetic_table(F(0), delta)
        self.assertEqual(counterfeit, candidate)
        self.assertTrue(estimate(counterfeit).matches_contrast(delta))
        self.assertEqual(calibration_check(None).status, "inconclusive")
        self.assertEqual(
            calibration_check(IsotropicCalibrator(counterfeit, False)).status,
            "inconclusive",
        )
        self.assertEqual(
            calibration_check(IsotropicCalibrator(counterfeit, True)).status,
            "detected_nonzero_calibrator_contrast",
        )
        self.assertEqual(
            calibration_check(IsotropicCalibrator(synthetic_table(F(0)), True)).status,
            "zero_calibrator_contrast_in_these_cells",
        )
        missing = ((None, None), (None, None))
        self.assertEqual(
            calibration_check(IsotropicCalibrator(missing, True)).status, "inconclusive"
        )

    def test_fixture_reversal_separates_channels_only_in_stated_model(self) -> None:
        self.assertEqual(spatial_parity(1, -1, 1), (-1, -1, -1))
        self.assertIsNone(fixture_control(F(3, 10), F(1, 10), assume_additive=False))
        mixed = fixture_control(F(3, 10), F(1, 10), assume_additive=True)
        self.assertEqual(mixed, (F(1, 5), F(1, 10)))
        self.assertEqual(
            fixture_control(F(1, 5), F(1, 5), assume_additive=True), (F(1, 5), F(0))
        )
        self.assertEqual(
            fixture_control(F(1, 5), F(-1, 5), assume_additive=True), (F(0), F(1, 5))
        )

    def test_cli_replays_exact_menu_checks_without_physical_status_upgrade(
        self,
    ) -> None:
        argv = [sys.executable, "-m", "scripts.probe_weak_parity_reversal"]
        first = subprocess.run(argv, check=False, capture_output=True, text=True)
        self.assertEqual(first.returncode, 0, first.stderr)
        second = subprocess.run(argv, check=True, capture_output=True, text=True)
        self.assertEqual(first.stdout, second.stdout)
        report = json.loads(first.stdout)
        menu = report["candidate_bridge"]
        self.assertEqual(menu["status"], "not_evaluable")
        self.assertIsNone(menu["predicted_a0"])
        self.assertFalse(menu["menu_reversal_is_physical_parity"])
        self.assertEqual(menu["basis_pairs"], 256)
        self.assertEqual(menu["selected_eigenvalue"], {"H": -1, "D": 1})
        self.assertEqual(menu["signed_coefficients_on_sample"], [2, -2])
        self.assertEqual(menu["positive_counts_on_same_sample"], [2, 2])
        self.assertEqual(
            [
                case["labels_reversed"]["none"]["exact_contrast"]
                for case in report["synthetic_controls"]
            ],
            ["0", "1/5", "-1/5"],
        )
        self.assertEqual(
            report["joint_efficiency_control"]["without_matched_calibrator"],
            "inconclusive",
        )
        self.assertTrue(report["joint_efficiency_control"]["same_cells_as_signal_only"])
        self.assertEqual(
            report["fixture_control"]["chi_times_S_dot_p_before_after"], [1, 1]
        )
        self.assertFalse(report["empirical_metadata_is_event_data"])
        self.assertEqual(
            [
                (row["a0"], row["stat"], row["syst"])
                for row in report["empirical_metadata"]
            ],
            [("-0.11985", "0.00017", "0.00012"), ("-0.12054", "0.00044", "0.00068")],
        )


if __name__ == "__main__":
    unittest.main()
