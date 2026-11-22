import math
import unittest

from scripts.probe_z_width_data_replay import agrees_with_publication, read_receipt, replay


class ZWidthDataReplayTests(unittest.TestCase):
    def test_updated_rounded_inputs_reproduce_table_9(self):
        result = replay(read_receipt())
        row = result["lep_updated"]
        self.assertAlmostEqual(row["nb_per_gev_minus_two"], 389379.3722, places=3)
        self.assertAlmostEqual(row["replayed_n_eff"], 2.99636985, places=7)
        self.assertAlmostEqual(row["replayed_error"], 0.00740573, places=7)
        self.assertTrue(agrees_with_publication(result))
        self.assertNotEqual(round(row["replayed_n_eff"], 4), row["reported"]["value"])
        self.assertEqual(result["lep_original"]["reported"], {"value": 2.9840, "error": 0.0082})
        self.assertEqual(round(result["lep_original"]["rounded_ratio_quotient"], 4), 2.9846)

    def test_unit_label_and_numerical_conversion(self):
        data = read_receipt()
        sigma = data["lep_updated"]["fit_inputs"]["sigma_had_nb"]
        sigma["unit"] = "pb"
        with self.assertRaisesRegex(ValueError, "unit"):
            replay(data)
        sigma["unit"] = "nb"
        sigma["value"] *= 1000  # pb number accidentally entered under an nb heading
        self.assertFalse(agrees_with_publication(replay(data)))

    def test_reversing_peak_cross_section_ratio_correlation_breaks_error_replay(self):
        data = read_receipt()
        corr = data["lep_updated"]["fit_inputs"]["correlations"]
        corr[1][2] = corr[2][1] = -corr[1][2]
        self.assertFalse(agrees_with_publication(replay(data)))

    def test_external_single_species_ratio_derivative(self):
        data = read_receipt()
        baseline = replay(data)["lep_updated"]
        theory = data["lep_updated"]["r_nu"]
        theory["value"] += 0.000001
        difference = replay(data)["lep_updated"]["replayed_n_eff"] - baseline["replayed_n_eff"]
        estimate = abs(difference / 0.000001) * theory["error"]
        self.assertAlmostEqual(estimate, baseline["error_component_external_r_nu"], places=9)
        theory["value"] -= 0.000001
        theory["error"] = 0
        fit_only = replay(data)["lep_updated"]["replayed_error"]
        self.assertAlmostEqual(math.hypot(fit_only, estimate), baseline["replayed_error"], places=9)

    def test_separate_measurement_and_no_combined_constraint(self):
        data = read_receipt()
        result = replay(data)
        self.assertEqual(set(result), {"lep_original", "lep_updated", "atlas", "mode"})
        self.assertEqual(result["mode"], "descriptive_only_no_combination")
        self.assertEqual(result["atlas"]["reported_mev"], {"value": 506, "stat_error": 2, "syst_error": 12})
        data["lep_original"]["sample"] = "hypothetical_other_run"
        with self.assertRaisesRegex(ValueError, "share events"):
            replay(data)
        data = read_receipt()
        data["atlas"]["normalization"] = "independent"
        with self.assertRaisesRegex(ValueError, "external"):
            replay(data)


if __name__ == "__main__":
    unittest.main()
