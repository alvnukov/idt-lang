"""Exact neutral-current traces and deliberately non-inferential observation comparisons."""

from __future__ import annotations

import hashlib
import unittest
from copy import deepcopy
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from theory_experiments import neutral_current_width as nc
from theory_experiments.primitive_screen import Limits


def diagonal(*values):
    return {"id": "test_current", "family": "neutral_current_width",
            "species": [f"nu{i}" for i in range(len(values))],
            "mass_regime": "all_negligible", "bridge": "standard_invisible_left_current_only",
            "left_current_matrix": [[[v if i == j else "0", "0"] for j in range(len(values))]
                                    for i, v in enumerate(values)]}


def predict(raw, maximum=144):
    return nc.predict_neutral_current_width(nc.parse_neutral_current_width(raw), Limits(max_cases=maximum))


class NeutralCurrentWidthTest(unittest.TestCase):
    def test_exact_trace_blind_to_neutral_count(self):
        three = diagonal("1", "1", "1")
        four = diagonal("1", "1", "3/5", "4/5")
        for raw, cost in ((three, 9), (four, 16)):
            result = predict(raw)
            self.assertEqual(result["effective_species"], "3")
            self.assertEqual(result["budget"]["checked"], cost)
            self.assertEqual(len(result["ordered_channels"]), cost)

    def test_rotated_active_sterile_projection_includes_both_off_diagonals(self):
        # Real rotation of diag(1,1,1,0); the third active column is (0,0,3/5,4/5).
        raw = diagonal("1", "1", "9/25", "16/25")
        without_off_diagonals = predict(raw)
        matrix = raw["left_current_matrix"]
        matrix[2][3] = ["12/25", "0"]
        matrix[3][2] = ["12/25", "0"]
        result = predict(raw)
        self.assertEqual(result["effective_species"], predict(diagonal("1", "1", "1", "0"))["effective_species"])
        weights = {(c["particle"], c["antiparticle"]): c["squared_coupling"] for c in result["ordered_channels"]}
        self.assertEqual(len(weights), 16)
        self.assertEqual((weights["nu2", "nu3"], weights["nu3", "nu2"]), ("144/625", "144/625"))
        self.assertEqual(without_off_diagonals["effective_species"], "1587/625")
        # Rephasing the sterile column moves the mixing entirely to the imaginary part.
        matrix[2][3] = ["0", "12/25"]
        matrix[3][2] = ["0", "-12/25"]
        self.assertEqual(predict(raw), result)

    def test_complex_conjugation_and_modulus(self):
        raw = diagonal("0", "0")
        raw["left_current_matrix"][0][1] = ["3/5", "4/5"]
        raw["left_current_matrix"][1][0] = ["3/5", "-4/5"]
        self.assertEqual(predict(raw)["effective_species"], "2")
        raw["left_current_matrix"][1][0] = ["3/5", "4/5"]
        with self.assertRaisesRegex(ValueError, "Hermitian"):
            nc.parse_neutral_current_width(raw)

    def test_bounds_grammar_and_shapes(self):
        valid = diagonal("1", "-2/3")
        model = nc.parse_neutral_current_width(valid)
        self.assertEqual(model, nc.parse_neutral_current_width(model.specification()))
        for value in (0, True, 1.2, "1e0", "1.0", "1/-2", "3/0", "1/1234567890", "1"*10000, None):
            with self.subTest(value=repr(value)[:32]), self.assertRaises(ValueError):
                raw = deepcopy(valid)
                raw["left_current_matrix"][0][0][0] = value
                nc.parse_neutral_current_width(raw)
        for field, value in (("species", []), ("species", ["a"]*13), ("species", ["a","a"]),
                             ("species", ["a",True]), ("left_current_matrix", []),
                             ("left_current_matrix", [[["0","0"]]]*2),
                             ("left_current_matrix", [[["0"], ["0","0"]]]*2),
                             ("mass_regime", True), ("bridge", "relabeled_sm")):
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                nc.parse_neutral_current_width({**valid, field:value})
        raw = diagonal("1")
        raw["left_current_matrix"][0][0][1] = "1/2"
        with self.assertRaisesRegex(ValueError, "Hermitian"):
            nc.parse_neutral_current_width(raw)
        with self.assertRaises(ValueError):
            nc.parse_neutral_current_width({**valid, "fit_to_data": True})
        full = diagonal(*(["1"]*12))
        self.assertEqual(predict(full, 144)["effective_species"], "12")
        self.assertEqual(predict(full, 143)["status"], "inconclusive")

    def test_budget_and_unmapped_routes_do_not_load_data_or_return_estimates(self):
        raw = diagonal("1", "1", "1")
        for inputs, maximum, state in ((raw, 8, "inconclusive"),
                ({**raw, "mass_regime": "threshold_or_unknown"}, 9, "unsupported"),
                ({**raw, "bridge": "unmapped"}, 9, "unsupported")):
            with self.subTest(state=state), patch.object(nc, "_pinned_receipt_bytes", side_effect=AssertionError):
                checks, scope = nc.evaluate_neutral_current_width(nc.parse_neutral_current_width(inputs),
                                                                  Limits(max_cases=maximum))
                self.assertEqual((checks[0].status, checks[0].checked, checks[0].planned), (state, 0, 9))
                self.assertEqual(scope["execution_status"], state)
                self.assertNotIn("effective_species", scope["prediction"])
                self.assertNotIn("ordered_channels", scope["prediction"])
                self.assertNotIn("comparison", scope)

    def test_exact_prediction_precedes_any_data_read(self):
        model = nc.parse_neutral_current_width(diagonal("2"))
        log = []
        predict_original = nc.predict_neutral_current_width
        def observe_prediction(*args):
            pred = predict_original(*args)
            log.append(("predicted", pred["effective_species"]))
            return pred
        def observe_data():
            log.append(("read", None))
            raise ValueError("simulated unavailable data")
        with patch.object(nc, "predict_neutral_current_width", observe_prediction), \
                patch.object(nc, "_pinned_receipt_bytes", observe_data), self.assertRaises(ValueError):
            nc.evaluate_neutral_current_width(model, Limits())
        self.assertEqual(log, [("predicted", "4"), ("read", None)])

    def test_frozen_measurements_keep_their_printed_precision_and_separate_methods(self):
        checks, scope = nc.evaluate_neutral_current_width(nc.parse_neutral_current_width(diagonal("1","1","1")),
                                                          Limits(max_cases=9))
        self.assertEqual(checks[0].status, "no_counterexample_within_bounds")
        self.assertEqual((scope["candidate_verdict"], scope["proof_status"], scope["empirical_status"]),
                         ("not_assessed", "not_attempted", "not_tested"))
        comparison = scope["comparison"]
        lep = comparison["lep_updated"]
        self.assertEqual((lep["printed_effective_species"], lep["printed_quoted_uncertainty"]),
                         ("2.9963", "0.0074"))
        self.assertEqual((lep["measured_minus_predicted"], lep["residual_over_quoted_uncertainty"]),
                         ("-37/10000", "-1/2"))
        self.assertIn("not_an_independent_measurement", comparison["lep_original"])
        atlas = comparison["atlas"]
        obs = atlas["reported_invisible_width_mev"]
        self.assertEqual(tuple(obs[k] for k in ("value","stat_error","syst_error")), ("506", "2", "12"))
        inputs = atlas["calibration"]
        self.assertEqual(inputs["lep_original_gamma_lepton_mev"]["value"], "83.985")
        self.assertEqual(inputs["lep_updated_r_nu"], {"value": "1.99060", "error": "0.00021"})
        one = Fraction("83.985") * Fraction(inputs["lep_updated_r_nu"]["value"])
        self.assertEqual(Fraction(atlas["predicted_invisible_width_mev"]), 3 * one)
        self.assertEqual(Fraction(atlas["measured_minus_predicted_mev"]), 506 - 3 * one)
        self.assertNotIn("significance", atlas)
        far_checks, far = nc.evaluate_neutral_current_width(nc.parse_neutral_current_width(diagonal("12")), Limits())
        self.assertEqual(checks[0].status, far_checks[0].status)
        self.assertEqual(far["candidate_verdict"], "not_assessed")

    def test_changed_receipt_and_changed_loaded_code_fail_closed(self):
        nc.assert_loaded_sources()
        raw = (nc.ROOT / nc.DATA_PATH).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), nc.DATA_SHA256)
        with TemporaryDirectory() as temp, patch.object(nc, "ROOT", Path(temp)):
            path = Path(temp) / nc.DATA_PATH
            path.parent.mkdir(parents=True)
            path.write_bytes(raw + b" ")
            with self.assertRaisesRegex(ValueError, "digest mismatch"):
                nc.assert_loaded_sources()
            with self.assertRaisesRegex(ValueError, "digest mismatch"):
                nc.evaluate_neutral_current_width(nc.parse_neutral_current_width(diagonal("1")), Limits())
        with patch.object(nc, "LOADED_SOURCE_SHA256", "0"*64), self.assertRaisesRegex(ValueError, "source changed"):
            nc.assert_loaded_sources()


if __name__ == "__main__":
    unittest.main()
