"""Independent exact targets and deliberately failing scientific controls."""

from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as F

from theory_experiments.physics_screen import (
    ChiralSpectrum,
    QuantumReadout,
    WeylField,
    evaluate_qm,
    evaluate_sm,
    parse_physics,
    physics_controls,
    probabilities,
    scope,
)
from theory_experiments.primitive_screen import Check, Limits, aggregate_status


def indexed(checks: tuple[Check, ...]) -> dict[str, Check]:
    return {check.id: check for check in checks}


class QuantumScreenTests(unittest.TestCase):
    def test_born_exact_finite_targets(self) -> None:
        checks = evaluate_qm(QuantumReadout("born", 1), Limits())
        self.assertEqual(aggregate_status(checks), "no_counterexample_within_bounds")
        self.assertEqual([check.checked for check in checks], [1, 5, 2, 1, 4, 1])
        self.assertTrue(all(check.assumptions for check in checks))

    def test_complex_amplitude_phase_and_common_scale(self) -> None:
        amplitudes = ((F(3), F(4)), (F(0), F(5)))
        for power in range(1, 5):
            self.assertEqual(probabilities(amplitudes, power), (F(1, 2), F(1, 2)))
            self.assertEqual(probabilities(tuple((7*r, 7*i) for r, i in amplitudes), power),
                             probabilities(amplitudes, power))
        with self.assertRaises(ValueError):
            probabilities(((F(), F()),), 1)

    def test_fourth_power_specific_counterexamples(self) -> None:
        checks = indexed(evaluate_qm(QuantumReadout("fourth", 2), Limits()))
        expected = {"qm_born_reference": "-1008/8425",
                    "qm_phase_interference": "12/85",
                    "qm_local_no_signalling": "-144/481"}
        for name, value in expected.items():
            with self.subTest(name=name):
                check = checks[name]
                self.assertEqual(check.status, "counterexample")
                assert check.witness is not None
                self.assertEqual(check.witness["actual"], value)
        self.assertEqual(checks["qm_phase_interference"].checked, 5)
        self.assertEqual(checks["qm_tsirelson_bound"].status, "counterexample")
        self.assertEqual(checks["qm_projective_repeatability"].status, "no_counterexample_within_bounds")

    def test_short_budget_preserves_incomplete_scope(self) -> None:
        checks = evaluate_qm(QuantumReadout("born", 1), Limits(max_cases=1))
        self.assertEqual(aggregate_status(checks), "inconclusive")
        self.assertEqual(indexed(checks)["qm_phase_interference"].planned, 5)

    def test_rejects_invented_outputs_and_invalid_powers(self) -> None:
        for value in (0, 5, True, "1", 1.0):
            with self.subTest(value=value), self.assertRaises(ValueError):
                parse_physics({"id": "x", "family": "qm_readout", "norm_power": value})
        with self.assertRaises(ValueError):
            parse_physics({"id": "x", "family": "qm_readout", "norm_power": 1, "p": "1/2"})


class StandardModelScreenTests(unittest.TestCase):
    def reference(self) -> ChiralSpectrum:
        candidate = physics_controls()["sm_reference"]
        assert isinstance(candidate, ChiralSpectrum)
        return candidate

    def test_reference_cancels_all_supported_anomalies(self) -> None:
        checks = evaluate_sm(self.reference(), Limits())
        self.assertEqual(len(checks), 8)
        self.assertEqual(aggregate_status(checks), "no_counterexample_within_bounds")
        self.assertEqual(sum(abs(f.color)*f.weak*f.copies for f in self.reference().fields), 45)

    def test_bad_hypercharge_fails_independent_cubic_and_linear_sums(self) -> None:
        candidate = physics_controls()["sm_bad_charge"]
        assert isinstance(candidate, ChiralSpectrum)
        checks = indexed(evaluate_sm(candidate, Limits()))
        for key, expected in (("sm_y_cubic", "21"), ("sm_mixed_gravitational_y", "3")):
            witness = checks[key].witness
            assert witness is not None
            self.assertEqual(witness["actual"], expected)
        self.assertEqual(checks["sm_su3_cubic"].status, "no_counterexample_within_bounds")

    def test_one_generation_is_anomaly_free_not_three_generations(self) -> None:
        candidate = physics_controls()["sm_one_generation"]
        assert isinstance(candidate, ChiralSpectrum)
        checks = evaluate_sm(candidate, Limits())
        self.assertTrue(all(check.status == "no_counterexample_within_bounds" for check in checks[:6]))
        self.assertEqual(indexed(checks)["sm_minimal_multiplet_content"].status, "counterexample")

    def test_color_degeneracy_and_witten_parity(self) -> None:
        checks = indexed(evaluate_sm(ChiralSpectrum("q_only", (
            WeylField("q", 3, 2, F(1, 6), 1),), F(1, 2)), Limits()))
        expected = {"sm_su3_cubic": "2", "sm_su3_squared_y": "1/3",
                    "sm_su2_squared_y": "1/2", "sm_y_cubic": "1/36",
                    "sm_mixed_gravitational_y": "1", "sm_witten_doublets": "1"}
        for key, value in expected.items():
            witness = checks[key].witness
            assert witness is not None
            self.assertEqual(witness["actual"], value)

    def test_antifundamental_cubic_sign_not_mixed_sign(self) -> None:
        checks = indexed(evaluate_sm(ChiralSpectrum("uc_only", (
            WeylField("uc", -3, 1, F(-2, 3), 1),), F(1, 2)), Limits()))
        for key, value in (("sm_su3_cubic", "-1"), ("sm_su3_squared_y", "-2/3")):
            witness = checks[key].witness
            assert witness is not None
            self.assertEqual(witness["actual"], value)

    def test_target_is_independent_of_labels_order_and_split_multiplicities(self) -> None:
        candidate = self.reference()
        fields = tuple(replace(field, label=f"renamed{i}")
                       for i, field in enumerate(reversed(candidate.fields)))
        first = fields[0]
        fields = (replace(first, copies=1), replace(first, label="split", copies=2)) + fields[1:]
        self.assertEqual(aggregate_status(evaluate_sm(replace(candidate, fields=fields), Limits())),
                         "no_counterexample_within_bounds")

    def test_higgs_charges_and_neutrino_gap(self) -> None:
        candidate = self.reference()
        details = scope(candidate)
        untested = details["untested"]
        assert isinstance(untested, list)
        self.assertIn("neutrino_mass_mechanism", untested)
        self.assertEqual(details["derived_electric_charges"], [
            {"field": "q", "copies": 3, "color_dimension": 3, "charges": ["2/3", "-1/3"]},
            {"field": "uc", "copies": 3, "color_dimension": 3, "charges": ["-2/3"]},
            {"field": "dc", "copies": 3, "color_dimension": 3, "charges": ["1/3"]},
            {"field": "l", "copies": 3, "color_dimension": 1, "charges": ["0", "-1"]},
            {"field": "ec", "copies": 3, "color_dimension": 1, "charges": ["1"]},
        ])
        checks = indexed(evaluate_sm(replace(candidate, higgs_hypercharge=F()), Limits()))
        self.assertEqual(checks["sm_neutral_higgs_lower_component"].status, "counterexample")

    def test_parser_rejects_unsupported_representations_and_float_charges(self) -> None:
        for color, weak, hypercharge in ((8, 1, "0"), (3, 3, "0"), (1, 1, 0.5), (True, 1, "0")):
            with self.subTest(color=color, weak=weak, hypercharge=hypercharge), self.assertRaises(ValueError):
                parse_physics({"id": "bad", "family": "sm_chiral", "higgs_hypercharge": "1/2",
                               "fields": [{"label": "x", "color": color, "weak": weak,
                                           "hypercharge": hypercharge, "copies": 1}]})
        for candidate in physics_controls().values():
            self.assertEqual(parse_physics(candidate.specification()), candidate)


if __name__ == "__main__":
    unittest.main()
