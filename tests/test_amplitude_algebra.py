"""Independent native-law controls and regression against lossy source adapters."""

from __future__ import annotations

import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from scripts.archive_existing_primitives import inventory_specifications
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import primitive_screen as primitive
from theory_experiments.amplitude_algebra import (
    SOURCE_BINDINGS,
    AmplitudeAlgebra,
    evaluate_amplitude_algebra,
    parse_amplitude_algebra,
)
from theory_experiments.candidate_history import History
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    aggregate_status,
    load_json,
    object_fields,
    quadratic,
    tensor,
)

SCALAR = AmplitudeAlgebra("scalar", "integer_scalar", 0, 0)
GAUSSIAN = AmplitudeAlgebra("gaussian", "integer_plane", -1, 1)
ROOT = Path(__file__).resolve().parents[1]


def checked(model: AmplitudeAlgebra, limits: Limits | None = None) -> dict[str, Check]:
    return {check.id: check for check in evaluate_amplitude_algebra(model, limits or Limits())[0]}


class AmplitudeAlgebraTests(unittest.TestCase):
    def test_native_operations_match_integer_carriers(self) -> None:
        self.assertEqual(SCALAR.grid(1), ((-1, 0), (0, 0), (1, 0)))
        self.assertEqual(len(GAUSSIAN.grid(1)), 9)
        self.assertEqual(GAUSSIAN.add((2, -3), (-4, 5)), (-2, 2))
        self.assertEqual(GAUSSIAN.multiply((2, -3), (-4, 5)), (7, 22))
        self.assertEqual(GAUSSIAN.weight((7, 22)), 533)
        self.assertEqual(SCALAR.weight((-3, 0)), 9)

    def test_both_realizations_survive_same_narrow_requirements(self) -> None:
        for model in (SCALAR, GAUSSIAN):
            with self.subTest(carrier=model.carrier):
                checks = checked(model)
                self.assertEqual(aggregate_status(tuple(checks.values())), "no_counterexample_within_bounds")
                self.assertEqual(checks["native_sorkin_i3"].checked, len(model.grid(1)) ** 3)
                self.assertEqual(checks["native_two_path_interference"].witness,
                    {"kind": "existence", "inputs": {"amplitudes": [list(model.grid(1)[0])] * 2},
                     "actual": str(2 * model.weight(model.grid(1)[0])), "required": "!=0"})
                # Weights are not normalized as probabilities of every algebraic expression.
                self.assertEqual(model.weight(model.add((1, 0), (1, 0))), 4)

    def test_negative_controls_have_independent_exact_witnesses(self) -> None:
        quartic = AmplitudeAlgebra("quartic", "integer_scalar", 0, 0, "quartic")
        absolute = AmplitudeAlgebra("absolute", "integer_scalar", 0, 0, "absolute")
        deformed = AmplitudeAlgebra("deformed", "integer_plane", -1, 2)
        split = AmplitudeAlgebra("split", "integer_plane", 1, -1)
        self.assertEqual(quartic.third_order((1, 0), (1, 0), (1, 0)), 36)
        self.assertEqual(absolute.third_order((-1, 0), (1, 0), (1, 0)), 2)
        self.assertEqual(deformed.weight(deformed.multiply((0, 1), (0, 1)))
                         - deformed.weight((0, 1)) ** 2, -3)
        self.assertEqual(split.weight((0, 1)), -1)
        for model, gate in ((quartic, "native_sorkin_i3"), (absolute, "native_sorkin_i3"),
                            (deformed, "native_product_weight"), (split, "native_nonnegative")):
            with self.subTest(model=model.id):
                self.assertEqual(checked(model)[gate].status, "counterexample")

    def test_empty_weight_and_unit_convention_are_separate_checks(self) -> None:
        zero = checked(AmplitudeAlgebra("zero", "integer_scalar", 0, 0, "zero"))
        self.assertEqual(zero["native_empty_weight"].status, "no_counterexample_within_bounds")
        self.assertEqual(zero["native_unit_weight"].status, "counterexample")
        self.assertEqual(zero["native_two_path_interference"].status, "inconclusive")
        self.assertEqual(zero["native_two_path_interference"].checked, 9)
        self.assertIsNone(zero["native_two_path_interference"].witness)

    def test_budget_exhaustion_never_becomes_pass_or_rejection(self) -> None:
        checks, scope = evaluate_amplitude_algebra(GAUSSIAN, Limits(max_cases=1, coefficient_radius=2))
        self.assertEqual(aggregate_status(checks), "inconclusive")
        third = {c.id: c for c in checks}["native_sorkin_i3"]
        self.assertEqual((third.checked, third.planned), (1, 15625))
        self.assertEqual(third.status, "inconclusive")
        diagnostics = object_fields(scope["diagnostics"])
        self.assertEqual((diagnostics["checked"], diagnostics["planned"]), (1, 25))
        self.assertFalse(diagnostics["complete_within_box"])

    def test_phase_capabilities_are_diagnostics_not_selection_gates(self) -> None:
        expected = ((SCALAR, {"0", "4"}), (GAUSSIAN, {"0", "2", "4"}))
        for model, weights in expected:
            checks, scope = evaluate_amplitude_algebra(model, Limits())
            samples = object_fields(scope["diagnostics"])["unit_weight_samples"]
            assert isinstance(samples, list)
            self.assertEqual({object_fields(row)["unit_plus_weight"] for row in samples}, weights)
            self.assertFalse(any("phase" in check.id for check in checks))

    def test_degenerate_dual_carrier_exposes_insufficiency_without_global_rejection(self) -> None:
        dual = AmplitudeAlgebra("dual", "integer_plane", 0, 0)
        checks, scope = evaluate_amplitude_algebra(dual, Limits())
        self.assertEqual(aggregate_status(checks), "no_counterexample_within_bounds")
        self.assertEqual(dual.weight((0, 1)), 0)
        samples = object_fields(scope["diagnostics"])["nonzero_zero_weight_samples"]
        assert isinstance(samples, list)
        self.assertIn([0, 1], samples)
        self.assertEqual(scope["scientific_status"], "unassessed")

    def test_real_projection_preserves_single_weights_but_not_composition(self) -> None:
        kernel = ((Fraction(1, 2), Fraction(0)), (Fraction(0), Fraction(1, 2)))
        for a, b in GAUSSIAN.grid(2):
            self.assertEqual(quadratic(kernel, (Fraction(a), Fraction(b))),
                             Fraction(GAUSSIAN.weight((a, b)), 2))
        native = GAUSSIAN.add(GAUSSIAN.multiply((1, 0), (1, 0)), GAUSSIAN.multiply((0, 1), (0, 1)))
        projected = quadratic(tensor(kernel, kernel), (Fraction(1), Fraction(0), Fraction(0), Fraction(1)))
        self.assertEqual(Fraction(GAUSSIAN.weight(native), 4), 0)
        self.assertEqual(projected, Fraction(1, 2))

    def test_archived_bindings_are_exact_and_never_invoke_imported_qm(self) -> None:
        specs = [object_fields(value) for value in inventory_specifications()]
        known = [spec for spec in specs if pipeline.digest(spec) in SOURCE_BINDINGS]
        self.assertEqual(len(known), 2)
        with (patch.object(pipeline, "evaluate_qm", side_effect=AssertionError("no imported QM")),
              patch.object(primitive, "evaluate", side_effect=AssertionError("no real kernel projection"))):
            results = pipeline.run_batch(list(known))
        for original, result in zip(known, results, strict=True):
            self.assertEqual(object_fields(result.report["request"])["candidate"], original)
            self.assertEqual(result.report["status"], "no_counterexample_within_bounds")
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            scope = object_fields(result.report["scope"])
            self.assertEqual(scope["missing_bridges"], original["missing_bridges"])
            expected = (SCALAR if original["id"] == "pair_history_signed_scalar_realization" else GAUSSIAN)
            self.assertEqual(scope["native_law"], {**expected.specification(), "id": original["id"]})
            samples = object_fields(scope["diagnostics"])["unit_weight_samples"]
            assert isinstance(samples, list)
            self.assertEqual(len(samples), 2 if expected is SCALAR else 4)
            modified = {**original, "declared_status": "different source claim"}
            self.assertEqual(pipeline.run_batch([modified])[0].report["status"], "unsupported")
        lower = next(spec for spec in specs if spec["id"] == "pair_history_lower_law")
        self.assertEqual(pipeline.run_batch([lower])[0].report["status"], "unsupported")

    def test_invalid_specs_fail_validation_not_physics(self) -> None:
        for fields in ({"product_square": True}, {"imaginary_weight": 3}, {"carrier": "complex"},
                       {"weight_rule": "born"}, {"unexpected": 0}, {"product_square": 1}):
            with self.subTest(fields=fields), self.assertRaises((ValueError, TypeError)):
                parse_amplitude_algebra({**SCALAR.specification(), **fields})
        with self.assertRaises(ValueError):
            parse_amplitude_algebra({**GAUSSIAN.specification(), "weight_rule": "absolute"})

    def test_new_family_cache_and_controls_are_reproducible(self) -> None:
        specs = load_json(ROOT / "data/amplitude_algebra_controls.json")
        assert isinstance(specs, list)
        with tempfile.TemporaryDirectory() as directory:
            initial = pipeline.run_batch(specs, cache_dir=Path(directory))
            cached = pipeline.run_batch(specs, cache_dir=Path(directory))
            fresh = pipeline.run_batch(specs, cache_dir=Path(directory), fresh=True)
        self.assertEqual([r.report for r in initial], [r.report for r in cached])
        self.assertEqual([r.report for r in initial], [r.report for r in fresh])
        self.assertTrue(all(r.reused for r in cached))
        self.assertEqual([r.report["status"] for r in initial], ["counterexample"] * 5 + ["no_counterexample_within_bounds"])

    def test_history_keeps_controls_and_original_unsupported_observations(self) -> None:
        history = History()
        controls = history.get("submissions", "444570469f455efa2464b66d81070e13130fb99ab9bab796bae9b4f10724f1aa")
        self.assertEqual(controls["candidates"], load_json(ROOT / "data/amplitude_algebra_controls.json"))
        for key in ("3ed6b4dfa2b92c1fa0fb1a65ee93df221d9fd84a2f0f1779ab97416bf1a3b69f",
                    "7d74b571d44e96b023a09fcf08d98cf3805f746cd0c8560ff2ee109e8e92888a"):
            reports = history.get("observations", key)["reports"]
            assert isinstance(reports, list)
            self.assertEqual(object_fields(reports[0])["status"], "unsupported")


if __name__ == "__main__":
    unittest.main()
