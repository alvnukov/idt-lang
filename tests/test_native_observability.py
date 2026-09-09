"""A lossy projection is not a rejected candidate; quotients need composition."""

from __future__ import annotations

import contextlib
import io
import itertools
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import check_native_observability as cli
from scripts.archive_existing_primitives import inventory_specifications
from theory_experiments.amplitude_algebra import (
    AmplitudeAlgebra,
    evaluate_amplitude_algebra,
)
from theory_experiments.candidate_history import History
from theory_experiments.native_observability import GRAMMAR, analyze_projection
from theory_experiments.primitive_screen import (
    Limits,
    aggregate_status,
    canonical_json,
    load_json,
    object_fields,
)

ROOT = Path(__file__).resolve().parents[1]


class NativeObservabilityTests(unittest.TestCase):
    def test_all_supplied_plane_parameters_match_independent_existing_gates(self) -> None:
        survivors: list[tuple[int, int]] = []
        for k, eta in itertools.product(range(-2, 3), repeat=2):
            model = AmplitudeAlgebra("comparison", "integer_plane", k, eta)
            report = analyze_projection(model.specification())
            laws = object_fields(report["quadratic_law_compatibility"])
            checks = {c.id: c for c in evaluate_amplitude_algebra(model, Limits())[0]}
            self.assertEqual(laws["nonnegative_on_integer_carrier"], checks["native_nonnegative"].status == "no_counterexample_within_bounds")
            self.assertEqual(laws["multiplicative_on_integer_carrier"], checks["native_product_weight"].status == "no_counterexample_within_bounds")
            if laws["nonnegative_on_integer_carrier"] and laws["multiplicative_on_integer_carrier"]:
                survivors.append((k, eta))
        self.assertEqual(survivors, [(-2, 2), (-1, 1), (0, 0)])

    def test_exact_defect_coefficients_reproduce_native_product(self) -> None:
        for k, eta in itertools.product(range(-2, 3), repeat=2):
            model = AmplitudeAlgebra("identity", "integer_plane", k, eta)
            coefficients = object_fields(analyze_projection(model.specification())["weight_law_coefficients"])
            first, second = coefficients["abcd"], coefficients["b2d2"]
            assert isinstance(first, int) and isinstance(second, int)
            for (a, b), (c, d) in itertools.product(model.grid(1), repeat=2):
                native = model.weight(model.multiply((a, b), (c, d))) - model.weight((a, b)) * model.weight((c, d))
                self.assertEqual(native, first * a * b * c * d + second * b * b * d * d)

    def test_dual_quotient_is_many_to_one_not_a_defective_candidate(self) -> None:
        dual = AmplitudeAlgebra("dual", "integer_plane", 0, 0)
        report = analyze_projection(dual.specification())
        self.assertEqual(report["status"], "preserves_declared_grammar")
        self.assertEqual(report["relation"], "many_to_one_weight_preserving_quotient")
        self.assertEqual(report["candidate_verdict"], "unchanged")
        self.assertEqual(report["grammar"], list(GRAMMAR))
        for initial in dual.grid(2):
            value, projected = initial, initial[0]
            for _ in range(8):
                value = dual.add(dual.multiply(value, (2, -1)), (0, 1))
                projected *= 2
                self.assertEqual(dual.weight(value), projected ** 2)
        # An added coordinate-swap operation can expose the hidden coordinate.
        self.assertNotEqual(dual.weight((1, 0)), dual.weight((0, 0)))
        untested = report["untested"]
        assert isinstance(untested, list)
        self.assertIn("additional_transformations", untested)

    def test_scalar_projection_is_identity_on_scalar_carrier(self) -> None:
        report = analyze_projection(AmplitudeAlgebra("scalar", "integer_scalar", 0, 0).specification())
        self.assertEqual(report["relation"], "identity")
        self.assertEqual(report["status"], "preserves_declared_grammar")

    def test_zero_weight_alone_cannot_authorize_projection(self) -> None:
        report = analyze_projection(AmplitudeAlgebra("activation", "integer_plane", -1, 0).specification())
        self.assertEqual(report["status"], "projection_counterexample")
        witness = object_fields(report["witness"])
        self.assertEqual(witness["initial_native_weight"], "0")
        self.assertEqual(witness["native_weight"], "1")
        self.assertEqual(witness["expression"], {"multiply": [{"variable": 0}, {"variable": 0}]})
        self.assertEqual(report["candidate_verdict"], "unchanged")

    def test_gaussian_projection_failure_does_not_invalidate_gaussian(self) -> None:
        gaussian = AmplitudeAlgebra("gaussian", "integer_plane", -1, 1)
        report = analyze_projection(gaussian.specification())
        self.assertEqual(object_fields(report["witness"])["native_weight"], "1")
        self.assertEqual(report["status"], "projection_counterexample")
        self.assertEqual(aggregate_status(evaluate_amplitude_algebra(gaussian, Limits())[0]), "no_counterexample_within_bounds")
        self.assertEqual(report["empirical_status"], "not_tested")
        self.assertEqual(report["proof_status"], "not_checked_by_this_command")

    def test_source_binding_and_open_lower_law_remain_distinct(self) -> None:
        specs = [object_fields(spec) for spec in inventory_specifications()]
        expectations = {"pair_history_signed_scalar_realization": "preserves_declared_grammar",
                        "pair_history_gaussian_realization": "projection_counterexample",
                        "pair_history_lower_law": "unsupported"}
        for spec in specs:
            identifier = spec["id"]
            assert isinstance(identifier, str)
            if identifier in expectations:
                report = analyze_projection(spec)
                self.assertEqual(report["status"], expectations[identifier])
                self.assertEqual(report["missing_bridges"], spec["missing_bridges"])
                self.assertEqual(analyze_projection({**spec, "declared_status": "modified"})["status"], "unsupported")

    def test_nonquadratic_rule_remains_unsupported_not_incompatible(self) -> None:
        report = analyze_projection(AmplitudeAlgebra("quartic", "integer_scalar", 0, 0, "quartic").specification())
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(report["candidate_verdict"], "unchanged")
        self.assertNotIn("quadratic_law_compatibility", report)

    def test_cli_reports_projection_failures_without_candidate_rejection_exit(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()) as output:
            code = cli.main(["--batch-file", str(ROOT / "data/native_observability_probes.json")])
        self.assertEqual(code, 0)
        self.assertIn('"projection_counterexample"', output.getvalue())
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "unsupported.json"
            path.write_text(canonical_json([AmplitudeAlgebra("zero", "integer_scalar", 0, 0, "zero").specification()]))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(cli.main(["--batch-file", str(path)]), 3)

    def test_sources_changed_since_import_or_during_run_are_errors(self) -> None:
        spec = AmplitudeAlgebra("dual", "integer_plane", 0, 0).specification()
        with patch.object(cli, "LOADED_EXTRA_HASHES", {}), self.assertRaisesRegex(ValueError, "since import"):
            cli.evidence([spec])
        with patch.object(cli, "LOADED_MODULE_SHA256", "old"), self.assertRaisesRegex(ValueError, "since import"):
            cli.evidence([spec])
        with patch.object(cli, "LOADED_SOURCE_HASHES", {}), self.assertRaisesRegex(ValueError, "since import"):
            cli.evidence([spec])
        with (patch.object(cli, "_extra_source_hashes", side_effect=[cli.LOADED_EXTRA_HASHES, {}]),
              self.assertRaisesRegex(ValueError, "during analysis")):
            cli.evidence([spec])

    def test_new_probes_have_opposite_scoped_screen_results(self) -> None:
        specs = load_json(ROOT / "data/native_observability_probes.json")
        assert isinstance(specs, list)
        from theory_experiments.candidate_pipeline import run_batch
        self.assertEqual([r.report["status"] for r in run_batch(specs)],
                         ["counterexample", "no_counterexample_within_bounds"])

    def test_saved_review_matches_analysis_and_probe_inputs_remain_archived(self) -> None:
        saved = object_fields(load_json(ROOT / "data/native_observability_review.json"))
        specs = saved["candidates"]
        assert isinstance(specs, list)
        self.assertEqual(len(specs), 5)
        self.assertEqual(saved["reports"], [analyze_projection(spec) for spec in specs])
        record = History().get("submissions", "e03cb6c58c7d0e5a45d89875fba77d3d39629b625172ba0046af2f9aed9196bb")
        self.assertEqual(record["candidates"], load_json(ROOT / "data/native_observability_probes.json"))


if __name__ == "__main__":
    unittest.main()
