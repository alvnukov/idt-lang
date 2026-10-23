"""Finite phase probes preserve candidates and exact diagnostic scope."""

from __future__ import annotations

import copy
import gzip
import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from scripts.search_native_phases import main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import continuation_sufficiency as continuation
from theory_experiments import native_phase_search as phase
from theory_experiments.amplitude_algebra import AmplitudeAlgebra, WeightRule
from theory_experiments.candidate_history import History, record_batch
from theory_experiments.continuation_sufficiency import verify_certificate
from theory_experiments.primitive_screen import (
    Limits,
    canonical_json,
    exact_fraction,
    load_json,
    object_fields,
)


def gaussian(rule: WeightRule = "quadratic") -> AmplitudeAlgebra:
    return AmplitudeAlgebra("test_gaussian_" + rule, "integer_plane", -1, 1, rule)


def array(value: object) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("expected test array")
    return value


def probabilities(orbit: dict[str, object]) -> list[object]:
    return [object_fields(row)["p"] for row in array(orbit["trace_first_five"])]


class NativePhaseSearchTests(unittest.TestCase):
    def test_exact_52_unique_specifications_and_coverage(self) -> None:
        models = phase.candidates()
        self.assertEqual(len(models), 52)
        self.assertEqual(len({model.id for model in models}), 52)
        self.assertEqual(len({canonical_json(model.specification()) for model in models}), 52)
        actual = {(m.product_square, m.imaginary_weight, m.weight_rule)
                  for m in models if m.carrier == "integer_plane"}
        self.assertEqual(actual, {(k, eta, rule) for k in range(-2, 3)
                                  for eta in range(-2, 3) for rule in ("quadratic", "quartic")})
        self.assertEqual([(m.product_square, m.imaginary_weight, m.weight_rule)
                          for m in models if m.carrier == "integer_scalar"],
                         [(0, 0, "quadratic"), (0, 0, "quartic")])

    def test_fixed_config_matches_file_and_rejects_malformed_or_tuned_fields(self) -> None:
        self.assertEqual(phase.load_config(), phase.campaign_config())
        for key, invalid in (("parameter_min", -3), ("parameter_max", True),
                             ("multiplier_radius", 2.0), ("max_multiplications", 17),
                             ("trace_length", False), ("reference", [True, 0]),
                             ("plane_seeds", [[1, 0]])):
            config = phase.campaign_config()
            config[key] = invalid
            with self.subTest(key=key), self.assertRaises((TypeError, ValueError)):
                phase.validate_config(config)
        config = phase.campaign_config()
        config["extra"] = 0
        with self.assertRaises(ValueError):
            phase.validate_config(config)

    def test_gaussian_quadratic_and_quartic_share_seed_one_trace(self) -> None:
        for rule in ("quadratic", "quartic"):
            model = gaussian("quadratic" if rule == "quadratic" else "quartic")
            orbit = phase.probe_orbit(model, (0, 1), (1, 0))
            self.assertEqual(probabilities(orbit), ["1", "1/2", "0", "1/2", "1"])
            self.assertTrue(orbit["quarter_cycle_trace_hit"])
            self.assertEqual(orbit["cycle_length"], 4)
            self.assertEqual(orbit["orbit_status"], "exact_state_closure")
            self.assertEqual(orbit["candidate_verdict"], "unchanged")

    def test_off_axis_seed_distinguishes_weights_and_equal_one_i3(self) -> None:
        quadratic, quartic = gaussian(), gaussian("quartic")
        self.assertEqual(phase.readout(quadratic, (1, 1))["p"], "5/6")
        self.assertEqual(phase.readout(quartic, (1, 1))["p"], "25/26")
        self.assertEqual(quadratic.third_order((1, 0), (1, 0), (1, 0)), 0)
        self.assertEqual(quartic.third_order((1, 0), (1, 0), (1, 0)), 36)

    def test_invalid_negative_weights_and_zero_denominators_are_separate(self) -> None:
        indefinite = AmplitudeAlgebra("indefinite", "integer_plane", -1, -1)
        negative = phase.readout(indefinite, (1, 1))
        zero = phase.readout(indefinite, (0, 1))
        self.assertEqual(negative["issues"], ["negative_weight"])
        self.assertEqual(zero["issues"], ["zero_denominator"])
        self.assertIsNone(negative["p"])
        self.assertIsNone(zero["p"])
        bad = phase.probe_orbit(indefinite, (1, 0), (0, 1))
        self.assertEqual(bad["continuation_status"], "invalid_orbit_readout")
        self.assertIsNone(bad["continuation"])

    def test_open_orbit_is_not_failure_or_readout_repeat_closure(self) -> None:
        # Dual-number multiplier (1,1): (1,n), constant W=1 and p=1,
        # but every exact state differs. A readout-only closure would be false.
        model = AmplitudeAlgebra("dual", "integer_plane", 0, 0)
        with patch.object(continuation, "analyze", side_effect=AssertionError("must not call")):
            orbit = phase.probe_orbit(model, (1, 1), (1, 0))
        self.assertEqual(probabilities(orbit), ["1"] * 5)
        self.assertEqual(orbit["orbit_status"], "open_within_bound")
        self.assertEqual(len(array(orbit["visited"])), 17)
        self.assertEqual(orbit["continuation_status"], "no_finite_certificate_within_bound")
        self.assertEqual(orbit["candidate_verdict"], "unchanged")

    def test_finite_current_readout_witness_is_independently_verified(self) -> None:
        orbit = phase.probe_orbit(gaussian(), (0, 1), (1, 0))
        finite = object_fields(orbit["continuation"])
        analysis = object_fields(finite["analysis"])
        certificate = object_fields(analysis["certificate"])
        self.assertEqual(certificate["kind"], "distinguishing_word")
        self.assertTrue(verify_certificate(finite["model"], certificate))
        self.assertEqual(analysis["candidate_verdict"], "unchanged")
        self.assertIn("not_quantum", str(finite["full_state_boundary"]))
        broken = copy.deepcopy(certificate)
        broken["word"] = []
        self.assertFalse(verify_certificate(finite["model"], broken))

    def test_critical_integer_inputs_reject_bools_and_floats(self) -> None:
        for steps in (True, 1.0, 0, 17):
            with self.subTest(steps=steps), self.assertRaises(ValueError):
                # Deliberately hostile runtime input, despite the typed public API.
                phase.probe_orbit(gaussian(), (0, 1), (1, 0), max_steps=steps)  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            phase.probe_orbit(gaussian(), (True, 1), (1, 0))

    def test_full_campaign_reproducible_all_laws_preserved(self) -> None:
        first = phase.campaign(phase.campaign_config())
        second = phase.campaign(phase.campaign_config())
        self.assertEqual(first, second)
        unhashed = {key: value for key, value in first.items() if key != "report_sha256"}
        self.assertEqual(first["report_sha256"], pipeline.digest(unhashed))
        rows = [object_fields(row) for row in array(first["candidates"])]
        self.assertEqual(len(rows), 52)
        self.assertIsNone(first["archival"])
        statuses = {object_fields(row["bounded_native_laws"])["status"] for row in rows}
        self.assertIn("counterexample", statuses)
        self.assertIn("no_counterexample_within_bounds", statuses)
        self.assertTrue(any(not object_fields(row["phase"])["quarter_cycle_hit"] for row in rows))
        self.assertTrue(all(row["candidate_verdict"] == "unchanged" for row in rows))
        hashes = object_fields(first["source_sha256"])
        self.assertIn("theory_experiments/amplitude_algebra.py", hashes)
        self.assertIn("theory_experiments/continuation_sufficiency.py", hashes)
        for row in rows:
            self.assertEqual(row["candidate_sha256"], pipeline.digest(row["candidate_specification"]))
        screen = object_fields(next(row for row in rows
                                   if object_fields(row["candidate_specification"])["imaginary_weight"] == 1
                                   and object_fields(row["candidate_specification"])["weight_rule"] == "quadratic"
                                   )["bounded_native_laws"])
        checks = [object_fields(row) for row in array(screen["checks"])]
        i3 = next(row for row in checks if row["id"] == "native_sorkin_i3")
        self.assertEqual((i3["checked"], i3["planned"]), (729, 729))

    def test_temp_archive_keeps_52_specs_reports_and_old_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            archive = History(Path(directory) / "history")
            initial = record_batch([gaussian().specification()], Limits(), history=archive)
            old = {p: p.read_bytes() for p in archive.root.rglob("*") if p.is_file()}
            report = phase.campaign(phase.campaign_config(), history=archive)
            links = object_fields(report["archival"])
            submission, observation = links["submission"], links["observation"]
            assert isinstance(submission, str) and isinstance(observation, str)
            specs = array(archive.get("submissions", submission)["candidates"])
            results = array(archive.get("observations", observation)["reports"])
            self.assertEqual(len(specs), 52)
            self.assertEqual(len(results), 52)
            self.assertEqual(specs, [m.specification() for m in phase.candidates()])
            self.assertTrue(all(p.read_bytes() == contents for p, contents in old.items()))
            self.assertEqual(archive.baseline(initial.submission)["submission"], initial.submission)
            for spec, result in zip(specs, results, strict=True):
                self.assertEqual(object_fields(object_fields(result)["request"])["candidate"], spec)

    def test_cli_default_no_writes_and_explicit_output_refuses_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "report.json"
            # Use a real campaign, no patched output or history implementation.
            with redirect_stdout(io.StringIO()) as stdout:
                self.assertEqual(main([]), 0)
            self.assertEqual(list(root.iterdir()), [])
            self.assertLess(len(stdout.getvalue()), 1000)
            with redirect_stdout(io.StringIO()):
                self.assertEqual(main(["--output", str(output)]), 0)
            saved = output.read_bytes()
            self.assertEqual(len(array(object_fields(json.loads(saved))["candidates"])), 52)
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                main(["--output", str(output)])
            self.assertEqual(output.read_bytes(), saved)
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                main(["--record-history"])
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                main(["--history-dir", str(root / "history")])

    def test_cli_gzip_exact_report_deterministic_bytes_and_no_overwrite(self) -> None:
        report = phase.campaign(phase.campaign_config())
        expected = canonical_json(report).encode("utf-8") + b"\n"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first, second = root / "first.json.gz", root / "second.json.gz"
            with redirect_stdout(io.StringIO()):
                self.assertEqual(main(["--output", str(first)]), 0)
                self.assertEqual(main(["--output", str(second)]), 0)
            saved = first.read_bytes()
            self.assertEqual(gzip.decompress(saved), expected)
            self.assertEqual(saved, second.read_bytes())
            self.assertEqual(saved, gzip.compress(expected, mtime=0))
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                main(["--output", str(first)])
            self.assertEqual(first.read_bytes(), saved)

    def test_rational_extension_leads_exact_recurrences_without_native_adapter(self) -> None:
        fixture = object_fields(load_json(
            Path(__file__).resolve().parents[1] / "data/native_phase_search/rational_extension_leads.json"))
        self.assertEqual(fixture["schema"], "idt-rational-phase-extension-leads/1")
        self.assertEqual(fixture["candidate_verdict"], "unchanged")
        self.assertEqual(fixture["adapter_status"], "not_registered")
        self.assertEqual(fixture["adapter_scope"], "source_proposal_only_not_an_integer_amplitude_adapter")
        self.assertEqual(fixture["proof_status"], "finite_exact_calculation_not_formal_proof")
        self.assertEqual(fixture["empirical_status"], "not_tested")
        self.assertEqual(fixture["missing_bridges"], [
            "physical_preparation", "physical_readout_map", "physical_composites", "full_QM", "SM", "gravity"])
        expected: dict[str, tuple[int, int, tuple[Fraction, Fraction]]] = {
            "rational_phase_weighted_two_v1": (-2, 2, (Fraction(1, 3), Fraction(2, 3))),
            "rational_phase_gaussian_v1": (-1, 1, (Fraction(3, 5), Fraction(4, 5))),
        }
        leads = [object_fields(value) for value in array(fixture["candidates"])]
        self.assertEqual({row["id"] for row in leads}, set(expected))
        self.assertEqual(len(leads), 2)
        for lead in leads:
            identifier = lead["id"]
            assert isinstance(identifier, str)
            k, eta, multiplier = expected[identifier]
            spec = object_fields(lead["specification"])
            self.assertIs(type(spec["product_square"]), int)
            self.assertIs(type(spec["imaginary_weight"]), int)
            self.assertEqual((spec["product_square"], spec["imaginary_weight"]), (k, eta))
            self.assertEqual(spec["carrier"], "Q^2")
            self.assertEqual(spec["seed"], ["1", "0"])
            self.assertEqual(spec["reference"], ["1", "0"])
            self.assertEqual(tuple(exact_fraction(x) for x in array(spec["multiplier"])), multiplier)
            self.assertEqual(spec["reported_readout_times"], list(range(8)))
            self.assertEqual(spec["multiplications_checked"], 8)
            self.assertEqual(lead["status"], "synthetic_finite_rational_extension_hit")
            self.assertEqual(lead["candidate_verdict"], "unchanged")
            self.assertEqual(lead["adapter_status"], "not_registered")
            self.assertEqual(lead["integer_screen_status"], "not_applicable_rational_domain_extension")
            self.assertEqual(lead["empirical_status"], "not_tested")
            self.assertEqual(lead["orbit_status"], "no_repeat_observed_through_eight_multiplications")
            self.assertEqual(lead["continuation_status"], "no_finite_orbit_certificate")
            self.assertEqual(lead["weight_scope"], "visited_states_only_no_universal_statement_tested")
            self.assertIs(lead["visited_weights_equal_one"], True)
            # Rational proposals are intentionally outside the integer adapter.
            with self.assertRaises(ValueError):
                pipeline.parse_hypothesis(spec)
            observations = array(lead["observations"]) + [lead["next_state_observation"]]
            self.assertEqual(len(observations), 9)
            state = (Fraction(1), Fraction(0))
            visited: set[tuple[Fraction, Fraction]] = set()
            c, d = multiplier
            for t, value in enumerate(observations):
                row = object_fields(value)
                self.assertIs(type(row["t"]), int)
                self.assertEqual(row["t"], t)
                self.assertEqual(tuple(exact_fraction(x) for x in array(row["state"])), state)
                self.assertNotIn(state, visited)
                visited.add(state)
                a, b = state
                weight = a * a + eta * b * b
                plus, minus = (a + 1) ** 2 + eta * b * b, (a - 1) ** 2 + eta * b * b
                self.assertEqual(weight, 1)
                self.assertGreaterEqual(plus, 0)
                self.assertGreaterEqual(minus, 0)
                self.assertGreater(plus + minus, 0)
                for field, calculated in (("weight", weight), ("plus_weight", plus), ("minus_weight", minus),
                                           ("denominator", plus + minus), ("p", plus / (plus + minus))):
                    self.assertEqual(exact_fraction(row[field]), calculated)
                state = (a * c + k * b * d, a * d + b * c)


if __name__ == "__main__":
    unittest.main()
