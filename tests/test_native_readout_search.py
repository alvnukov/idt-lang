"""Independent reference formulas and integration boundaries for bounded search."""

from __future__ import annotations

import copy
import itertools
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import native_readout_search as search_module
from theory_experiments.amplitude_algebra import AmplitudeAlgebra
from theory_experiments.candidate_history import History, record_batch
from theory_experiments.native_bell_bridge import evaluate_native_bell_bridge
from theory_experiments.native_readout_probe import (
    evaluate_native_readout_probe,
    evaluate_response_on_native_trace,
    parse_native_readout_probe,
)
from theory_experiments.native_readout_search import (
    NativeReadoutSearch,
    evaluate_native_readout_search,
    parse_native_readout_search,
    reference_preparations,
)
from theory_experiments.primitive_screen import (
    Limits,
    canonical_json,
    load_json,
    object_fields,
    parse_limits,
)

ROOT = Path(__file__).resolve().parents[1]
SUCCESS = "no_counterexample_within_bounds"
NAMES = ("native_weight", "squared_native_weight", "spike_49")


def specification(responses: tuple[str, ...] = NAMES, radius: int = 4) -> dict[str, object]:
    return NativeReadoutSearch("reference_search", AmplitudeAlgebra("scalar", "integer_scalar", 0, 0),
                                radius, responses).specification()


def run(responses: tuple[str, ...] = NAMES, radius: int = 4, budget: int = 324,
        *, spec: dict[str, object] | None = None) -> dict[str, object]:
    return pipeline.run_batch([specification(responses, radius) if spec is None else spec],
                              Limits(max_cases=budget))[0].report


def details(report: dict[str, object]) -> dict[str, object]:
    return object_fields(report["scope"])


def rows(report: dict[str, object]) -> dict[str, dict[str, object]]:
    values = details(report)["responses"]
    assert isinstance(values, list)
    return {str(object_fields(value)["response"]): object_fields(value) for value in values}


def witness(report: dict[str, object], response: str) -> dict[str, object]:
    return object_fields(rows(report)[response]["first_witness"])


def oracle_reference(x: int, y: int, response: str) -> tuple[Fraction, Fraction]:
    # Independent formulas on amplitudes, not production raw weights/trace functions.
    def g(n: int) -> int:
        square = n * n
        return (square * square if response == "squared_native_weight" else
                square + int(square == 49) if response == "spike_49" else square)
    return Fraction(g(1), g(x) + g(y) + g(1)), Fraction(2 * g(1), g(x + y) + g(x - y) + 2 * g(1))


def oracle_order(radius: int) -> list[tuple[int, int]]:
    # Construct shells and Manhattan sub-shells, not production sorted product.
    result: list[tuple[int, int]] = []
    for shell in range(radius + 1):
        for distance in range(2 * shell + 1):
            for x in range(-shell, shell + 1):
                for y in range(-shell, shell + 1):
                    if max(abs(x), abs(y)) == shell and abs(x) + abs(y) == distance:
                        result.append((x, y))
    return result


def source_specification() -> dict[str, object]:
    values = load_json(ROOT / "data/native_readout_controls.json")
    assert isinstance(values, list)
    return object_fields(object_fields(object_fields(values[0])["protocol"])["model"])


class NativeReadoutSearchTests(unittest.TestCase):
    def test_full_signed_order_prefixes_and_independent_first_witnesses(self) -> None:
        for radius, size in enumerate((1, 9, 25, 49, 81)):
            values = reference_preparations(radius)
            self.assertEqual(list(values), oracle_order(radius))
            self.assertEqual(len(set(values)), size)
            self.assertEqual(values, reference_preparations(4)[:size])
        order = oracle_order(4)
        expected = {"native_weight": (0, None), "squared_native_weight": (64, (6, (-1, -1))),
                    "spike_49": (8, (70, (-4, -3)))}
        for response, (count, first) in expected.items():
            hits = [(index, pair) for index, pair in enumerate(order, 1)
                    if len(set(oracle_reference(*pair, response))) != 1]
            self.assertEqual(len(hits), count)
            self.assertEqual(hits[0] if hits else None, first)

    def test_exact_witnesses_and_reference_row_not_unrelated_flag(self) -> None:
        report = run()
        self.assertEqual(report["status"], SUCCESS)
        self.assertEqual(rows(report)["native_weight"]["state"], "no_violation_within_bounds")
        for response, point, index, before, after, difference in (
            ("squared_native_weight", [-1, -1], 6, "1/3", "1/9", "2/9"),
            ("spike_49", [-4, -3], 70, "1/26", "2/53", "1/1378"),
        ):
            with self.subTest(response=response):
                row = rows(report)[response]
                found = witness(report, response)
                self.assertEqual(row["state"], "conditional_violation_found")
                self.assertEqual(row["preparations_checked"], index)
                self.assertEqual(found["coordinates"], point)
                self.assertEqual(found["preparation_index"], index)
                self.assertEqual(found["reference_row"], {"before": before, "after": after,
                                                        "difference_before_minus_after": difference})
                selected = object_fields(found["selected_response_evidence"])
                contexts = selected["response_contexts"]
                assert isinstance(contexts, list)
                for i, value in enumerate((before, after, before, after)):
                    marginal = object_fields(contexts[i])["alice_marginal"]
                    assert isinstance(marginal, list)
                    self.assertEqual(marginal[1], value)
                diagnostic = object_fields(selected["no_signalling_diagnostic"])
                self.assertFalse(diagnostic["holds"])
                differences = diagnostic["alice_marginal_differences_y0_minus_y1"]
                assert isinstance(differences, list)
                self.assertEqual(differences, [[str(-Fraction(difference)), difference]] * 2)

    def test_radius_three_and_zero_are_finite_absence_only(self) -> None:
        for radius, count in ((0, 1), (3, 49)):
            report = run(("spike_49",), radius)
            self.assertEqual(report["status"], SUCCESS)
            self.assertEqual(rows(report)["spike_49"]["state"], "no_violation_within_bounds")
            self.assertIsNone(rows(report)["spike_49"]["first_witness"])
            self.assertEqual(rows(report)["spike_49"]["preparations_checked"], count)
            self.assertTrue(details(report)["domain_exhausted"])
            self.assertTrue(details(report)["search_complete"])
            self.assertEqual(details(report)["stop_reason"], "domain_exhausted")
        zero = run(radius=0)
        self.assertEqual({str(row["state"]) for row in rows(zero).values()}, {"no_violation_within_bounds"})

    def test_atomic_budget_edges_and_all_witness_early_stop(self) -> None:
        for response, below, exact, index in (("squared_native_weight", 23, 24, 6), ("spike_49", 279, 280, 70)):
            incomplete = run((response,), budget=below)
            self.assertEqual(incomplete["status"], "inconclusive")
            self.assertIsNone(rows(incomplete)[response]["first_witness"])
            self.assertEqual(object_fields(details(incomplete)["budget"])["checked"], 4 * (index - 1))
            complete = run((response,), budget=exact)
            self.assertEqual(complete["status"], SUCCESS)
            self.assertEqual(details(complete)["stop_reason"], "all_witnesses_found")
            self.assertTrue(details(complete)["search_complete"])
            self.assertFalse(details(complete)["domain_exhausted"])
            self.assertEqual(object_fields(details(complete)["budget"])["checked"], exact)
        both = run(("spike_49", "squared_native_weight"), budget=324)
        self.assertEqual(object_fields(details(both)["budget"])["checked"], 280)
        self.assertEqual(object_fields(details(both)["budget"])["planned"], 324)

    def test_budgets_below_four_execute_no_native_trace_or_arithmetic(self) -> None:
        for budget in (1, 2, 3):
            with patch.object(search_module, "evaluate_native_bell_bridge", side_effect=AssertionError("started")):
                report = run(budget=budget)
            self.assertEqual(report["status"], "inconclusive")
            self.assertEqual(object_fields(details(report)["budget"])["checked"], 0)
            self.assertEqual({row["preparations_checked"] for row in rows(report).values()}, {0})

    def test_partial_success_preserved_with_native_unresolved(self) -> None:
        report = run(budget=280)
        self.assertEqual(report["status"], "inconclusive")
        self.assertEqual(rows(report)["native_weight"]["state"], "inconclusive")
        self.assertEqual(rows(report)["native_weight"]["preparations_checked"], 70)
        self.assertEqual(rows(report)["squared_native_weight"]["state"], "conditional_violation_found")
        self.assertEqual(rows(report)["spike_49"]["state"], "conditional_violation_found")
        self.assertFalse(details(report)["search_complete"])
        self.assertFalse(details(report)["domain_exhausted"])
        self.assertEqual(details(report)["stop_reason"], "budget_exhausted")

    def test_response_permutation_and_budget_prefix_stability(self) -> None:
        full = rows(run())
        for responses in itertools.permutations(NAMES):
            report = run(responses)
            self.assertEqual(list(rows(report)), list(responses))
            self.assertEqual(rows(report), {name: full[name] for name in responses})
        partial = run(budget=24)
        self.assertEqual(rows(partial)["squared_native_weight"], full["squared_native_weight"])
        for name in ("native_weight", "spike_49"):
            self.assertEqual(rows(partial)[name]["state"], "inconclusive")
            self.assertEqual(rows(partial)[name]["preparations_checked"], 6)

    def test_native_trace_once_per_preparation_no_copy_reparse_or_response_recompute(self) -> None:
        parsed = parse_native_readout_search(specification())
        with (
            patch.object(search_module, "evaluate_native_bell_bridge", wraps=evaluate_native_bell_bridge) as native,
            patch.object(search_module, "evaluate_response_on_native_trace", wraps=evaluate_response_on_native_trace) as selected,
            patch.object(search_module, "parse_amplitude_algebra", side_effect=AssertionError("reparsed")),
            patch.object(copy, "deepcopy", side_effect=AssertionError("copied")),
        ):
            checks, result = evaluate_native_readout_search(parsed, Limits(max_cases=324))
        self.assertEqual(checks[0].status, SUCCESS)
        self.assertEqual(native.call_count, 81)
        self.assertEqual(selected.call_count, 81 + 6 + 70)
        for call in native.call_args_list:
            self.assertIs(call.args[0].model, parsed.model)
            self.assertEqual(call.args[1].max_cases, 4)
        grouped: dict[int, list[object]] = {}
        for call in selected.call_args_list:
            self.assertIs(call.args[0].protocol.model, parsed.model)
            grouped.setdefault(id(call.args[0].protocol), []).append(call.args[3])
        self.assertEqual(len(grouped), 81)
        for traces in grouped.values():
            self.assertTrue(all(trace is traces[0] for trace in traces))
        self.assertEqual(object_fields(result["budget"])["checked"], 324)

    def test_unknown_response_entire_request_unsupported_before_binding_and_arithmetic(self) -> None:
        spec = specification(("native_weight", "future_response"))
        with (
            patch.object(search_module, "evaluate_native_bell_bridge", side_effect=AssertionError("native")),
            patch.object(AmplitudeAlgebra, "weight", side_effect=AssertionError("weight")),
            patch.object(search_module, "resolve_source_algebra", side_effect=AssertionError("resolved")),
        ):
            report = run(spec=spec, budget=1)
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(details(report)["unsupported_reason"], "unknown_selected_response")
        self.assertEqual(object_fields(details(report)["budget"])["checked"], 0)

    def test_binding_forgery_and_unsupported_algebra_preflight_preserve_unsupported(self) -> None:
        source = source_specification()
        source["declared_status"] = "forged same id"
        for model in (source, AmplitudeAlgebra("fourth", "integer_scalar", 0, 0, "quartic").specification(),
                      AmplitudeAlgebra("indefinite", "integer_plane", 1, -1).specification()):
            spec = specification()
            spec["model"] = model
            with patch.object(search_module, "evaluate_native_bell_bridge", side_effect=AssertionError("native")):
                report = run(spec=spec, budget=1)
            self.assertEqual(report["status"], "unsupported")
            self.assertEqual(object_fields(details(report)["budget"])["checked"], 0)

    def test_strict_schema_radii_lists_duplicates_and_nested_models(self) -> None:
        base = specification()
        for field, value in (("extra", 1), ("family", "not_search"), ("radius", True), ("radius", False),
                             ("radius", -1), ("radius", 5), ("radius", "4"), ("radius", 4.0),
                             ("responses", []), ("responses", ["native_weight"] * 2),
                             ("responses", ["a", "b", "c", "d"]), ("responses", "native_weight"),
                             ("responses", [True]), ("responses", [{"power": 2}]), ("model", base)):
            malformed = dict(base)
            malformed[field] = value
            with self.subTest(field=field, value=value), self.assertRaises((ValueError, TypeError)):
                parse_native_readout_search(malformed)
        for field in base:
            malformed = dict(base)
            del malformed[field]
            with self.assertRaises((ValueError, TypeError)):
                parse_native_readout_search(malformed)
        self.assertEqual(parse_native_readout_search(base).specification(), base)

    def test_source_bound_full_spec_witness_replay_and_source_model_not_reparsed(self) -> None:
        spec = specification(("squared_native_weight",))
        spec["model"] = source_specification()
        parsed = parse_native_readout_search(spec)
        with patch.object(search_module, "parse_source_candidate", side_effect=AssertionError("reparsed")):
            _, direct = evaluate_native_readout_search(parsed, Limits(max_cases=24))
        self.assertEqual(direct["model_origin"], "exact_archived_source_specification_binding")
        report = run(spec=spec, budget=24)
        found = witness(report, "squared_native_weight")
        probe = parse_native_readout_probe(found["probe"])
        self.assertEqual(probe.protocol.model.specification(), spec["model"])
        checks, selected = evaluate_native_readout_probe(probe, parse_limits(found["limits"]))
        self.assertEqual(found["selected_response_checks"], [check.specification() for check in checks])
        self.assertEqual(found["selected_response_evidence"], selected)
        native = object_fields(selected["native_protocol_evidence"])
        self.assertEqual(native["source_specification_sha256"], pipeline.digest(spec["model"]))
        self.assertEqual(selected["protocol_sha256"], pipeline.digest(probe.protocol.specification()))

    def test_witness_uses_actual_native_trace_not_formula_shortcut(self) -> None:
        # A synthetic reused trace changes reference weights; production must consume it.
        parsed = parse_native_readout_search(specification(("squared_native_weight",), 0))
        from theory_experiments.native_bell_bridge import BRIDGE, NativeBellBridge
        protocol = NativeBellBridge("synthetic", BRIDGE, parsed.model,
            (((0, 0), (0, 0)), ((1, 0), (0, 0))),
            (search_module.IDENTITY,) * 2, (search_module.IDENTITY, search_module.HADAMARD))
        checks, native = evaluate_native_bell_bridge(protocol, Limits(max_cases=4))
        contexts = native["contexts"]
        assert isinstance(contexts, list)
        for i, context in enumerate(contexts):
            assert isinstance(context, dict)
            context["raw_weights"] = [["1", "1"], ["1", "0"]] if i % 2 == 0 else [["4", "0"], ["1", "1"]]
        with patch.object(search_module, "evaluate_native_bell_bridge", return_value=(checks, native)):
            result_checks, result = evaluate_native_readout_search(parsed, Limits(max_cases=4))
        self.assertEqual(result_checks[0].status, SUCCESS)
        values = result["responses"]
        assert isinstance(values, list)
        found = object_fields(object_fields(values[0])["first_witness"])
        self.assertEqual(found["reference_row"], {"before": "1/3", "after": "1/9",
                                                 "difference_before_minus_after": "2/9"})

    def test_cache_replay_corruption_and_source_provenance_invalidation(self) -> None:
        spec = specification(("squared_native_weight",), 1)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary) / "cache"
            first = pipeline.run_batch([spec], Limits(max_cases=24), cache)[0]
            with patch.object(pipeline, "compute", side_effect=AssertionError("recomputed")):
                second = pipeline.run_batch([spec], Limits(max_cases=24), cache)[0]
            self.assertTrue(second.reused)
            self.assertEqual(first.report, second.report)
            assert first.artifact is not None
            self.assertEqual(pipeline.replay_artifact(first.artifact), first.report)
            changed = pipeline.provenance()
            hashes = object_fields(changed["source_sha256"])
            hashes["theory_experiments/native_readout_search.py"] = "0" * 64
            changed["source_sha256"] = hashes
            with patch.object(pipeline, "provenance", return_value=changed), self.assertRaisesRegex(ValueError, "since import"):
                pipeline.run_batch([spec], Limits(max_cases=24), cache)
            envelope = object_fields(json.loads(first.artifact.read_text()))
            corrupted = object_fields(envelope["report"])
            corrupted["status"] = "counterexample"
            envelope["report"] = corrupted
            first.artifact.write_text(canonical_json(envelope), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "integrity"):
                pipeline.run_batch([spec], Limits(max_cases=24), cache)

    def test_worst_case_source_output_size_claim_boundaries_and_temporary_history(self) -> None:
        spec = specification()
        spec["model"] = source_specification()
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary) / "cache"
            result = pipeline.run_batch([spec], Limits(max_cases=324), cache)[0]
            assert result.artifact is not None
            self.assertLess(result.artifact.stat().st_size, 524288)
            self.assertLess(len(canonical_json([spec]).encode()), 131072)
            self.assertEqual(pipeline.read_entry(result.artifact, object_fields(result.report["request"])), result.report)
            recorded = record_batch([spec], Limits(max_cases=24), history=History(Path(temporary) / "history"))
            self.assertEqual(recorded.results[0].report["status"], "inconclusive")
            self.assertEqual(recorded.changes, [])
        report = result.report
        self.assertEqual(report["proof_status"], "not_attempted")
        self.assertEqual(report["empirical_status"], "not_tested")
        self.assertEqual(report["rejection_scope"], "no_primitive_rejection_execution_diagnostics_only")
        self.assertEqual(details(report)["candidate_verdict"], "unchanged")
        self.assertEqual(details(report)["scientific_status"], "unassessed")
        self.assertEqual(details(report)["proof_check"], "not_run_by_this_evaluator")
        self.assertIn("not_formal_Python_verification", str(details(report)["artifact_relation"]))
        self.assertIn("theory_experiments/native_readout_search.py", pipeline.SOURCE_PATHS)
        self.assertIn("data/native_readout_search_controls.json", pipeline.SOURCE_PATHS)

    def test_new_controls_and_old_readout_shared_function_identity(self) -> None:
        values = load_json(ROOT / "data/native_readout_search_controls.json")
        assert isinstance(values, list)
        self.assertEqual(len(values), 6)
        for result in pipeline.run_batch(values, Limits(max_cases=324)):
            candidate = object_fields(object_fields(result.report["request"])["candidate"])
            self.assertEqual(result.report["status"], "unsupported" if candidate["id"] == "search_unknown_response" else SUCCESS)
        old = load_json(ROOT / "data/native_readout_controls.json")
        assert isinstance(old, list)
        for value in old:
            probe = parse_native_readout_probe(value)
            native_checks, native = evaluate_native_bell_bridge(probe.protocol, Limits(max_cases=4))
            self.assertEqual(evaluate_native_readout_probe(probe, Limits(max_cases=4)),
                             evaluate_response_on_native_trace(probe, Limits(max_cases=4), native_checks, native))

    def test_both_archived_control_models_exact_binding_same_real_integer_witnesses(self) -> None:
        values = load_json(ROOT / "data/native_readout_search_controls.json")
        assert isinstance(values, list)
        self.assertLess(len(canonical_json(values).encode()), 131072)
        old = load_json(ROOT / "data/native_readout_controls.json")
        assert isinstance(old, list)
        expected_models = {str(object_fields(value)["id"]):
            object_fields(object_fields(value)["protocol"])["model"] for value in old}
        source_names = {"search_archived_scalar_all_responses": "readout_scalar_bell_native",
                        "search_archived_gaussian_all_responses": "readout_gaussian_bell_native"}
        archived = [object_fields(value) for value in values if object_fields(value)["id"] in source_names]
        self.assertEqual(len(archived), 2)
        for spec in archived:
            name = str(spec["id"])
            self.assertEqual(spec["model"], expected_models[source_names[name]])
            report = run(spec=spec)
            self.assertEqual(report["status"], SUCCESS)
            self.assertEqual(details(report)["model_sha256"], pipeline.digest(spec["model"]))
            self.assertEqual(details(report)["source_specification_sha256"], pipeline.digest(spec["model"]))
            metadata = object_fields(details(report)["native_protocol_metadata"])
            self.assertNotIn("preparation_raw_total", metadata)
            self.assertEqual(metadata["model_origin"], "exact_archived_source_specification_binding")
            for response, point in (("squared_native_weight", [-1, -1]), ("spike_49", [-4, -3])):
                found = witness(report, response)
                self.assertEqual(found["coordinates"], point)
                probe = parse_native_readout_probe(found["probe"])
                self.assertEqual(probe.protocol.model.specification(), spec["model"])
                checks, selected = evaluate_native_readout_probe(probe, parse_limits(found["limits"]))
                self.assertEqual(found["selected_response_checks"], [check.specification() for check in checks])
                self.assertEqual(found["selected_response_evidence"], selected)

    def test_compact_cards_show_findings_partial_budget_and_unsupported_without_archive(self) -> None:
        for budget in (24, 280, 324):
            spec = specification()
            spec["model"] = source_specification()
            result = pipeline.run_batch([spec], Limits(max_cases=budget))[0]
            card = result.card()
            summary = object_fields(card["search"])
            self.assertTrue(summary["completion_only"])
            self.assertEqual(summary["rejection_scope"], "no_primitive_rejection_execution_diagnostics_only")
            self.assertEqual(summary["search_complete"], budget == 324)
            self.assertEqual(summary["domain_exhausted"], budget == 324)
            self.assertEqual(summary["stop_reason"], "domain_exhausted" if budget == 324 else "budget_exhausted")
            found = summary["responses"]
            assert isinstance(found, list)
            mapped = {str(object_fields(value)["response"]): object_fields(value) for value in found}
            self.assertEqual(object_fields(mapped["squared_native_weight"]["first_witness"])["coordinates"], [-1, -1])
            if budget >= 280:
                spike = object_fields(mapped["spike_49"]["first_witness"])
                self.assertEqual(spike, {"preparation_index": 70, "coordinates": [-4, -3],
                    "reference_row": {"before": "1/26", "after": "2/53", "difference_before_minus_after": "1/1378"}})
            self.assertEqual(mapped["native_weight"]["state"],
                             "no_violation_within_bounds" if budget == 324 else "inconclusive")
            encoded = canonical_json(card)
            self.assertLess(len(encoded), 4096)
            for archive_field in ("sources", "file_sha256", "native_protocol_evidence", "response_contexts"):
                self.assertNotIn(archive_field, encoded)
        unknown = pipeline.run_batch([specification(("future_response",))], Limits(max_cases=1))[0].card()
        self.assertEqual(unknown["status"], "unsupported")
        self.assertEqual(object_fields(unknown["search"])["unsupported_reason"], "unknown_selected_response")
        old = load_json(ROOT / "data/native_readout_controls.json")
        assert isinstance(old, list)
        old_card = pipeline.run_batch([old[0]], Limits(max_cases=4))[0].card()
        self.assertEqual(set(old_card), {"id", "family", "status", "reused", "checks", "artifact", "key",
                                         "proof_status", "empirical_status"})


if __name__ == "__main__":
    unittest.main()
