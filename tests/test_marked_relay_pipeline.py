"""Marked-relay control batch, source audit, cache replay and scratch history."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from collections.abc import Sequence
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from scripts import marked_relay_controls as controls
from scripts import probe_minimal_signal_relay as signal
from scripts import probe_shuttle_local_reunions as shuttle
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.marked_relay import MarkedRelay
from theory_experiments.primitive_screen import Limits, object_fields

PASS = "no_counterexample_within_bounds"
FAIL = "counterexample"
PENDING = "inconclusive"
MODEL_PATH = "theory_experiments/marked_relay.py"


def model_for(spec: object) -> MarkedRelay:
    model = pipeline.parse_hypothesis(spec)
    if not isinstance(model, MarkedRelay):
        raise TypeError("expected a marked relay specification")
    return model


def indexed_specs() -> dict[str, object]:
    specs: dict[str, object] = {}
    for spec in controls.control_specs():
        identifier = object_fields(spec)["id"]
        if not isinstance(identifier, str) or identifier in specs:
            raise ValueError("fixture identifiers must be unique strings")
        specs[identifier] = spec
    return specs


def one_check(result: pipeline.Result) -> dict[str, object]:
    checks = result.report["checks"]
    if not isinstance(checks, list) or len(checks) != 1:
        raise TypeError("expected one marked relay check")
    return object_fields(checks[0])


def get_scope(result: pipeline.Result) -> dict[str, object]:
    return object_fields(result.report["scope"])


class MarkedRelayPipelineTests(unittest.TestCase):
    def assert_component_isomorphic(
        self, model: MarkedRelay, source_ports: shuttle.Ports, source_origin: int
    ) -> None:
        """Recover the map via a stack; check both directions and reachability."""
        correspondence = {0: source_origin}
        reverse = {source_origin: 0}
        pending = [0]
        while pending:
            here = pending.pop()
            for port, destination in enumerate(model.transitions[here]):
                source_destination = source_ports[port][correspondence[here]]
                if destination not in correspondence:
                    pending.append(destination)
                    correspondence[destination] = source_destination
                self.assertEqual(correspondence[destination], source_destination)
                self.assertEqual(
                    reverse.setdefault(source_destination, destination), destination
                )
        self.assertEqual(len(correspondence), len(model.transitions))
        source_component = next(
            part for part in shuttle.components(source_ports) if source_origin in part
        )
        self.assertEqual(source_component, set(reverse))

    def assert_fault_path(
        self, result: pipeline.Result, expected_word: Sequence[int], origin: int
    ) -> dict[str, object]:
        check = one_check(result)
        failure = object_fields(object_fields(check["witness"])["inputs"])
        candidate = model_for(object_fields(result.report["request"])["candidate"])
        path = [origin]
        for port in expected_word:
            path.append(candidate.transitions[path[-1]][port])
        self.assertEqual(failure["origin"], origin)
        self.assertEqual(failure["word"], list(expected_word))
        self.assertEqual(failure["path"], path)
        self.assertEqual(failure["endpoint"], path[-1])
        self.assertEqual(
            failure["origin_marker_class"], candidate.marker_classes[origin]
        )
        self.assertEqual(
            failure["endpoint_marker_class"], candidate.marker_classes[path[-1]]
        )
        self.assertEqual(
            candidate.marker_classes[origin], candidate.marker_classes[path[-1]]
        )
        self.assertIs(failure["expected_return"], False)
        self.assertIs(failure["observed_return"], True)
        return failure

    def test_input_only_generator_matches_the_frozen_control_constructors(self) -> None:
        specs = indexed_specs()
        self.assertEqual(controls.CONTROL_MAX_CASES, 5000)
        for key, spec in specs.items():
            with self.subTest(key=key):
                model = model_for(spec)
                self.assertEqual(model.specification(), spec)
                self.assertEqual(model.id, key)
        output = StringIO()
        with redirect_stdout(output):
            controls.main()
        self.assertEqual(json.loads(output.getvalue()), list(specs.values()))

        small = signal.quotient_4((0, 1, 2, 3))
        large = signal.quotient_4((0, 2))
        for suffix, probe, markers, program in (
            ("32_named_six", small, tuple(range(32)), "named_six"),
            ("32_through_six", small, tuple(range(32)), "through_six"),
            ("64_through_six", large, tuple(range(64)), "through_six"),
            ("64_role_detector_through_six", large, large.role, "through_six"),
        ):
            model = model_for(specs[f"relay_{suffix}"])
            self.assertEqual(model.transitions, probe.neighbors)
            self.assertEqual(model.marker_classes, markers)
            self.assertEqual(model.program, program)

        source = shuttle.moved_mark()
        gate = source["gate"]
        if not isinstance(gate, tuple) or any(type(value) is not int for value in gate):
            self.fail("frozen moved-mark gate must be an immutable integer table")
        source_ports = shuttle.tables(4, gate)
        source_original = 4**4 + sum(2 * 4**port for port in shuttle.PORTS)
        fixed_original = model_for(specs["shuttle_105_fixed_original"])
        self.assert_component_isomorphic(fixed_original, source_ports, source_original)
        self.assertEqual(source["component_size"], len(fixed_original.transitions))
        self.assertEqual(fixed_original.marker_classes, tuple(range(105)))
        self.assertEqual(fixed_original.origin, 0)
        for suffix, contract, expected_origin in (
            ("fixed_neighbor", "fixed", fixed_original.transitions[0][0]),
            ("all_origins", "all", None),
            ("exists_origin", "exists", None),
        ):
            other = model_for(specs[f"shuttle_105_{suffix}"])
            self.assertEqual(other.transitions, fixed_original.transitions)
            self.assertEqual(other.marker_classes, fixed_original.marker_classes)
            self.assertEqual(other.origin_contract, contract)
            self.assertEqual(other.origin, expected_origin)
        cycle = model_for(specs["shuttle_128_cycle_all_origins"])
        self.assertEqual(len(cycle.transitions), 128)
        self.assertEqual(cycle.marker_classes, tuple(range(128)))
        self.assert_component_isomorphic(cycle, shuttle.tables(4, shuttle.ring(4)), 0)

    def test_fresh_full_batch_reports_scoped_results_and_replayable_witnesses(
        self,
    ) -> None:
        results = pipeline.run_batch(
            controls.control_specs(), Limits(max_cases=5000), fresh=True
        )
        indexed = {result.card()["id"]: result for result in results}
        expected = (
            ("relay_32_named_six", PASS, 36, 36, 32),
            ("relay_32_through_six", FAIL, 496, 1456, 32),
            ("relay_64_through_six", PASS, 1456, 1456, 64),
            ("relay_64_role_detector_through_six", FAIL, 5, 1456, 64),
            ("shuttle_105_fixed_original", PASS, 1456, 1456, 105),
            ("shuttle_105_fixed_neighbor", FAIL, 282, 1456, 105),
            ("shuttle_105_all_origins", FAIL, 1738, 152880, 105),
            ("shuttle_105_exists_origin", PASS, 1456, 152880, 105),
            ("shuttle_128_cycle_all_origins", PASS, 1456, 1456, 128),
        )
        self.assertEqual(tuple(indexed), tuple(row[0] for row in expected))
        for identifier, status, checked, planned, states in expected:
            with self.subTest(identifier=identifier):
                result = indexed[identifier]
                report = result.report
                check, scope = one_check(result), get_scope(result)
                self.assertEqual(check["id"], "marked_relay_return_language")
                self.assertEqual((report["status"], check["status"]), (status, status))
                self.assertEqual(
                    (check["checked"], check["planned"]), (checked, planned)
                )
                self.assertEqual(scope["state_count"], states)
                self.assertIs(scope["quantified_requirement_resolved"], True)
                self.assertEqual(report["proof_status"], "not_attempted")
                self.assertEqual(report["empirical_status"], "not_tested")
                self.assertEqual(
                    report["rejection_scope"],
                    "declared_markers_origins_and_supplied_relay_target_only",
                )
                self.assertFalse(result.reused)
                self.assertIsNone(result.artifact)

        self.assert_fault_path(indexed["relay_32_through_six"], (0, 1, 0, 2, 0, 3), 0)
        coarse = self.assert_fault_path(
            indexed["relay_64_role_detector_through_six"], (0, 1), 0
        )
        self.assertNotEqual(coarse["origin"], coarse["endpoint"])
        echo = (1, 2, 1, 2, 1)
        self.assertEqual(shuttle.moved_mark()["forbidden_echo"], echo)
        self.assert_fault_path(indexed["shuttle_105_fixed_neighbor"], echo, 1)
        self.assert_fault_path(indexed["shuttle_105_all_origins"], echo, 1)
        existential = get_scope(indexed["shuttle_105_exists_origin"])
        self.assertEqual(existential["viable_origin"], 0)
        self.assertEqual(existential["stop_reason"], "existential_origin_witness")
        self.assertIs(existential["all_origin_classes_decided"], False)
        self.assertIs(existential["trajectory_plan_exhausted"], False)

    def test_case_budget_is_separate_and_never_presumes_a_partial_result(self) -> None:
        specs = indexed_specs()
        selected = [
            specs[identifier]
            for identifier in (
                "relay_64_through_six",
                "shuttle_105_exists_origin",
                "shuttle_128_cycle_all_origins",
            )
        ]
        under = pipeline.run_batch(selected, Limits(max_cases=1455))
        exact = pipeline.run_batch(selected, Limits(max_cases=1456))
        for short, full in zip(under, exact, strict=True):
            self.assertEqual(short.report["status"], PENDING)
            self.assertEqual(one_check(short)["checked"], 1455)
            self.assertIsNone(one_check(short)["witness"])
            self.assertIs(get_scope(short)["quantified_requirement_resolved"], False)
            self.assertEqual(full.report["status"], PASS)
            self.assertEqual(one_check(full)["checked"], 1456)
            self.assertNotEqual(short.key, full.key)
            self.assertEqual(
                object_fields(short.report["request"])["candidate"],
                object_fields(full.report["request"])["candidate"],
            )

        universal = specs["shuttle_105_all_origins"]
        (short,) = pipeline.run_batch([universal], Limits(max_cases=1737))
        (full,) = pipeline.run_batch([universal], Limits(max_cases=1738))
        self.assertEqual(short.report["status"], PENDING)
        self.assertEqual(one_check(short)["checked"], 1737)
        self.assertIsNone(one_check(short)["witness"])
        self.assertEqual(full.report["status"], FAIL)
        self.assert_fault_path(full, (1, 2, 1, 2, 1), 1)

    def test_fresh_scratch_baseline_cache_reuse_replay_and_source_hash(self) -> None:
        model_hash = hashlib.sha256(
            (pipeline.ROOT / MODEL_PATH).read_bytes()
        ).hexdigest()
        self.assertIn(MODEL_PATH, pipeline.SOURCE_PATHS)
        with tempfile.TemporaryDirectory() as temporary:
            scratch = Path(temporary)
            history, cache = History(scratch / "history"), scratch / "cache"
            specs = controls.control_specs()
            limits = Limits(max_cases=controls.CONTROL_MAX_CASES)
            first = record_batch(specs, limits, cache, fresh=True, history=history)
            self.assertEqual(first.changes, [])
            self.assertEqual(
                history.baseline(first.submission)["reports"],
                [result.report for result in first.results],
            )
            before = {
                file: file.read_bytes() for file in scratch.rglob("*") if file.is_file()
            }
            with patch.object(
                pipeline, "compute", side_effect=AssertionError("cache hit executed")
            ):
                cached = pipeline.run_batch(specs, limits, cache)
            for original, hit in zip(first.results, cached, strict=True):
                self.assertFalse(original.reused)
                self.assertTrue(hit.reused)
                self.assertEqual(original.key, hit.key)
                self.assertEqual(original.report, hit.report)
                provenance = object_fields(
                    object_fields(hit.report["request"])["provenance"]
                )
                self.assertEqual(
                    object_fields(provenance["source_sha256"])[MODEL_PATH], model_hash
                )
                if hit.artifact is None:
                    self.fail("cache replay requires an artifact")
                self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            rechecked = recheck_history(history)
            self.assertEqual(rechecked["status"], "unchanged")
            self.assertEqual(rechecked["evaluation_status_counts"], {PASS: 5, FAIL: 4})
            self.assertEqual(
                rechecked["meaning"],
                "regression_comparison_not_a_physical_truth_verdict",
            )
            self.assertEqual(
                before,
                {
                    file: file.read_bytes()
                    for file in scratch.rglob("*")
                    if file.is_file()
                },
            )
