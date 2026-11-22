"""Generated lower-primitive tables, calibration quantifiers and bounded coverage."""

from __future__ import annotations

import ast
import copy
import hashlib
import json
import tempfile
import unittest
from itertools import product
from pathlib import Path
from unittest.mock import patch

from scripts import probe_opposition_clock_scatter as frozen
from scripts import probe_three_opposition_origin as origin
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import opposition_flag as opposition
from theory_experiments import unsigned_pair_packet as packet
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.primitive_screen import Limits, object_fields


def specification(
    flag: tuple[int, int] = (0, 4),
    extension: str = "transparent_spare",
    label_contract: str = "fixed_calibration",
    observation: str = "resolved_packets",
    identifier: str = "opposition_candidate",
) -> dict[str, object]:
    result: dict[str, object] = {
        "id": identifier,
        "family": "opposition_flag",
        "flag": list(flag),
        "data_extension": extension,
        "observation_contract": observation,
        "label_contract": label_contract,
    }
    if label_contract == "fixed_calibration":
        result["leg_labels"] = [0, 1, 2, 3]
    return result


def evaluate(spec: dict[str, object], budget: int = 1000) -> dict[str, object]:
    return pipeline.run_batch([spec], Limits(max_cases=budget))[0].report


def one_check(report: dict[str, object]) -> dict[str, object]:
    values = report["checks"]
    if not isinstance(values, list) or len(values) != 1:
        raise TypeError("one quantified packet check required")
    return object_fields(values[0])


class OppositionFlagAdapterTests(unittest.TestCase):
    def test_strict_parser_and_round_trip(self) -> None:
        spec = specification()
        parsed = pipeline.parse_hypothesis(spec)
        self.assertIsInstance(parsed, opposition.OppositionFlag)
        self.assertEqual(parsed.specification(), spec)
        bad: list[object] = [None, [], True, {**spec, "outputs": list(packet.ID)}]
        bad.extend(
            {key: value for key, value in spec.items() if key != missing}
            for missing in spec
        )
        invalid: dict[str, list[object]] = {
            "id": [True, 1, "", "UPPER"],
            "family": [True, "wrong"],
            "flag": [
                None,
                (0, 4),
                [],
                [0],
                [0, 2, 4],
                [0, 0],
                [0, 1],
                [True, 4],
                [0, 6],
                [0, -1],
                [0, 4.0],
            ],
            "leg_labels": [
                None,
                (0, 1, 2, 3),
                [],
                [0, 1, 2],
                [0, 1, 2, 2],
                [0, 1, 2, True],
                [0, 1, 2, 4],
            ],
            "data_extension": [True, None, [], "natural_backtrack", "table_is_correct"],
            "observation_contract": [True, None, [], "pure_ports"],
            "label_contract": [True, None, [], "unknown"],
        }
        for field, values in invalid.items():
            bad.extend({**spec, field: value} for value in values)
        for quantifier in ("exists_s4", "all_s4"):
            quantified = specification(label_contract=quantifier)
            self.assertEqual(
                pipeline.parse_hypothesis(quantified).specification(), quantified
            )
            bad.append({**quantified, "leg_labels": [0, 1, 2, 3]})
        for item in bad:
            with self.subTest(item=item), self.assertRaises((ValueError, TypeError)):
                pipeline.parse_hypothesis(item)
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            with self.assertRaises(ValueError):
                pipeline.run_batch([spec, {**spec, "flag": [0, 1]}], cache_dir=cache)
            self.assertFalse(cache.exists())

    def test_pure_core_agrees_with_frozen_probes(self) -> None:
        self.assertEqual(opposition.FLAGS, frozen.FLAGS)
        self.assertEqual(opposition.G, frozen.G)
        self.assertEqual(opposition.SHEET, origin.SHEET)
        self.assertEqual(opposition.DUAL, origin.DUAL)
        self.assertEqual(opposition.LITERAL_EDGES, origin.EDGES)
        for perm in frozen.G:
            self.assertEqual(opposition.chart(perm), frozen.chart(perm))
        for flag in frozen.FLAGS:
            for flip in (False, True):
                self.assertEqual(
                    opposition.extend(*flag, flip), frozen.extend(*flag, flip)
                )
                self.assertEqual(
                    opposition.extend(flag[1], flag[0] ^ 1, flip),
                    opposition.extend(*flag, flip),
                )
        source = ast.parse(
            (pipeline.ROOT / "theory_experiments/opposition_flag.py").read_text()
        )
        for node in ast.walk(source):
            if isinstance(node, ast.ImportFrom):
                self.assertFalse((node.module or "").startswith("scripts"))
            elif isinstance(node, ast.Import):
                self.assertTrue(
                    all(not item.name.startswith("scripts") for item in node.names)
                )

    def test_every_generated_table_matches_independent_cube_incidence(self) -> None:
        # This oracle rebuilds binary completions independently; it does not
        # use the production edge encoding or its generated table internals.
        vertices = tuple(
            bits for bits in product((0, 1), repeat=3) if sum(bits) % 2 == 0
        )
        for flag in frozen.FLAGS:
            for extension in ("transparent_spare", "flip_spare", "passive_chart"):
                route = (
                    tuple(range(6))
                    if extension == "passive_chart"
                    else frozen.extend(*flag, extension == "flip_spare")
                )
                for labels in opposition.S4:
                    model = opposition.parse_opposition_flag(
                        {**specification(flag, extension), "leg_labels": list(labels)}
                    )
                    generated = opposition.generate_table(
                        model.flag, model.data_extension, labels
                    )
                    expected = [-1] * 6
                    for literal in range(6):
                        before = tuple(
                            sorted(
                                labels[i]
                                for i, bits in enumerate(vertices)
                                if bits[literal // 2] == literal % 2
                            )
                        )
                        target = route[literal]
                        after = tuple(
                            sorted(
                                labels[i]
                                for i, bits in enumerate(vertices)
                                if bits[target // 2] == target % 2
                            )
                        )
                        expected[packet.EDGES.index((before[0], before[1]))] = (
                            packet.EDGES.index((after[0], after[1]))
                        )
                    self.assertEqual(generated, tuple(expected))
                    oracle = packet.check_table(generated)
                    actual = opposition.calibration_test(model, labels)
                    self.assertEqual(
                        actual["satisfies_both_requirements"],
                        oracle["transparent_root"],
                    )

    def test_control_batch_and_non_nominal_evaluation(self) -> None:
        values: object = json.loads(
            (pipeline.ROOT / "data/opposition_flag_controls.json").read_text()
        )
        self.assertIsInstance(values, list)
        if not isinstance(values, list):
            self.fail("control batch must be a JSON array")
        results = pipeline.run_batch(values)
        self.assertEqual(
            [result.report["status"] for result in results],
            [
                "no_counterexample_within_bounds",
                "counterexample",
                "no_counterexample_within_bounds",
                "counterexample",
                "counterexample",
            ],
        )
        first = evaluate(specification())
        renamed = evaluate(specification(identifier="misleading_rejected_name"))
        self.assertEqual(first["checks"], renamed["checks"])
        self.assertEqual(first["scope"], renamed["scope"])
        with patch.object(opposition, "generate_table", return_value=packet.ID):
            self.assertEqual(evaluate(specification())["status"], "counterexample")
        for result in results:
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")

    def test_calibration_quantifiers_are_not_interchanged(self) -> None:
        fixed = evaluate(specification((0, 2)))
        exists = evaluate(specification((0, 2), label_contract="exists_s4"))
        universal = evaluate(specification((0, 2), label_contract="all_s4"))
        self.assertEqual(
            [r["status"] for r in (fixed, exists, universal)],
            ["counterexample", "no_counterexample_within_bounds", "counterexample"],
        )
        scope = object_fields(exists["scope"])
        self.assertEqual(scope["viable_calibration"], [0, 1, 3, 2])
        self.assertFalse(scope["domain_exhausted"])
        self.assertTrue(scope["quantified_requirement_resolved"])
        self.assertEqual(
            (one_check(exists)["checked"], one_check(exists)["planned"]), (16, 192)
        )
        self.assertIsNone(one_check(exists)["witness"])
        for flag in opposition.FLAGS:
            model = opposition.parse_opposition_flag(
                specification(flag, label_contract="exists_s4")
            )
            viable = [
                labels
                for labels in opposition.S4
                if opposition.calibration_test(model, labels)[
                    "satisfies_both_requirements"
                ]
            ]
            self.assertEqual(len(viable), 8)
            self.assertEqual(
                opposition.evaluate_opposition_flag(model, Limits())[0][0].status,
                "no_counterexample_within_bounds",
            )

    def test_unlabeled_rejection_requires_eliminating_all_calibrations(self) -> None:
        for extension in ("flip_spare", "passive_chart"):
            spec = specification(extension=extension, label_contract="exists_s4")
            partial = evaluate(spec, 191)
            complete = evaluate(spec, 192)
            self.assertEqual(partial["status"], "inconclusive")
            self.assertEqual(one_check(partial)["checked"], 184)
            self.assertIsNone(one_check(partial)["witness"])
            self.assertEqual(complete["status"], "counterexample")
            self.assertEqual(one_check(complete)["checked"], 192)
            witness = object_fields(one_check(complete)["witness"])
            failed = object_fields(witness["inputs"])["failed_calibrations"]
            self.assertIsInstance(failed, list)
            if isinstance(failed, list):
                self.assertEqual(len(failed), 24)

    def test_atomic_observation_budget_is_explicit(self) -> None:
        for budget in (1, 7):
            report = evaluate(specification(), budget)
            self.assertEqual(report["status"], "inconclusive")
            self.assertEqual(one_check(report)["checked"], 0)
            self.assertEqual(object_fields(report["scope"])["calibrations"], [])
        self.assertEqual(
            evaluate(specification(), 8)["status"], "no_counterexample_within_bounds"
        )
        spec = specification((0, 2), label_contract="exists_s4")
        self.assertEqual(evaluate(spec, 15)["status"], "inconclusive")
        self.assertEqual(
            evaluate(spec, 16)["status"], "no_counterexample_within_bounds"
        )
        universal = specification(label_contract="all_s4")
        self.assertEqual(evaluate(universal, 8)["status"], "inconclusive")
        self.assertEqual(evaluate(universal)["status"], "counterexample")

    def test_active_passive_and_output_resolution_remain_visible(self) -> None:
        raw = evaluate(specification(extension="flip_spare"))
        coarse = evaluate(
            specification(extension="flip_spare", observation="port_totals")
        )
        self.assertEqual(raw["status"], "counterexample")
        self.assertEqual(coarse["status"], "no_counterexample_within_bounds")
        passive = evaluate(specification(extension="passive_chart"))
        scope = object_fields(passive["scope"])
        self.assertFalse(scope["active_record_coupling"])
        self.assertEqual(scope["physical_record_route"], list(range(6)))
        for labels in opposition.S4:
            self.assertEqual(
                opposition.generate_table((0, 4), "passive_chart", labels), packet.ID
            )
        witness = object_fields(object_fields(one_check(raw)["witness"])["inputs"])
        failure = object_fields(witness["first_failure"])
        self.assertEqual(failure["ticks"], 1)

    def test_cache_replay_provenance_and_scratch_history(self) -> None:
        path = "theory_experiments/opposition_flag.py"
        self.assertIn(path, pipeline.SOURCE_PATHS)
        self.assertEqual(
            object_fields(pipeline.provenance()["source_sha256"])[path],
            hashlib.sha256((pipeline.ROOT / path).read_bytes()).hexdigest(),
        )
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            spec = specification((0, 2), label_contract="exists_s4")
            first = pipeline.run_batch([spec], cache_dir=cache)[0]
            with patch.object(
                pipeline, "compute", side_effect=AssertionError("cache hit executed")
            ):
                hit = pipeline.run_batch([spec], cache_dir=cache)[0]
            self.assertTrue(hit.reused)
            self.assertEqual(first.report, hit.report)
            if hit.artifact is None:
                self.fail("missing cache artifact")
            self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            changed = pipeline.run_batch(
                [specification((0, 2), label_contract="all_s4")], cache_dir=cache
            )[0]
            self.assertNotEqual(first.key, changed.key)
            self.assertEqual(changed.report["status"], "counterexample")
            stale = copy.deepcopy(pipeline.provenance())
            hashes = object_fields(stale["source_sha256"])
            hashes[path] = "0" * 64
            stale["source_sha256"] = hashes
            with (
                patch.object(pipeline, "provenance", return_value=stale),
                self.assertRaisesRegex(ValueError, "sources changed"),
            ):
                pipeline.run_batch([spec], cache_dir=cache)
            history = History(Path(directory) / "history")
            record_batch(
                [spec, specification(extension="flip_spare")],
                history=history,
                fresh=True,
            )
            before = {
                file: file.read_bytes()
                for file in history.root.rglob("*")
                if file.is_file()
            }
            self.assertEqual(recheck_history(history)["status"], "unchanged")
            self.assertEqual(
                before,
                {
                    file: file.read_bytes()
                    for file in history.root.rglob("*")
                    if file.is_file()
                },
            )


if __name__ == "__main__":
    unittest.main()
