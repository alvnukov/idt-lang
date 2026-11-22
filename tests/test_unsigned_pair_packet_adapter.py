"""Packet observation contracts, exact coverage, and history-preserving dispatch."""

from __future__ import annotations

import copy
import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import probe_unsigned_collision_search as search
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import unsigned_pair_packet as packet
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.primitive_screen import Limits, object_fields

ROOTS = ((2, 1, 5, 0, 4, 3), (3, 1, 0, 5, 4, 2))
IMPOSTOR = (2, 1, 5, 0, 1, 3)


def specification(
    outputs: tuple[int, ...] = ROOTS[0], contract: str = "resolved_packets",
    identifier: str = "packet_candidate",
) -> dict[str, object]:
    return {
        "id": identifier, "family": "unsigned_pair_packet", "outputs": list(outputs),
        "observation_contract": contract,
    }


def checks(report: dict[str, object]) -> list[dict[str, object]]:
    values = report["checks"]
    if not isinstance(values, list):
        raise TypeError("checks must be an array")
    return [object_fields(value) for value in values]


class UnsignedPairPacketAdapterTests(unittest.TestCase):
    def test_strict_parser_round_trip_and_malformed_inputs(self) -> None:
        spec = specification()
        candidate = pipeline.parse_hypothesis(spec)
        self.assertIsInstance(candidate, packet.UnsignedPairPacket)
        self.assertEqual(candidate.specification(), spec)
        bad: list[object] = [None, [], True, {**spec, "extra": 1}]
        bad.extend({key: value for key, value in spec.items() if key != missing} for missing in spec)
        invalid_fields: dict[str, list[object]] = {
            "outputs": [None, 1, ROOTS[0], [], [0] * 5, [0] * 7,
                        [0, 1, 2, 3, 4, True], [0, 1, 2, 3, 4, 6],
                        [0, 1, 2, 3, 4, -1], [0, 1, 2, 3, 4, 1.0],
                        [0, 1, 2, 3, 4, "1"]],
            "id": [True, 1, "", "UPPER", "a" * 65],
            "family": [True, "unknown"],
            "observation_contract": [True, None, [], "pure_port_preparations", "raw"],
        }
        for field, values in invalid_fields.items():
            bad.extend({**spec, field: value} for value in values)
        for value in bad:
            with self.subTest(value=value), self.assertRaises((ValueError, TypeError)):
                pipeline.parse_hypothesis(value)
        with self.assertRaises(ValueError):
            packet.UnsignedPairPacket("bool_output", (0, 1, 2, 3, 4, True), "port_totals")
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory) / "cache"
            with self.assertRaises(ValueError):
                pipeline.run_batch([spec, {**spec, "outputs": [0]}], cache_dir=cache)
            self.assertFalse(cache.exists())

    def test_both_roots_exhaust_all_declared_observations(self) -> None:
        self.assertEqual(packet.EDGES, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)))
        self.assertEqual(packet.SWAP, (5, 1, 3, 2, 4, 0))
        self.assertEqual(packet.FIX, (1, 4))
        for outputs in ROOTS:
            for contract in ("resolved_packets", "port_totals"):
                with self.subTest(outputs=outputs, contract=contract):
                    report = pipeline.run_batch([specification(outputs, contract)])[0].report
                    self.assertEqual(report["status"], "no_counterexample_within_bounds")
                    self.assertEqual(report["proof_status"], "not_attempted")
                    self.assertEqual(report["empirical_status"], "not_tested")
                    rows = checks(report)
                    self.assertEqual([(row["checked"], row["planned"]) for row in rows], [(6, 6), (2, 2)])
                    self.assertTrue(all(row["witness"] is None for row in rows))
                    scope = object_fields(report["scope"])
                    self.assertEqual(scope["available_input_packets"], list(range(6)))
                    coverage = object_fields(scope["coverage"])
                    for row in coverage.values():
                        entry = object_fields(row)
                        self.assertTrue(entry["complete"])
                        self.assertEqual(entry["not_exercised_input_packets"], [])

    def test_coarse_impostor_is_not_rejected_by_unavailable_raw_checks(self) -> None:
        coarse, raw = pipeline.run_batch([
            specification(IMPOSTOR, "port_totals"), specification(IMPOSTOR),
        ])
        self.assertEqual(coarse.report["status"], "no_counterexample_within_bounds")
        self.assertEqual(raw.report["status"], "counterexample")
        scope = object_fields(coarse.report["scope"])
        applicability = object_fields(scope["requirement_applicability"])
        self.assertEqual(applicability["resolved_two_tick_exchange"], "not_applicable_unresolved_outputs")
        self.assertEqual(applicability["resolved_equal_input_transparency"], "not_applicable_unresolved_outputs")
        self.assertTrue(all(str(row["id"]).startswith("port_total_") for row in checks(coarse.report)))
        self.assertEqual(scope["diagnostics"], {
            "histogram_sufficient": False, "bijective": False, "square_stock": False,
        })
        # Input packet 13 is available despite sharing port totals with packet 02.
        witness = object_fields(checks(raw.report)[0]["witness"])
        inputs = object_fields(witness["inputs"])
        self.assertEqual(inputs["input_packet"], 4)
        self.assertEqual(inputs["observed_actual"], [1])
        self.assertEqual(inputs["observed_required"], [4])
        self.assertEqual((witness["actual"], witness["required"]), ("1", "=0"))

    def test_exact_rejected_table_and_first_witness_coverage(self) -> None:
        report = pipeline.run_batch([specification(packet.ID)])[0].report
        echo, transparency = checks(report)
        self.assertEqual(report["status"], "counterexample")
        self.assertEqual((echo["checked"], echo["planned"]), (1, 6))
        inputs = object_fields(object_fields(echo["witness"])["inputs"])
        self.assertEqual(inputs["input_packet"], 0)
        self.assertEqual(inputs["observed_actual"], [0])
        self.assertEqual(inputs["observed_required"], [5])
        self.assertEqual(transparency["status"], "no_counterexample_within_bounds")
        coverage = object_fields(object_fields(report["scope"])["coverage"])
        echo_coverage = object_fields(coverage["resolved_two_tick_exchange"])
        self.assertEqual(echo_coverage["tested_input_packets"], [0])
        self.assertEqual(echo_coverage["not_exercised_input_packets"], [1, 2, 3, 4, 5])
        self.assertEqual(echo_coverage["stop_reason"], "first_counterexample")

    def test_echo_roots_without_resolved_transparency_are_separately_rejected(self) -> None:
        rotation = packet.leg_table((3, 0, 1, 2))
        inverse = packet.after(rotation, packet.after(rotation, rotation))
        for outputs in (rotation, inverse):
            self.assertEqual(packet.after(outputs, outputs), packet.SWAP)
            raw, coarse = pipeline.run_batch([
                specification(outputs), specification(outputs, "port_totals"),
            ])
            self.assertEqual(
                [row["status"] for row in checks(raw.report)],
                ["no_counterexample_within_bounds", "counterexample"],
            )
            self.assertEqual(coarse.report["status"], "no_counterexample_within_bounds")

    def test_partial_budget_cannot_become_full_acceptance_or_unseen_rejection(self) -> None:
        for outputs in (ROOTS[0], IMPOSTOR):
            report = pipeline.run_batch([specification(outputs)], Limits(max_cases=1))[0].report
            self.assertEqual(report["status"], "inconclusive")
            self.assertEqual([(row["checked"], row["planned"]) for row in checks(report)], [(1, 6), (1, 2)])
            self.assertTrue(all(row["witness"] is None for row in checks(report)))
            coverage = object_fields(object_fields(report["scope"])["coverage"])
            self.assertEqual(object_fields(coverage["resolved_equal_input_transparency"])["not_exercised_input_packets"], [4])
        two = pipeline.run_batch([specification()], Limits(max_cases=2))[0].report
        self.assertEqual([row["status"] for row in checks(two)], ["inconclusive", "no_counterexample_within_bounds"])
        self.assertEqual(pipeline.exit_code(pipeline.run_batch([specification()], Limits(max_cases=1))), 3)

    def test_shared_core_preserves_entire_census_without_search_during_evaluation(self) -> None:
        self.assertIs(search.check_table, packet.check_table)
        census = search.search()
        self.assertEqual(census.counts, {
            "all": 46656, "histogram_sufficient": 318, "bijective": 720,
            "square_stock": 48, "bijective_histogram": 48, "coarse_echo": 144,
            "coarse_transparent": 8, "raw_echo": 4, "transparent_root": 2,
        })
        self.assertEqual(census.roots, ROOTS)
        self.assertEqual(census.coarse_nonraw, IMPOSTOR)
        with patch.object(search, "search", side_effect=AssertionError("exhaustive search executed")):
            self.assertEqual(pipeline.run_batch([specification()])[0].report["status"], "no_counterexample_within_bounds")

    def test_cache_replay_and_source_provenance(self) -> None:
        module_path = "theory_experiments/unsigned_pair_packet.py"
        self.assertIn(module_path, pipeline.SOURCE_PATHS)
        expected_hash = hashlib.sha256((pipeline.ROOT / module_path).read_bytes()).hexdigest()
        self.assertEqual(object_fields(pipeline.provenance()["source_sha256"])[module_path], expected_hash)
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory)
            spec = specification(IMPOSTOR, "port_totals")
            first = pipeline.run_batch([spec], cache_dir=cache)[0]
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache hit executed")):
                hit = pipeline.run_batch([spec], cache_dir=cache)[0]
            self.assertTrue(hit.reused)
            self.assertEqual(first.report, hit.report)
            if hit.artifact is None:
                self.fail("cache artifact missing")
            self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            changed_contract = pipeline.run_batch([specification(IMPOSTOR)], cache_dir=cache)[0]
            self.assertNotEqual(first.key, changed_contract.key)
            self.assertFalse(changed_contract.reused)
            self.assertEqual(changed_contract.report["status"], "counterexample")
            stale = copy.deepcopy(pipeline.provenance())
            hashes = object_fields(stale["source_sha256"])
            hashes[module_path] = "0" * 64
            stale["source_sha256"] = hashes
            with patch.object(pipeline, "provenance", return_value=stale), self.assertRaisesRegex(ValueError, "sources changed"):
                pipeline.run_batch([spec], cache_dir=cache)
            self.assertEqual(len(list(cache.glob("*.json"))), 2)

    def test_temporary_history_detects_regressions_without_replacing_baselines(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            specs: list[object] = [
                specification(identifier="good"),
                specification(IMPOSTOR, "port_totals", "coarse"),
                specification(IMPOSTOR, "resolved_packets", "rejected"),
            ]
            run = record_batch(specs, history=history, fresh=True)
            record_batch([specification(identifier="partial")], Limits(max_cases=1), history=history, fresh=True)
            before = {p: p.read_bytes() for p in history.root.rglob("*") if p.is_file()}
            replay = recheck_history(history)
            self.assertEqual(replay["status"], "unchanged")
            self.assertEqual(replay["evaluation_status_counts"], {
                "no_counterexample_within_bounds": 2, "counterexample": 1, "inconclusive": 1,
            })
            self.assertEqual(before, {p: p.read_bytes() for p in history.root.rglob("*") if p.is_file()})
            original = pipeline.compute

            def flipped(candidate: pipeline.Hypothesis, limits: Limits,
                        request: dict[str, object]) -> dict[str, object]:
                report = original(candidate, limits, request)
                if candidate.id in ("good", "rejected"):
                    report["status"] = "counterexample" if candidate.id == "good" else "no_counterexample_within_bounds"
                return report

            with patch.object(pipeline, "compute", side_effect=flipped):
                changed = recheck_history(history, record=True)
            self.assertEqual(changed["status"], "review_required")
            differences = changed["changes"]
            if not isinstance(differences, list):
                self.fail("history differences must be an array")
            self.assertEqual(len(differences), 2)
            self.assertTrue(all(path.read_bytes() == raw for path, raw in before.items()))
            self.assertEqual(history.baseline(run.submission)["reports"], [r.report for r in run.results])
            self.assertEqual(recheck_history(history)["status"], "unchanged")


if __name__ == "__main__":
    unittest.main()
