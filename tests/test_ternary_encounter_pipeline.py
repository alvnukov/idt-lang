"""Exact request binding, finite replay and source-only isolation for the encounter adapter."""

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text
from theory_experiments.ternary_encounter import CHECK_ID, SCOPE, TernaryEncounter


def spec(rule="anchored"):
    return {"id": "tag_test", "family": "ternary_encounter", "rule": rule, "marked_ports": [4, 3],
            "observations": [{"packets": [9, 0, 0], "vertex": 30, "count": 2},
                             {"packets": [3, 10, 3], "vertex": 29, "count": 2}]}


class EncounterPipelineTests(unittest.TestCase):
    def test_finite_candidate_does_not_upgrade_an_archived_source(self):
        body = "-- an independent tag count still needs to be supplied\n"
        retained = {"id": "paper_only", "family": "source_theory", "role": "primitive_base",
                    "components": ["ternary_encounter"], "declared_status": "unassessed",
                    "missing_bridges": ["independent tag counts"],
                    "sources": [SourceSnapshot("Proofs/Example.lean", 1, 1, sha256_text(body), body).specification()]}
        yes, no, idle, unresolved = pipeline.run_batch([spec("relative"), spec(), spec("idle"), retained])
        self.assertEqual([r.report["status"] for r in (yes, no, idle, unresolved)],
                         ["no_counterexample_within_bounds", "counterexample", "counterexample", "unsupported"])
        self.assertEqual(unresolved.report["scope"]["adapter_status"], "missing")
        for r in (yes, no, idle):
            self.assertEqual([c["id"] for c in r.report["checks"]], [CHECK_ID])
            self.assertEqual((r.report["rejection_scope"], r.report["proof_status"], r.report["empirical_status"],
                              r.report["scope"]["scientific_status"]), (SCOPE, "not_attempted", "not_tested", "unassessed"))

    def test_type_normalization_limits_and_request_binding_before_evaluation(self):
        class DerivedCandidate(TernaryEncounter):
            pass

        class DerivedLimits(Limits):
            pass

        c = pipeline.parse_hypothesis(spec())
        req = pipeline.request_for(c, Limits(), pipeline.provenance())
        other = pipeline.parse_hypothesis(spec("relative"))
        with patch.object(pipeline, "evaluate_ternary_encounter", side_effect=AssertionError("unbound call")):
            for obj, limits, request in (
                (DerivedCandidate(**vars(c)), Limits(), req), (c, DerivedLimits(), req),
                (other, Limits(), req), (c, Limits(), {**req, "candidate": spec()}),
                (c, Limits(), {**req, "limits": {**req["limits"], "coefficient_radius": True}}),
                (c, Limits(), {**req, "schema": "bad"}), (c, Limits(), {**req, "extra": 1}),
                (c, Limits(max_cases=1), req),
            ):
                with self.assertRaisesRegex(ValueError, "candidate/limits"):
                    pipeline.compute(obj, limits, request)
            with self.assertRaisesRegex(ValueError, "candidate/limits"):
                pipeline.run_batch([spec()], DerivedLimits())

    def test_fresh_warm_replay_and_partial_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            good, = pipeline.run_batch([spec()], cache_dir=root)
            limited, = pipeline.run_batch([spec()], Limits(max_cases=1), root)
            self.assertNotEqual(good.key, limited.key)
            self.assertEqual((limited.report["status"], limited.report["checks"][0]["checked"]), ("inconclusive", 1))
            normalized = pipeline.parse_hypothesis(spec()).specification()
            with patch.object(pipeline, "evaluate_ternary_encounter", wraps=pipeline.evaluate_ternary_encounter) as evaluate:
                warm, = pipeline.run_batch([normalized], cache_dir=root)
                self.assertTrue(warm.reused)
                self.assertEqual(warm.key, good.key)
                self.assertEqual(evaluate.call_count, 1)
            self.assertEqual(pipeline.replay_artifact(good.artifact), good.report)
            bad = {**good.report, "request": limited.report["request"]}
            path = root / "wrong-budget.json"
            with self.assertRaisesRegex(ValueError, "cached ternary encounter"):
                pipeline.publish(path, bad, bad["request"])
            self.assertFalse(path.exists())

    def test_source_pins_block_stale_disk_and_false_offline_hashes(self):
        pins = ("theory_experiments/ternary_encounter.py", "theory_experiments/primitive_screen.py",
                "theory_experiments/candidate_pipeline.py")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result, = pipeline.run_batch([spec()], cache_dir=root)
            req = result.report["request"]
            candidate = pipeline.parse_hypothesis(spec())
            original = Path.read_bytes
            for pin in pins:
                target = pipeline.ROOT / pin
                actual = original(target)
                self.assertEqual(req["provenance"]["source_sha256"][pin], hashlib.sha256(actual).hexdigest())
                forged = copy.deepcopy(req)
                forged["provenance"]["source_sha256"][pin] = "0" * 64
                with self.assertRaisesRegex(ValueError, "ternary encounter source changed"):
                    pipeline.read_entry(result.artifact, forged)

                def stale(p, actual=actual, target=target):
                    return actual + b"\n" if p == target else original(p)
                with patch.object(Path, "read_bytes", stale):
                    for call in (lambda: pipeline.run_batch([spec()], cache_dir=root / "absent"),
                                 lambda: pipeline.compute(candidate, Limits(), req),
                                 lambda: pipeline.read_entry(result.artifact, req),
                                 lambda: pipeline.replay_artifact(result.artifact)):
                        with self.subTest(pin=pin), self.assertRaisesRegex(ValueError, "ternary encounter source changed"):
                            call()
            self.assertFalse((root / "absent").exists())

    def test_rehashed_wrong_finite_results_and_status_promotions_fail_all_routes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result, = pipeline.run_batch([spec()], cache_dir=root)
            pristine = result.artifact.read_bytes()
            req = result.report["request"]
            never = root / "not-published.json"
            for keys, replacement in (
                (("scope", "comparisons", 0, "predicted_count"), 0),
                (("scope", "distinct_triggering_preparations"), 17),
                (("checks", 0, "witness", "actual"), "0"),
                (("status",), "no_counterexample_within_bounds"),
                (("checks", 0, "checked"), 1), (("empirical_status",), "tested"),
                (("proof_status",), "proved"), (("scope", "scientific_status"), "confirmed"),
            ):
                envelope = json.loads(pristine)
                obj = envelope["report"]
                for key in keys[:-1]:
                    obj = obj[key]
                obj[keys[-1]] = replacement
                envelope["report_sha256"] = pipeline.digest(envelope["report"])
                encoded = canonical_json(envelope).encode()
                result.artifact.write_bytes(encoded)
                for call in (lambda: pipeline.run_batch([spec()], cache_dir=root),
                             lambda report=envelope["report"]: pipeline.publish(never, report, req),
                             lambda: pipeline.read_entry(result.artifact, req),
                             lambda: pipeline.replay_artifact(result.artifact)):
                    with self.subTest(keys=keys), self.assertRaisesRegex(ValueError, "cached ternary encounter"):
                        call()
                self.assertFalse(never.exists())
                self.assertEqual(result.artifact.read_bytes(), encoded)


if __name__ == "__main__":
    unittest.main()
