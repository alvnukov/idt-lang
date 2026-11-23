"""Bounded replay of exact ledger decisions, including unsupported and incomplete receipts."""

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tests.test_operational_probability_ledger import ledger, six
from theory_experiments import candidate_pipeline as pipe
from theory_experiments.operational_probability_ledger import (
    CHECK_ID,
    SCOPE,
    OperationalProbabilityLedger,
    verify_ledger_certificate,
)
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text


class LedgerPipelineTests(unittest.TestCase):
    def setUp(self):
        pipe._ledger_body_digests.clear()
        self.addCleanup(pipe._ledger_body_digests.clear)

    def test_scope_separate_denominators_budget_and_archived_source(self):
        body = "-- a proposed event link is not a ledger\n"
        source = {"id": "retained", "family": "source_theory", "role": "primitive_base",
                  "components": ["operational_probability_ledger"], "declared_status": "unassessed",
                  "missing_bridges": ["an operational ledger"],
                  "sources": [SourceSnapshot("Proofs/Example.lean", 1, 1, sha256_text(body), body).specification()]}
        feasible, impossible, conditioned, retained = pipe.run_batch(
            [six("1/5"), six(0), six(0, "separately_postselected"), source])
        short, = pipe.run_batch([six(0)], Limits(max_cases=1))
        self.assertEqual([r.report["status"] for r in (feasible, impossible, conditioned, short, retained)],
                         ["no_counterexample_within_bounds", "counterexample", "unsupported", "inconclusive", "unsupported"])
        self.assertEqual(retained.report["scope"]["adapter_status"], "missing")
        self.assertEqual(short.report["scope"]["completed_pivots"], 1)
        for r in (feasible, impossible, conditioned, short):
            check, = r.report["checks"]
            self.assertEqual((check["id"], r.report["rejection_scope"], r.report["proof_status"],
                              r.report["empirical_status"]), (CHECK_ID, SCOPE, "not_attempted", "not_tested"))
            cert = r.report["scope"]["checked_certificate"]
            if r is feasible or r is impossible:
                self.assertTrue(verify_ledger_certificate(pipe.parse_hypothesis(r.report["request"]["candidate"]), cert))
            else:
                self.assertIsNone(cert)
                self.assertIsNone(check["witness"])

    def test_exact_binding_cross_type_and_sorted_request_before_solving(self):
        class Derived(OperationalProbabilityLedger):
            pass

        class OtherLimits(Limits):
            pass

        raw = six(0)
        c = pipe.parse_hypothesis(raw)
        req = pipe.request_for(c, Limits(), pipe.provenance())
        alternate = pipe.parse_hypothesis(six(0, "separately_postselected"))
        other = pipe.parse_hypothesis({"id": "other", "family": "ternary_encounter", "rule": "idle",
                                      "marked_ports": [3, 4], "observations": [{"packets": [0, 0, 0], "vertex": 0, "count": 3}]})
        wrong_request = pipe.request_for(other, Limits(), pipe.provenance())
        with patch.object(pipe, "evaluate_operational_probability_ledger", side_effect=AssertionError("unbound solve")):
            for subject, budget, request in (
                (Derived(**vars(c)), Limits(), req), (c, OtherLimits(), req), (c, Limits(max_cases=1), req),
                (alternate, Limits(), req), (c, Limits(), wrong_request), (other, Limits(), req),
                (c, Limits(), {**req, "candidate": raw}), (c, Limits(), {**req, "schema": "wrong"}),
                (c, Limits(), {**req, "limits": {**req["limits"], "coefficient_radius": True}}),
            ):
                with self.assertRaisesRegex(ValueError, "operational probability ledger candidate/limits"):
                    pipe.compute(subject, budget, request)
            with self.assertRaisesRegex(ValueError, "candidate/limits"):
                pipe.run_batch([raw], OtherLimits())

    def test_cold_warm_fresh_and_eviction_do_not_trust_a_saved_digest(self):
        raw = six(0)
        with tempfile.TemporaryDirectory() as tmp, patch.object(pipe, "_LEDGER_DIGEST_CAP", 2), patch.object(
                pipe, "evaluate_operational_probability_ledger", wraps=pipe.evaluate_operational_probability_ledger) as solve:
            root = Path(tmp)
            original, = pipe.run_batch([raw], cache_dir=root)
            self.assertEqual(solve.call_count, 1)  # publishing the freshly computed report does not rerun
            warm, = pipe.run_batch([pipe.parse_hypothesis(raw).specification()], cache_dir=root)
            self.assertTrue(warm.reused)
            self.assertEqual((warm.key, solve.call_count), (original.key, 1))
            for cid in ("another", "third"):
                pipe.run_batch([{**raw, "id": cid}])
            self.assertEqual(len(pipe._ledger_body_digests), 2)
            self.assertNotIn(original.key, pipe._ledger_body_digests)
            self.assertEqual(pipe.read_entry(original.artifact, original.report["request"]), original.report)
            self.assertEqual(solve.call_count, 4)
            pipe.run_batch([raw], cache_dir=root)
            self.assertEqual(solve.call_count, 4)
            self.assertEqual(pipe.replay_artifact(original.artifact), original.report)
            self.assertEqual(solve.call_count, 5)
            fresh, = pipe.run_batch([raw], cache_dir=root, fresh=True)
            self.assertFalse(fresh.reused)
            self.assertEqual(solve.call_count, 6)

    def test_rehashed_certificate_telemetry_and_unearned_negative_positive_decisions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            feasible, impossible, conditioned = pipe.run_batch([six("1/5"), six(0), six(0, "separately_postselected")],
                                                              cache_dir=root)
            short, = pipe.run_batch([six(0)], Limits(max_cases=1), root)
            cases = [(feasible, ("scope", "checked_certificate", "values"), ["0"] * feasible.report["scope"]["variables"]),
                     (impossible, ("scope", "checked_certificate", "weights"), []),
                     (impossible, ("checks", 0, "witness", "actual"), "0"),
                     (conditioned, ("status",), "counterexample"), (conditioned, ("scope", "basis"), "all_attempts"),
                     (short, ("scope", "completed_pivots"), 2), (short, ("status",), "no_counterexample_within_bounds"),
                     (feasible, ("empirical_status",), "tested"), (feasible, ("scope", "coefficient_updates_charged"), 0)]
            for result, keys, val in cases:
                pristine = result.artifact.read_bytes()
                envelope = json.loads(pristine)
                req = envelope["report"]["request"]
                obj = envelope["report"]
                for k in keys[:-1]:
                    obj = obj[k]
                obj[keys[-1]] = val
                envelope["report_sha256"] = pipe.digest(envelope["report"])
                data = canonical_json(envelope).encode()
                result.artifact.write_bytes(data)
                for known in (True, False):
                    if not known:
                        pipe._ledger_body_digests.clear()
                    with self.subTest(keys=keys, warm=known), self.assertRaisesRegex(ValueError, "cached operational"):
                        pipe.read_entry(result.artifact, req)
                with self.assertRaisesRegex(ValueError, "cached operational"):
                    pipe.run_batch([req["candidate"]], pipe.parse_limits(req["limits"]), root)
                with self.assertRaisesRegex(ValueError, "cached operational"):
                    pipe.replay_artifact(result.artifact)
                with self.assertRaisesRegex(ValueError, "cached operational"):
                    pipe.publish(root / "forgery", envelope["report"], req)
                self.assertFalse((root / "forgery").exists())
                self.assertEqual(result.artifact.read_bytes(), data)
                result.artifact.write_bytes(pristine)
            # A valid higher-budget certificate still does not attest a short
            # run; relabeling a real refusal as a legitimate decision also fails.
            for real, target in ((impossible, short), (conditioned, impossible), (impossible, conditioned)):
                req = target.report["request"]
                with self.assertRaisesRegex(ValueError, "cached operational"):
                    pipe.publish(root / "swapped", {**real.report, "request": req}, req)
            self.assertFalse((root / "swapped").exists())

    def test_loaded_checker_core_and_primitive_pins_apply_even_on_memory_hits(self):
        raw = ledger([("s", "ab")])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cold, = pipe.run_batch([raw], cache_dir=root)
            req = cold.report["request"]
            c = pipe.parse_hypothesis(raw)
            original_read = Path.read_bytes
            for rel in ("theory_experiments/operational_probability_ledger.py",
                        "theory_experiments/primitive_screen.py", "theory_experiments/candidate_pipeline.py"):
                path = pipe.ROOT / rel
                actual = original_read(path)
                self.assertEqual(req["provenance"]["source_sha256"][rel], hashlib.sha256(actual).hexdigest())
                forged = copy.deepcopy(req)
                forged["provenance"]["source_sha256"][rel] = "0"*64
                with self.assertRaisesRegex(ValueError, "ledger source changed"):
                    pipe.read_entry(cold.artifact, forged)

                def newer(p, path=path, actual=actual):
                    return actual+b"\n" if p == path else original_read(p)
                with patch.object(Path, "read_bytes", newer):
                    for call in (lambda: pipe.run_batch([raw], cache_dir=root / "missing"),
                                 lambda: pipe.compute(c, Limits(), req),
                                 lambda: pipe.read_entry(cold.artifact, req),
                                 lambda: pipe.replay_artifact(cold.artifact)):
                        with self.subTest(source=rel), self.assertRaisesRegex(ValueError, "ledger source changed"):
                            call()
            self.assertFalse((root / "missing").exists())


if __name__ == "__main__":
    unittest.main()
