"""Bind named counters to their full ordered input stream and replay only the allowed prefix."""

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tests.test_signed_contact_stream import raw
from theory_experiments import candidate_pipeline as pipe
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.signed_contact_stream import (
    CHECK_ID,
    SCOPE,
    SignedContactStream,
)
from theory_experiments.source_candidate import SourceSnapshot, sha256_text


def sample(rule="anonymous_bucket", *, earliest=True):
    # Integrating a full pair cycle erases the temporal contrast.
    reads = [(2, "prefix", [-1, 1, 1, 1])]
    if earliest:
        reads.append((1, "step", [0, 1, 0, 0]))
    return raw(rule, 4, 0, [(0, 1), (0, 1)], reads)


class SignedStreamPipelineTests(unittest.TestCase):
    def test_raw_vectors_not_probabilities_and_no_implicit_source_adapter(self):
        text = "-- names an update, not an input stream or measured output\n"
        retained = {"id": "unspecified", "family": "source_theory", "role": "primitive_base",
                    "components": ["signed_contact_stream"], "declared_status": "unassessed",
                    "missing_bridges": ["explicit stream and counter observations"],
                    "sources": [SourceSnapshot("Proofs/Example.lean", 1, 1, sha256_text(text), text).specification()]}
        terminal, bucket, rotor, source = pipe.run_batch([sample(earliest=False), sample(),
                                                         sample("ordered_pair_rotor"), retained])
        self.assertEqual([r.report["status"] for r in (terminal, bucket, rotor, source)],
                         ["no_counterexample_within_bounds", "counterexample", "no_counterexample_within_bounds", "unsupported"])
        self.assertEqual(source.report["scope"]["adapter_status"], "missing")
        for r in (terminal, rotor, bucket):
            self.assertEqual(r.report["checks"][0]["id"], CHECK_ID)
            self.assertEqual((r.report["rejection_scope"], r.report["empirical_status"], r.report["proof_status"],
                              r.report["scope"]["scientific_status"]), (SCOPE, "not_tested", "not_attempted", "unassessed"))
        self.assertEqual(bucket.report["scope"]["comparisons"][-1]["predicted_counts"], [-1, 1, 1, 1])

    def test_cache_keys_normalize_reads_but_bind_arrival_order_phase_sign_and_scope(self):
        spec = raw("ordered_pair_rotor", 4, 1, [(0, -1), (3, 1)], [(2, "prefix", [1, 0, 0, -1]), (1, "step", [0]*4)])
        c = pipe.parse_hypothesis(spec)
        norm = c.specification()
        reversed_input = {**norm, "inputs": list(reversed(norm["inputs"]))}
        changed_sign = {**norm, "inputs": [{"port": 0, "sign": 1}, norm["inputs"][1]]}
        changed_scope = {**norm, "readouts": [{**norm["readouts"][0], "scope": "prefix"}, norm["readouts"][1]]}
        different = [reversed_input, changed_sign, changed_scope, {**norm, "initial_phase": 2},
                     {**norm, "rule": "anonymous_bucket"}]
        results = pipe.run_batch([spec, norm, *different])
        self.assertEqual(results[0].key, results[1].key)
        self.assertTrue(results[1].reused)
        self.assertEqual(len({r.key for r in results}), len(results)-1)
        req = results[0].report["request"]

        class Derived(SignedContactStream):
            pass

        class OtherLimits(Limits):
            pass

        other = pipe.parse_hypothesis({"id": "other", "family": "ternary_encounter", "rule": "idle",
                                      "marked_ports": [3, 4], "observations": [{"packets": [0, 0, 0], "vertex": 0, "count": 3}]})
        with patch.object(pipe, "evaluate_signed_contact_stream", side_effect=AssertionError("unbound execution")):
            for target, bounds, request in (
                (c, Limits(), {**req, "candidate": spec}), (Derived(**vars(c)), Limits(), req),
                (c, OtherLimits(), req), (c, Limits(max_cases=1), req), (other, Limits(), req),
                (c, Limits(), pipe.request_for(other, Limits(), req["provenance"])),
                (c, Limits(), {**req, "limits": {**req["limits"], "max_copies": True}}),
                *((c, Limits(), {**req, "candidate": s}) for s in different),
            ):
                with self.assertRaisesRegex(ValueError, "signed contact stream candidate/limits"):
                    pipe.compute(target, bounds, request)
            with self.assertRaisesRegex(ValueError, "candidate/limits"):
                pipe.run_batch([spec], OtherLimits())

    def test_partial_budget_and_warm_replay_with_no_uncomputed_history(self):
        # Provisional mismatch at step one, unobserved suffix. Finishing all
        # requested reads does not license promoting the incomplete stream.
        spec = raw("idle_wire", 2, 0, [(0, 1), (1, -1)], [(1, "step", [0, 1])])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            short, = pipe.run_batch([spec], Limits(max_cases=1), root)
            full, = pipe.run_batch([spec], Limits(max_cases=2), root)
            self.assertNotEqual(short.key, full.key)
            ck, = short.report["checks"]
            self.assertEqual((short.report["status"], ck["checked"], ck["planned"], ck["witness"]),
                             ("inconclusive", 1, 1, None))
            self.assertEqual(short.report["scope"]["model_prefix_after_consumed_inputs"], [1, 0])
            self.assertEqual(full.report["scope"]["model_prefix_after_consumed_inputs"], [1, -1])
            self.assertEqual(full.report["status"], "counterexample")
            with patch.object(pipe, "evaluate_signed_contact_stream", wraps=pipe.evaluate_signed_contact_stream) as run:
                warm, = pipe.run_batch([spec], Limits(max_cases=1), root)
                self.assertTrue(warm.reused)
                self.assertEqual((run.call_count, warm.report), (1, short.report))
            self.assertEqual(pipe.replay_artifact(short.artifact), short.report)
            req = short.report["request"]
            with self.assertRaisesRegex(ValueError, "cached signed contact stream"):
                pipe.publish(root / "swapped", {**full.report, "request": req}, req)
            self.assertFalse((root / "swapped").exists())

    def test_rehashed_temporal_counter_forgery_and_unsupported_promotion_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result, = pipe.run_batch([sample()], cache_dir=root)
            pristine = result.artifact.read_bytes()
            req = result.report["request"]
            attempts = [(("scope", "comparisons", 0, "predicted_counts"), [0, 1, 0, 0]),
                        (("scope", "comparisons", 1, "scope"), "step"),
                        (("scope", "inputs_consumed"), 1), (("scope", "model_phase_after_consumed_inputs"), 2),
                        (("checks", 0, "witness", "actual"), "0"), (("status",), "unsupported"),
                        (("empirical_status",), "measured"), (("scope", "scientific_status"), "confirmed")]
            for keys, value in attempts:
                envelope = json.loads(pristine)
                obj = envelope["report"]
                for key in keys[:-1]:
                    obj = obj[key]
                obj[keys[-1]] = value
                envelope["report_sha256"] = pipe.digest(envelope["report"])
                data = canonical_json(envelope).encode()
                result.artifact.write_bytes(data)
                for call in (lambda: pipe.read_entry(result.artifact, req),
                             lambda: pipe.replay_artifact(result.artifact),
                             lambda: pipe.run_batch([sample()], cache_dir=root),
                             lambda report=envelope["report"]: pipe.publish(root / "never", report, req)):
                    with self.subTest(keys=keys), self.assertRaisesRegex(ValueError, "cached signed contact stream"):
                        call()
                self.assertFalse((root / "never").exists())
                self.assertEqual(result.artifact.read_bytes(), data)

    def test_three_relevant_loaded_sources_pinned_on_live_and_offline_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result, = pipe.run_batch([sample()], cache_dir=root)
            req = result.report["request"]
            c = pipe.parse_hypothesis(sample())
            original_read = Path.read_bytes
            for name in ("signed_contact_stream", "primitive_screen", "candidate_pipeline"):
                rel = f"theory_experiments/{name}.py"
                path = pipe.ROOT / rel
                actual = original_read(path)
                self.assertEqual(req["provenance"]["source_sha256"][rel], hashlib.sha256(actual).hexdigest())
                forged = copy.deepcopy(req)
                forged["provenance"]["source_sha256"][rel] = "0"*64
                with self.assertRaisesRegex(ValueError, "stream source changed"):
                    pipe.read_entry(result.artifact, forged)

                def newer(p, path=path, actual=actual):
                    return actual+b"\n" if p == path else original_read(p)
                with patch.object(Path, "read_bytes", newer):
                    for call in (lambda: pipe.run_batch([sample()], cache_dir=root / "missing"),
                                 lambda: pipe.compute(c, Limits(), req), lambda: pipe.read_entry(result.artifact, req),
                                 lambda: pipe.replay_artifact(result.artifact)):
                        with self.subTest(name=name), self.assertRaisesRegex(ValueError, "stream source changed"):
                            call()
            self.assertFalse((root / "missing").exists())


if __name__ == "__main__":
    unittest.main()
