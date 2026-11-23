"""Pinned finite network receipts: modulus, visible nulls and contact order cannot drift."""

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tests.test_ternary_network_nulls import G, H, raw
from theory_experiments import candidate_pipeline as pipe
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text
from theory_experiments.ternary_network_nulls import (
    CHECK_ID,
    SCOPE,
    TernaryNetworkNulls,
)


def sample(rule="residue_field", p=5):
    return raw(rule, (0, 0, 1, 0), (H[::-1], G[::-1]), [(2, 2, True), (1, 0, False)], p)


class NullPipelineTests(unittest.TestCase):
    def test_same_input_darkness_depends_on_declared_channel_only(self):
        text = "-- a description is not an executable sequence of observations\n"
        retained = {"id": "not_a_run", "family": "source_theory", "role": "primitive_base",
                    "components": ["ternary_network_nulls"], "declared_status": "unassessed",
                    "missing_bridges": ["an independent port null observation"],
                    "sources": [SourceSnapshot("Proofs/Example.lean", 1, 1, sha256_text(text), text).specification()]}
        mod5, rational, mod7, no_run = pipe.run_batch([sample(), sample("mobile_depth", None), sample(p=7), retained])
        self.assertEqual([r.report["status"] for r in (mod5, rational, mod7, no_run)],
                         ["no_counterexample_within_bounds", "counterexample", "counterexample", "unsupported"])
        self.assertEqual(no_run.report["scope"]["adapter_status"], "missing")
        for r in (mod5, rational, mod7):
            ck, = r.report["checks"]
            self.assertEqual((ck["id"], r.report["rejection_scope"], r.report["proof_status"],
                              r.report["empirical_status"]), (CHECK_ID, SCOPE, "not_attempted", "not_tested"))
            for row in r.report["scope"]["comparisons"]:
                self.assertEqual(set(row), {"after", "port", "submitted_dark", "predicted_dark"})
                self.assertIs(type(row["predicted_dark"]), bool)

    def test_bind_order_modulus_readouts_and_limits_before_evaluating(self):
        spec = sample()
        c = pipe.parse_hypothesis(spec)
        norm = c.specification()
        different = [{**norm, "contacts": list(reversed(norm["contacts"]))}, {**norm, "modulus": 7},
                     {**norm, "rule": "mobile_depth", "modulus": None}, {**norm, "initial": [0, 1, 0, 0]},
                     {**norm, "readouts": [{**norm["readouts"][0], "dark": True}, norm["readouts"][1]]}]
        results = pipe.run_batch([spec, norm, *different])
        self.assertEqual(results[0].key, results[1].key)
        self.assertTrue(results[1].reused)
        self.assertEqual(len({r.key for r in results}), len(results)-1)
        req = results[0].report["request"]

        class Child(TernaryNetworkNulls):
            pass

        class OtherLimits(Limits):
            pass

        other = pipe.parse_hypothesis({"id": "other", "family": "ternary_encounter", "rule": "idle",
                                      "marked_ports": [3, 4], "observations": [{"packets": [0, 0, 0], "vertex": 0, "count": 3}]})
        with patch.object(pipe, "evaluate_ternary_network_nulls", side_effect=AssertionError("unbound call")):
            for actual, limits, request in (
                (c, Limits(), {**req, "candidate": spec}), (Child(**vars(c)), Limits(), req),
                (c, Limits(max_cases=1), req), (c, OtherLimits(), req), (other, Limits(), req),
                (c, Limits(), pipe.request_for(other, Limits(), req["provenance"])),
                (c, Limits(), {**req, "schema": "unbound"}),
                (c, Limits(), {**req, "limits": {**req["limits"], "coefficient_radius": True}}),
                *((c, Limits(), {**req, "candidate": v}) for v in different),
            ):
                with self.assertRaisesRegex(ValueError, "ternary network nulls candidate/limits"):
                    pipe.compute(actual, limits, request)
            with self.assertRaisesRegex(ValueError, "candidate/limits"):
                pipe.run_batch([spec], OtherLimits())

    def test_partial_receipt_never_certifies_an_unobserved_suffix(self):
        spec = raw("stationary_bucket", (1, 0, 0, 0), (H, G), [(1, 1, False)])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            short, = pipe.run_batch([spec], Limits(max_cases=1), root)
            full, = pipe.run_batch([spec], Limits(max_cases=2), root)
            self.assertNotEqual(short.key, full.key)
            ck, = short.report["checks"]
            self.assertEqual((short.report["status"], short.report["scope"]["contacts_consumed"], ck["checked"],
                              ck["planned"], ck["witness"]), ("inconclusive", 1, 1, 1, None))
            self.assertEqual((full.report["status"], full.report["scope"]["contacts_consumed"]), ("counterexample", 2))
            with patch.object(pipe, "evaluate_ternary_network_nulls", wraps=pipe.evaluate_ternary_network_nulls) as run:
                warm, = pipe.run_batch([spec], Limits(max_cases=1), root)
                self.assertEqual((run.call_count, warm.reused, warm.report), (1, True, short.report))
            self.assertEqual(pipe.replay_artifact(short.artifact), short.report)
            req = short.report["request"]
            with self.assertRaisesRegex(ValueError, "cached ternary network nulls"):
                pipe.publish(root / "swapped", {**full.report, "request": req}, req)
            self.assertFalse((root / "swapped").exists())

    def test_rehashed_false_flags_leaked_values_and_scope_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result, = pipe.run_batch([sample("mobile_depth", None)], cache_dir=root)
            pristine = result.artifact.read_bytes()
            req = result.report["request"]
            for keys, val in [
                (("scope", "comparisons", 1, "predicted_dark"), True), (("scope", "comparisons", 0, "predicted_dark"), 0),
                (("scope", "comparisons", 1, "numerator"), 5), (("scope", "private_stocks"), [2]),
                (("scope", "modulus"), 5), (("scope", "contacts_consumed"), 1), (("status",), "no_counterexample_within_bounds"),
                (("empirical_status",), "measured"), (("checks", 0, "witness", "actual"), "0"),
            ]:
                envelope = json.loads(pristine)
                obj = envelope["report"]
                for key in keys[:-1]:
                    obj = obj[key]
                obj[keys[-1]] = val
                envelope["report_sha256"] = pipe.digest(envelope["report"])
                encoded = canonical_json(envelope).encode()
                result.artifact.write_bytes(encoded)
                for action in (lambda: pipe.read_entry(result.artifact, req),
                               lambda: pipe.replay_artifact(result.artifact),
                               lambda: pipe.run_batch([req["candidate"]], cache_dir=root),
                               lambda report=envelope["report"]: pipe.publish(root / "never", report, req)):
                    with self.subTest(keys=keys), self.assertRaisesRegex(ValueError, "cached ternary network nulls"):
                        action()
                self.assertEqual(result.artifact.read_bytes(), encoded)
                self.assertFalse((root / "never").exists())

    def test_sparse_nine_prefix_run_requires_the_86th_command(self):
        word = (H, G)*43
        # All nine readings are raw nulls for this input in the idle control.
        spec = raw("idle_wire", (0, 0, 1, 0), word,
                   [(k, 1, True) for k in (2, 6, 10, 14, 22, 34, 46, 70, 86)])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for budget, verdict, reads in ((85, "inconclusive", 8), (86, "no_counterexample_within_bounds", 9)):
                result, = pipe.run_batch([spec], Limits(max_cases=budget), root)
                self.assertEqual((result.report["status"], result.report["scope"]["contacts_consumed"],
                                  result.report["checks"][0]["checked"]), (verdict, budget, reads))
                self.assertEqual(pipe.replay_artifact(result.artifact), result.report)

    def test_live_and_offline_checks_bind_checker_dependencies(self):
        spec = sample()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result, = pipe.run_batch([spec], cache_dir=root)
            req = result.report["request"]
            c = pipe.parse_hypothesis(spec)
            original_read = Path.read_bytes
            for name in ("ternary_network_nulls", "primitive_screen", "candidate_pipeline"):
                rel = f"theory_experiments/{name}.py"
                path = pipe.ROOT / rel
                actual = original_read(path)
                self.assertEqual(req["provenance"]["source_sha256"][rel], hashlib.sha256(actual).hexdigest())
                forged = copy.deepcopy(req)
                forged["provenance"]["source_sha256"][rel] = "0"*64
                with self.assertRaisesRegex(ValueError, "ternary network nulls source changed"):
                    pipe.read_entry(result.artifact, forged)

                def changed(p, path=path, actual=actual):
                    return actual+b"\n" if p == path else original_read(p)
                with patch.object(Path, "read_bytes", changed):
                    for action in (lambda: pipe.run_batch([spec], cache_dir=root / "missing"),
                                   lambda: pipe.compute(c, Limits(), req), lambda: pipe.read_entry(result.artifact, req),
                                   lambda: pipe.replay_artifact(result.artifact)):
                        with self.subTest(path=name), self.assertRaisesRegex(ValueError, "ternary network nulls source changed"):
                            action()
            self.assertFalse((root / "missing").exists())


if __name__ == "__main__":
    unittest.main()
