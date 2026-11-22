"""Prepare–measure dispatch, narrow receipts, and normalized cache/replay."""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from itertools import product
from math import gcd
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.prepare_measure_cut import (
    MAX_SETTINGS,
    RANK_CHECK_ID,
    SCOPE,
    TRACE_CHECK_ID,
    PrepareMeasureCut,
)
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text

ADAPTER_PATH = "theory_experiments/prepare_measure_cut.py"
HELPER_PATH = "theory_experiments/primitive_screen.py"
FULL_PASS = "no_counterexample_within_bounds"


def identity(d):
    return [[int(i == j) for j in range(d)] for i in range(d)]


def specification(table=None, *, basis="unconditional", model="classical", dimension=2, seed=False):
    table = identity(3) if table is None else table
    return {"id": "table_cut", "family": "prepare_measure_cut", "event": "ref",
            "event_basis": basis,
            "memory": {"model": model, "dimension": dimension, "shared_classical_seed": seed},
            "intervals": [[[str(x) for x in v] if isinstance(v, tuple) else [str(v), str(v)]
                           for v in row] for row in table]}


def periodic_control():
    return {"id": "periodic", "family": "periodic_contact_observer", "current": [1, -1],
            "signal": {"initial": 0, "transitions": [[1, 0], [0, 1]]},
            "clock": {"initial": 0, "transitions": [[0, True]]}}


def long_denominator_table():
    n, total, q = MAX_SETTINGS, 1, 10**12-1
    table = []
    for i in range(n):
        row = []
        for j in range(n):
            if i == j:
                row.append("1")
            else:
                while gcd(total, q) != 1:
                    q -= 1
                total *= q
                row.append(f"1/{q}")
                q -= 1
        table.append(row)
    return table


class PrepareMeasureCutPipelineTests(unittest.TestCase):
    def test_point_joint_and_postselected_modes_stay_distinct(self):
        samples = [specification(), specification(basis="accepted_only"),
                   specification(basis="joint_accepted_event"), specification(dimension=3)]
        results = pipeline.run_batch(samples)
        self.assertEqual([r.report["status"] for r in results],
                         ["counterexample", "unsupported", "counterexample", "inconclusive"])
        self.assertEqual([pipeline.exit_code((r,)) for r in results], [1, 3, 1, 3])
        for source, result in zip(samples, results, strict=True):
            self.assertEqual(pipeline.parse_hypothesis(source).specification(), source)
            self.assertEqual(result.report["request"]["candidate"], source)
            self.assertEqual(result.report["rejection_scope"], SCOPE)
            self.assertEqual(result.report["evidence_kind"], "necessary_conditions_on_submitted_finite_table_only")
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            self.assertTrue(result.report["scope"]["necessary_conditions_only"])
            self.assertEqual([c["id"] for c in result.report["checks"]], [RANK_CHECK_ID, TRACE_CHECK_ID])

    def test_shared_memory_is_a_distinct_explicit_receipt_not_an_excuse_to_reuse_rank(self):
        seeds = list(product((0, 1), repeat=5))
        table = [[str(sum(bits[i] == bits[j] for bits in seeds)) + "/" + str(len(seeds))
                  for j in range(5)] for i in range(5)]
        for model in ("classical", "quantum"):
            specs = [specification(table, model=model), specification(table, model=model, seed=True)]
            with self.subTest(model=model), tempfile.TemporaryDirectory() as temporary:
                cache = Path(temporary)
                originals = pipeline.run_batch(specs, cache_dir=cache)
                self.assertNotEqual(originals[0].key, originals[1].key)
                self.assertEqual([r.report["status"] for r in originals], ["counterexample", "inconclusive"])
                self.assertEqual(originals[1].report["checks"][0]["status"], "unsupported")
                self.assertEqual(originals[1].report["checks"][1]["status"], "inconclusive")
                with patch.object(pipeline, "compute", side_effect=AssertionError("warm cache recomputed")):
                    hits = pipeline.run_batch(specs, cache_dir=cache)
                self.assertTrue(all(r.reused for r in hits))
                self.assertEqual(hits[1].report, originals[1].report)
                self.assertEqual(pipeline.exit_code((hits[1],)), 3)

    def test_exact_class_candidate_and_budget_receipt_binding_both_ways(self):
        class OtherLimits(Limits):
            pass

        class OtherCut(PrepareMeasureCut):
            pass

        cut = pipeline.parse_hypothesis(specification())
        cut_subclass = OtherCut(cut.id, cut.event, cut.event_basis, cut.memory_model,
                                cut.dimension, cut.shared_classical_seed, cut.intervals)
        changed = pipeline.parse_hypothesis(specification(basis="accepted_only"))
        periodic = pipeline.parse_hypothesis(periodic_control())
        legacy = pipeline.controls()["qm_born"]
        sources = pipeline.provenance()
        bounds = Limits(max_cases=2)
        correct = pipeline.request_for(cut, bounds, sources)
        pairs = [(cut, changed), (changed, cut), (cut, legacy), (legacy, cut),
                 (cut, periodic), (periodic, cut), (cut_subclass, cut)]
        with patch.object(pipeline, "evaluate_prepare_measure_cut", side_effect=AssertionError("bad receipt evaluated")):
            for candidate, reference in pairs:
                request = pipeline.request_for(reference, bounds, sources)
                with self.assertRaisesRegex(ValueError, "prepare-measure cut candidate/limits do not match request"):
                    pipeline.compute(candidate, bounds, request)
            for budget in (Limits(max_cases=1), OtherLimits(max_cases=2)):
                with self.assertRaisesRegex(ValueError, "prepare-measure cut candidate/limits do not match request"):
                    pipeline.compute(cut, budget, correct)
            forged = copy.deepcopy(correct)
            forged["limits"]["max_copies"] = True
            with self.assertRaisesRegex(ValueError, "prepare-measure cut candidate/limits do not match request"):
                pipeline.compute(cut, bounds, forged)
        self.assertEqual(pipeline.compute(cut, bounds, correct),
                         pipeline.run_batch([specification()], bounds)[0].report)

    def test_replay_and_cache_never_upgrade_a_truncated_necessary_test(self):
        broad = [[1 if i == j else ("0", "1") for j in range(3)] for i in range(3)]
        samples = [specification(broad), specification(), specification(basis="accepted_only"), periodic_control()]
        bounds = Limits(max_cases=1)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            first = pipeline.run_batch(samples, bounds, cache)
            self.assertEqual([r.report["status"] for r in first],
                             ["inconclusive", "counterexample", "unsupported", FULL_PASS])
            self.assertEqual(first[0].report["scope"]["stop_reason"], "max_cases")
            self.assertEqual([row["checked"] for row in first[0].report["checks"]], [1, 0])
            before = {item.artifact: item.artifact.read_bytes() for item in first}
            with patch.object(pipeline, "compute", side_effect=AssertionError("warm cache recomputed")):
                hits = pipeline.run_batch(samples, bounds, cache)
            self.assertEqual([r.report for r in hits], [r.report for r in first])
            self.assertTrue(all(r.reused for r in hits))
            self.assertEqual(pipeline.exit_code((hits[0],)), 3)
            for result in hits:
                self.assertEqual(pipeline.replay_artifact(result.artifact), result.report)
            fresh = pipeline.run_batch(samples, bounds, cache, fresh=True)
            self.assertTrue(all(not r.reused for r in fresh))
            self.assertEqual([r.report for r in fresh], [r.report for r in first])
            self.assertEqual(before, {item.artifact: item.artifact.read_bytes() for item in first})
            for a, b in ((first[0], first[1]), (first[1], first[0]), (first[0], first[3]), (first[3], first[0])):
                with self.assertRaisesRegex(ValueError, "cache integrity/request mismatch"):
                    pipeline.read_entry(a.artifact, b.report["request"])

    def test_corrupt_and_impossibly_strong_rehashed_cache_is_refused_without_overwrite(self):
        raw = specification(dimension=3)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            baseline, = pipeline.run_batch([raw], cache_dir=cache)
            pristine = baseline.artifact.read_bytes()
            for fault, reason in (
                ("digest", "cache integrity/request mismatch"),
                ("aggregate", "status/scope"),
                ("check", "invalid checks"),
                ("nested_status", "status/scope"),
                ("event_basis", "status/scope"),
            ):
                with self.subTest(fault=fault):
                    envelope = json.loads(pristine)
                    row = envelope["report"]
                    if fault in ("digest", "aggregate"):
                        row["status"] = FULL_PASS
                    elif fault == "check":
                        row["checks"][0]["status"] = FULL_PASS
                    elif fault == "nested_status":
                        row["scope"]["scientific_status"] = "confirmed"
                    else:
                        row["scope"]["event_basis"] = "accepted_only"
                    if fault != "digest":
                        envelope["report_sha256"] = pipeline.digest(row)
                    changed = canonical_json(envelope).encode()
                    baseline.artifact.write_bytes(changed)
                    with self.assertRaisesRegex(ValueError, reason):
                        pipeline.run_batch([raw], cache_dir=cache)
                    with self.assertRaisesRegex(ValueError, reason):
                        pipeline.replay_artifact(baseline.artifact)
                    self.assertEqual(baseline.artifact.read_bytes(), changed)

            envelope = json.loads(pristine)
            envelope["report"]["scope"]["stop_reason"] = "not_the_replayed_reason"
            envelope["report_sha256"] = pipeline.digest(envelope["report"])
            baseline.artifact.write_text(canonical_json(envelope), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "replay mismatch"):
                pipeline.replay_artifact(baseline.artifact)

    def test_source_pins_on_batch_direct_read_and_replay(self):
        raw = specification()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache, missing = root / "cached", root / "missing"
            result, = pipeline.run_batch([raw], cache_dir=cache)
            request = result.report["request"]
            model = pipeline.parse_hypothesis(raw)
            read = Path.read_bytes
            pristine = read(result.artifact)
            for relative in (ADAPTER_PATH, HELPER_PATH):
                with self.subTest(relative=relative):
                    target = pipeline.ROOT / relative
                    actual = read(target)
                    self.assertEqual(request["provenance"]["source_sha256"][relative],
                                     hashlib.sha256(actual).hexdigest())
                    forged = copy.deepcopy(request)
                    forged["provenance"]["source_sha256"][relative] = "0" * 64
                    for action in (lambda r=forged: pipeline.compute(model, Limits(), r),
                                   lambda r=forged: pipeline.read_entry(result.artifact, r)):
                        with self.assertRaisesRegex(ValueError, "prepare-measure cut source changed since import"):
                            action()

                    def changed(path, target=target, actual=actual):
                        return actual + b"\n# simulated newer checkout\n" if path == target else read(path)

                    with patch.object(Path, "read_bytes", changed):
                        newer_snapshot = pipeline.provenance()["source_sha256"]
                        # Even a matching newer pipeline snapshot cannot attest
                        # that a previously loaded checker/helper is up to date.
                        with patch.object(pipeline, "LOADED_SOURCE_HASHES", newer_snapshot):
                            for action in (lambda: pipeline.run_batch([raw], cache_dir=missing),
                                           lambda: pipeline.run_batch([raw], cache_dir=cache),
                                           lambda: pipeline.run_batch([raw], cache_dir=cache, fresh=True),
                                           lambda: pipeline.compute(model, Limits(), request),
                                           lambda: pipeline.read_entry(result.artifact, request),
                                           lambda: pipeline.replay_artifact(result.artifact)):
                                with self.assertRaisesRegex(ValueError, "prepare-measure cut source changed since import"):
                                    action()
            self.assertFalse(missing.exists())
            self.assertEqual(read(result.artifact), pristine)

    def test_max_square_long_denominators_fit_regular_cache_envelope(self):
        raw = specification(long_denominator_table(), dimension=MAX_SETTINGS-1)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            result, = pipeline.run_batch([raw], cache_dir=cache)
            self.assertEqual(result.report["status"], "counterexample")
            self.assertEqual([c["status"] for c in result.report["checks"]], ["counterexample"] * 2)
            witness = result.report["checks"][0]["witness"]["inputs"]
            self.assertIn("0x", witness["determinant_in_listed_order"])
            self.assertLess(result.artifact.stat().st_size, 128 * 1024)
            once, = pipeline.run_batch([raw], cache_dir=cache)
            self.assertTrue(once.reused)
            self.assertEqual(pipeline.replay_artifact(result.artifact), result.report)

    def test_retained_source_is_not_automatically_joined_to_the_obstruction(self):
        body = "-- prepare_measure_cut in source is not a submitted table\n"
        source = {"id": "cut_source", "family": "source_theory", "role": "primitive_base",
                  "components": ["prepare_measure_cut"], "declared_status": "unassessed",
                  "missing_bridges": ["a reviewed prediction adapter"],
                  "sources": [SourceSnapshot("Proofs/Cut.lean", 1, 1, sha256_text(body), body).specification()]}
        with patch.object(pipeline, "evaluate_prepare_measure_cut", side_effect=AssertionError("implicit join")):
            result, = pipeline.run_batch([source])
        self.assertEqual(result.report["status"], "unsupported")
        self.assertEqual(result.report["scope"]["adapter_status"], "missing")


if __name__ == "__main__":
    unittest.main()
