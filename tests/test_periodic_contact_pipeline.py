"""Explicit finite-model dispatch, receipt binding, and shared cache boundaries."""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import primitive_screen as primitive
from theory_experiments.candidate_history import History
from theory_experiments.periodic_contact_observer import CHECK_ID, MAX_STATES, SCOPE
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text

ADAPTER_PATH = "theory_experiments/periodic_contact_observer.py"
HELPERS_PATH = "theory_experiments/primitive_screen.py"
PASS = "no_counterexample_within_bounds"


def ring(outputs):
    return [[(i+1) % len(outputs), out] for i, out in enumerate(outputs)]


def specification(*, signal=(0, 2, 0, 2), clock=(True, True, False, False), current=(1, 0, -1)):
    return {"id": "finite_contact", "family": "periodic_contact_observer", "current": list(current),
            "signal": {"initial": 0, "transitions": ring(signal)},
            "clock": {"initial": 0, "transitions": ring(clock)}}


class PeriodicContactPipelineTests(unittest.TestCase):
    def test_explicit_dispatch_preserves_model_only_statuses(self):
        samples = [
            specification(),
            specification(clock=(True, False, True, False)),
            specification(clock=(False,)),
            specification(current=(0, 0, 0)),
        ]
        results = pipeline.run_batch(samples)
        self.assertEqual([result.report["status"] for result in results],
                         [PASS, "counterexample", "unsupported", "unsupported"])
        for sample, result in zip(samples, results, strict=True):
            self.assertEqual(pipeline.parse_hypothesis(sample).specification(), sample)
            self.assertEqual(result.card()["family"], "periodic_contact_observer")
            self.assertEqual(result.report["rejection_scope"], SCOPE)
            self.assertEqual(result.report["scope"]["scientific_status"], "unassessed")
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            self.assertEqual(result.report["checks"][0]["id"], CHECK_ID)
        partial, = pipeline.run_batch([samples[0]], Limits(max_cases=2))
        self.assertEqual(partial.report["status"], "inconclusive")
        self.assertFalse(partial.report["scope"]["all_recurrent_phase_rail_rates_certified"])
        self.assertEqual(pipeline.exit_code((partial,)), 3)
        self.assertEqual(pipeline.exit_code(results), 1)

    def test_retained_source_never_implicitly_binds_observer(self):
        text = "-- periodic_contact_observer remains a supplied finite model\n"
        retained = {
            "id": "retained_contact", "family": "source_theory", "role": "primitive_base",
            "components": ["periodic_contact_observer"], "declared_status": "unassessed",
            "missing_bridges": ["reviewed physical prediction map"],
            "sources": [SourceSnapshot("Proofs/Contact.lean", 1, 1, sha256_text(text), text).specification()]
        }
        with patch.object(pipeline, "evaluate_periodic_contact_observer",
                          side_effect=AssertionError("implicit binding")):
            result, = pipeline.run_batch([retained])
        self.assertEqual(result.report["status"], "unsupported")
        self.assertEqual(result.report["scope"]["adapter_status"], "missing")

    def test_typed_arguments_and_candidate_limits_bind_direct_receipts_both_ways(self):
        class UntrustedLimits(Limits):
            pass

        periodic = pipeline.parse_hypothesis(specification())
        different = pipeline.parse_hypothesis(specification(clock=(True, False, True, False)))
        driven = pipeline.parse_hypothesis({
            "id": "old_selector", "family": "driven_event_selector",
            "contexts": [{"current": [0, 1, -1], "fixed": 0}],
            "initial": 0, "transitions": [[[0, 1]]],
        })
        legacy = pipeline.controls()["qm_born"]
        limits, sources = Limits(max_cases=4), pipeline.provenance()
        correct = pipeline.request_for(periodic, limits, sources)
        bad_pairs = [
            (different, limits, periodic), (periodic, limits, different),
            (periodic, Limits(max_cases=1), periodic), (periodic, UntrustedLimits(max_cases=4), periodic),
            (periodic, limits, legacy), (legacy, limits, periodic),
            (periodic, limits, driven), (driven, limits, periodic),
        ]
        with patch.object(pipeline, "evaluate_periodic_contact_observer",
                          side_effect=AssertionError("mismatched receipt evaluated")):
            for candidate, actual_limits, receipt_candidate in bad_pairs:
                with self.subTest(families=(candidate.specification()["family"],
                                            receipt_candidate.specification()["family"])):
                    request = pipeline.request_for(receipt_candidate, limits, sources)
                    with self.assertRaisesRegex(ValueError, "candidate/limits do not match request"):
                        pipeline.compute(candidate, actual_limits, request)
            bool_limit = copy.deepcopy(correct)
            bool_limit["limits"]["coefficient_radius"] = True
            with self.assertRaisesRegex(ValueError, "candidate/limits do not match request"):
                pipeline.compute(periodic, limits, bool_limit)
        self.assertEqual(pipeline.compute(periodic, limits, correct),
                         pipeline.run_batch([specification()], limits)[0].report)

    def test_small_mixed_warm_and_fresh_receipts_reject_crossed_disk_requests(self):
        inputs = [specification(), pipeline.controls()["qm_born"].specification()]
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            seed = pipeline.run_batch(inputs, cache_dir=cache, fresh=True)
            with patch.object(pipeline, "compute", side_effect=AssertionError("unexpected recomputation")):
                hits = pipeline.run_batch(inputs, cache_dir=cache)
            self.assertTrue(all(result.reused for result in hits))
            for previous, hit in zip(seed, hits, strict=True):
                self.assertEqual(previous.report, hit.report)
                self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            fresh = pipeline.run_batch(inputs, cache_dir=cache, fresh=True)
            self.assertTrue(all(not result.reused for result in fresh))
            for a, b in (seed, seed[::-1]):
                with self.assertRaisesRegex(ValueError, "cache integrity/request mismatch"):
                    pipeline.read_entry(a.artifact, b.report["request"])

    def test_pins_reject_stale_loaded_or_current_bytes_and_forged_receipt_hashes(self):
        sample = specification()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / "existing"
            result, = pipeline.run_batch([sample], cache_dir=cache)
            request = result.report["request"]
            candidate = pipeline.parse_hypothesis(sample)
            old_artifact = result.artifact.read_bytes()
            read_bytes = Path.read_bytes
            for relative in (ADAPTER_PATH, HELPERS_PATH):
                with self.subTest(relative=relative):
                    source = pipeline.ROOT / relative
                    original = read_bytes(source)
                    expected = hashlib.sha256(original).hexdigest()
                    self.assertEqual(request["provenance"]["source_sha256"][relative], expected)
                    forged = copy.deepcopy(request)
                    forged["provenance"]["source_sha256"][relative] = "0" * 64
                    for action in (lambda r=forged: pipeline.compute(candidate, Limits(), r),
                                   lambda r=forged: pipeline.read_entry(result.artifact, r)):
                        with self.assertRaisesRegex(ValueError, "periodic contact observer source changed since import"):
                            action()

                    def changed_disk(path, source=source, original=original):
                        return original + b"\n# simulated on-disk change\n" if path == source else read_bytes(path)

                    with patch.object(Path, "read_bytes", changed_disk):
                        new_snapshot = pipeline.provenance()["source_sha256"]
                        # Simulate preloading the helper before the central pipeline
                        # captured a newer, internally consistent disk snapshot.
                        with patch.object(pipeline, "LOADED_SOURCE_HASHES", new_snapshot):
                            actions = (
                                lambda: pipeline.run_batch([sample], cache_dir=root / "absent"),
                                lambda: pipeline.run_batch([sample], cache_dir=cache),
                                lambda: pipeline.run_batch([sample], cache_dir=cache, fresh=True),
                                lambda: pipeline.compute(candidate, Limits(), request),
                                lambda: pipeline.read_entry(result.artifact, request),
                                lambda: pipeline.replay_artifact(result.artifact),
                            )
                            for action in actions:
                                with self.assertRaisesRegex(
                                        ValueError, "periodic contact observer source changed since import"):
                                    action()
            self.assertFalse((root / "absent").exists())
            self.assertEqual(result.artifact.read_bytes(), old_artifact)

    def test_large_valid_cache_round_trip_does_not_expand_public_input_limits(self):
        n = MAX_STATES
        sample = specification(signal=list(range(8)) * (n//8),
                               clock=[True]*(n//2) + [False]*(n//2), current=(1, -1)*4)
        limits = Limits(max_cases=5000)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / "cache"
            seed, = pipeline.run_batch([sample], limits=limits, cache_dir=cache)
            before = seed.artifact.read_bytes()
            self.assertGreater(len(before), 128 * 1024)
            self.assertLess(len(before), 512 * 1024)
            self.assertEqual(seed.report["status"], "inconclusive")
            self.assertEqual(seed.report["checks"][0]["checked"], 5000)
            with patch.object(pipeline, "compute", side_effect=AssertionError("warm cache recomputed")):
                hit, = pipeline.run_batch([sample], limits=limits, cache_dir=cache)
            self.assertTrue(hit.reused)
            self.assertEqual(hit.report, seed.report)
            with patch.object(pipeline, "compute", wraps=pipeline.compute) as compute:
                self.assertEqual(pipeline.replay_artifact(seed.artifact), seed.report)
                self.assertEqual(compute.call_count, 1)
            self.assertEqual(seed.artifact.read_bytes(), before)
            batch_path = root / "input.json"
            batch_path.write_text(canonical_json([sample]), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "input exceeds 128 KiB"):
                primitive.load_json(batch_path)
            with self.assertRaisesRegex(ValueError, "candidate submission exceeds 128 KiB"):
                History(root / "history").submit([sample], limits)

    def test_shared_reader_rejects_corruption_nonexact_json_size_and_symlinks(self):
        sample = specification()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            seed, = pipeline.run_batch([sample], cache_dir=root)
            request = seed.report["request"]
            pristine = seed.artifact.read_bytes()
            forged = json.loads(pristine)
            forged["report"]["status"] = "counterexample"
            cases = (
                (b"{", "Expecting"),
                (b'{"schema":1,"schema":2}', "duplicate JSON key"),
                (b'{"schema":1.0}', "non-integer JSON"),
                (b'{"schema":NaN}', "non-integer JSON"),
                (b" " * (512 * 1024 + 1), "512 KiB"),
                (canonical_json(forged).encode("utf-8"), "cache integrity/request mismatch"),
            )
            for content, message in cases:
                with self.subTest(message=message):
                    seed.artifact.write_bytes(content)
                    with self.assertRaisesRegex(ValueError, message):
                        pipeline.run_batch([sample], cache_dir=root)
                    with self.assertRaisesRegex(ValueError, message):
                        pipeline.replay_artifact(seed.artifact)
                    self.assertEqual(seed.artifact.read_bytes(), content)
            # Even a digest-consistent, allegedly trusted envelope is
            # recomputed on replay, which exposes the changed verdict.
            forged["report_sha256"] = pipeline.digest(forged["report"])
            seed.artifact.write_text(canonical_json(forged), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "replay mismatch"):
                pipeline.replay_artifact(seed.artifact)

            original = root / "regular.json"
            original.write_bytes(pristine)
            seed.artifact.unlink()
            seed.artifact.symlink_to(original)
            for path in (seed.artifact, root):
                with self.subTest(path=path):
                    with self.assertRaises((ValueError, OSError)):
                        pipeline.read_entry(path, request)
                    with self.assertRaises((ValueError, OSError)):
                        pipeline.replay_artifact(path)
            self.assertEqual(original.read_bytes(), pristine)

    def test_oversized_output_refused_before_even_creating_publication_tempfile(self):
        sample = specification()
        seed, = pipeline.run_batch([sample])
        oversized = copy.deepcopy(seed.report)
        oversized["scope"]["padding"] = "x" * (512 * 1024)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            with (patch.object(pipeline, "compute", return_value=oversized),
                  self.assertRaisesRegex(ValueError, "512 KiB")):
                pipeline.run_batch([sample], cache_dir=cache)
            self.assertEqual(list(cache.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
