"""Explicit submitted-transducer dispatch, narrow claims, and source-safe cache use."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.primitive_screen import Limits, canonical_json
from theory_experiments.source_candidate import SourceSnapshot, sha256_text

MODEL_PATH = "theory_experiments/driven_event_selector.py"
PASS = "no_counterexample_within_bounds"
FAIL = "counterexample"
SCOPE = "only_submitted_finite_transducer_and_calibrated_reference"


def specification(**changes: object) -> dict[str, object]:
    result: dict[str, object] = {
        "id": "submitted_always_minus", "family": "driven_event_selector",
        "contexts": [{"current": [0, 1, -1], "fixed": 0}],
        "initial": 0, "transitions": [[[0, 1]]],
    }
    result.update(changes)
    return result


class DrivenEventSelectorPipelineTests(unittest.TestCase):
    def test_explicit_dispatch_and_narrow_report(self) -> None:
        specs = [specification(), specification(id="wrong_bit", transitions=[[[0, 0]]])]
        results = pipeline.run_batch(specs, fresh=True)
        self.assertEqual([r.report["status"] for r in results], [PASS, FAIL])
        for spec, result in zip(specs, results, strict=True):
            self.assertEqual(pipeline.parse_hypothesis(spec).specification(), spec)
            self.assertEqual(result.card()["family"], "driven_event_selector")
            self.assertEqual(result.report["rejection_scope"], SCOPE)
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            self.assertEqual(result.report["evidence_kind"],
                             "computation_with_explicit_algebraic_or_bounded_scope")
            self.assertEqual(result.report["checks"][0]["id"],
                             "driven_event_selector_context_rates")
            self.assertFalse(result.reused)
            self.assertIsNone(result.artifact)
        self.assertTrue(results[0].report["scope"]["all_eventually_periodic_context_rates_certified"])
        self.assertFalse(results[1].report["scope"]["all_eventually_periodic_context_rates_certified"])
        self.assertEqual(pipeline.exit_code(results), 1)

    def test_zero_current_is_unsupported_without_rejecting_the_primitive(self) -> None:
        result, = pipeline.run_batch([specification(contexts=[{"current": [0, 0, 0], "fixed": 0}])])
        self.assertEqual(result.report["status"], "unsupported")
        self.assertEqual(result.report["rejection_scope"], SCOPE)
        self.assertIsNone(result.report["checks"][0]["witness"])
        self.assertFalse(result.report["scope"]["all_eventually_periodic_context_rates_certified"])
        self.assertEqual(pipeline.exit_code((result,)), 3)

    def test_truncated_budget_is_inconclusive_not_a_certificate_or_rejection(self) -> None:
        spec = specification(contexts=[{"current": [1, 0, -1], "fixed": 0}],
                             transitions=[[[1, 1]], [[2, 0]], [[3, 0]], [[0, 0]]])
        short, = pipeline.run_batch([spec], Limits(max_cases=1))
        full, = pipeline.run_batch([spec], Limits(max_cases=4))
        self.assertEqual(short.report["status"], "inconclusive")
        self.assertEqual(short.report["checks"][0]["checked"], 1)
        self.assertIsNone(short.report["checks"][0]["witness"])
        self.assertFalse(short.report["scope"]["all_eventually_periodic_context_rates_certified"])
        self.assertEqual(full.report["status"], PASS)
        self.assertNotEqual(short.key, full.key)
        self.assertEqual(pipeline.exit_code((short,)), 3)

    def test_canonical_roundtrip_preserves_context_and_state_index_order(self) -> None:
        # Two separately submitted knobs may carry identical current labels.
        contexts = [{"current": [0, 1, -1], "fixed": 0}] * 2
        spec = specification(contexts=contexts, initial=1,
                             transitions=[[[1, 1], [0, 1]], [[0, 1], [1, 1]]])
        self.assertEqual(pipeline.parse_hypothesis(spec).specification(), spec)

    def test_bounded_input_validates_whole_batch_before_creating_cache(self) -> None:
        invalid = [
            {"extra": True}, {"initial": True}, {"initial": 1},
            {"contexts": []}, {"contexts": [{"current": [0, 1, -1], "fixed": 0}] * 9},
            {"contexts": [{"current": [0, True, -1], "fixed": 0}]},
            {"contexts": [{"current": [0, 1000001, -1000001], "fixed": 0}]},
            {"contexts": [{"current": [0, 1, 0], "fixed": 0}]},
            {"contexts": [{"current": [0, 1, -1], "fixed": 3}]},
            {"transitions": []}, {"transitions": [[[0, 1]]] * 129},
            {"transitions": [[[1, 1]]]}, {"transitions": [[[0, True]]]},
            {"transitions": [[[0, 2]]]}, {"transitions": [[[0, 1], [0, 1]]]},
        ]
        for changes in invalid:
            with self.subTest(changes=changes), tempfile.TemporaryDirectory() as temporary:
                cache = Path(temporary) / "absent"
                with self.assertRaises((ValueError, TypeError)):
                    pipeline.run_batch([specification(), specification(**changes)], cache_dir=cache)
                self.assertFalse(cache.exists())

    def test_retained_source_never_implicitly_binds_new_adapter(self) -> None:
        text = "-- driven_event_selector is a proposal, not executable binding\n"
        spec = {"id": "retained_selector", "family": "source_theory", "role": "primitive_base",
                "components": ["driven_event_selector"], "declared_status": "unassessed",
                "missing_bridges": ["reviewed physical prediction map"],
                "sources": [SourceSnapshot("Proofs/Selector.lean", 1, 1, sha256_text(text), text).specification()]}
        with patch.object(pipeline, "evaluate_driven_event_selector", side_effect=AssertionError("implicit binding")):
            result, = pipeline.run_batch([spec])
        self.assertEqual(result.report["status"], "unsupported")
        self.assertEqual(result.report["scope"]["adapter_status"], "missing")
        self.assertEqual(result.report["checks"][0]["id"], "primitive_prediction_adapter")

    def test_mixed_cache_fresh_replay_and_source_pin(self) -> None:
        specs = [specification(), specification(id="wrong_bit", transitions=[[[0, 0]]]),
                 specification(id="zero", contexts=[{"current": [0, 0, 0], "fixed": 0}])]
        expected = hashlib.sha256((pipeline.ROOT / MODEL_PATH).read_bytes()).hexdigest()
        self.assertIn(MODEL_PATH, pipeline.SOURCE_PATHS)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            first = pipeline.run_batch(specs, cache_dir=cache, fresh=True)
            before = {path: path.read_bytes() for path in cache.iterdir()}
            with patch.object(pipeline, "compute", side_effect=AssertionError("warm cache recomputed")):
                hits = pipeline.run_batch(specs, cache_dir=cache)
            for original, hit in zip(first, hits, strict=True):
                self.assertTrue(hit.reused)
                self.assertEqual(original.key, hit.key)
                self.assertEqual(original.report, hit.report)
                self.assertEqual(hit.report["request"]["provenance"]["source_sha256"][MODEL_PATH], expected)
                self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            fresh = pipeline.run_batch(specs, cache_dir=cache, fresh=True)
            self.assertTrue(all(not result.reused for result in fresh))
            duplicate = pipeline.run_batch([specs[0], specs[0]], fresh=True)
            self.assertEqual([r.reused for r in duplicate], [False, True])
            self.assertEqual(before, {path: path.read_bytes() for path in cache.iterdir()})

    def test_mutated_cache_report_or_request_is_refused_without_overwrite(self) -> None:
        for target in ("report", "request"):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as temporary:
                cache = Path(temporary)
                result, = pipeline.run_batch([specification()], cache_dir=cache)
                envelope = json.loads(result.artifact.read_text())
                if target == "report":
                    envelope["report"]["status"] = FAIL
                else:
                    envelope["report"]["request"]["candidate"]["initial"] = 1
                    envelope["report_sha256"] = pipeline.digest(envelope["report"])
                result.artifact.write_text(canonical_json(envelope) + "\n")
                before = result.artifact.read_bytes()
                with self.assertRaisesRegex(ValueError, "cache integrity/request mismatch"):
                    pipeline.run_batch([specification()], cache_dir=cache)
                self.assertEqual(result.artifact.read_bytes(), before)

    def test_direct_compute_and_cache_read_refuse_changed_disk_and_supplied_pin(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            result, = pipeline.run_batch([specification()], cache_dir=Path(temporary))
            request = result.report["request"]
            model = pipeline.parse_hypothesis(request["candidate"])
            original_read = Path.read_bytes
            for relative in (MODEL_PATH, "theory_experiments/primitive_screen.py"):
                source = pipeline.ROOT / relative
                changed = original_read(source) + b"\n# simulated post-import edit\n"

                def disk_read(path: Path, changed=changed, source=source) -> bytes:
                    return changed if path == source else original_read(path)

                bad_request = copy.deepcopy(request)
                bad_request["provenance"]["source_sha256"][relative] = "0" * 64
                with self.subTest(relative=relative):
                    for thunk in (lambda r=bad_request: pipeline.compute(model, Limits(), r),
                                  lambda r=bad_request: pipeline.read_entry(result.artifact, r)):
                        with self.assertRaisesRegex(ValueError, "driven event selector source changed since import"):
                            thunk()
                    with patch.object(Path, "read_bytes", disk_read):
                        for thunk in (lambda: pipeline.compute(model, Limits(), request),
                                      lambda: pipeline.read_entry(result.artifact, request)):
                            with self.assertRaisesRegex(ValueError, "driven event selector source changed since import"):
                                thunk()

    def test_direct_compute_binds_candidate_and_limits_to_request(self) -> None:
        a = pipeline.parse_hypothesis(specification())
        b = pipeline.parse_hypothesis(specification(id="wrong_bit", transitions=[[[0, 0]]]))
        limits = Limits(max_cases=2)
        request = pipeline.request_for(a, limits, pipeline.provenance())
        with patch.object(pipeline, "evaluate_driven_event_selector",
                          side_effect=AssertionError("mismatched receipt evaluated")):
            for candidate, budget in ((b, limits), (a, Limits(max_cases=1))):
                with (self.subTest(candidate=candidate.id, budget=budget.max_cases),
                      self.assertRaisesRegex(ValueError, "candidate/limits do not match request")):
                    pipeline.compute(candidate, budget, request)
        valid = pipeline.compute(a, limits, request)
        self.assertEqual(valid["request"], request)
        self.assertEqual(valid["status"], PASS)
        self.assertEqual(valid, pipeline.run_batch([specification()], limits)[0].report)

    def test_direct_compute_rejects_driven_and_legacy_family_receipt_swaps(self) -> None:
        driven = pipeline.parse_hypothesis(specification())
        legacy = pipeline.controls()["qm_born"]
        limits = Limits()
        sources = pipeline.provenance()
        for candidate, receipt_candidate in ((driven, legacy), (legacy, driven)):
            with self.subTest(candidate=candidate.specification()["family"]):
                request = pipeline.request_for(receipt_candidate, limits, sources)
                with self.assertRaisesRegex(ValueError, "candidate/limits do not match request"):
                    pipeline.compute(candidate, limits, request)

    def test_historical_normalized_result_stays_unchanged_across_engine_runtime(self) -> None:
        from theory_experiments.candidate_history import (
            History,
            recheck_history,
            record_batch,
        )

        with tempfile.TemporaryDirectory() as temporary:
            history = History(Path(temporary))
            record_batch([specification()], history=history)
            changed = copy.deepcopy(pipeline.provenance())
            changed["runtime"]["version"] = "simulated successor runtime"
            with patch.object(pipeline, "provenance", return_value=changed):
                recheck = recheck_history(history)
            self.assertEqual(recheck["status"], "unchanged")


IMPORT_PROBE = r'''
import hashlib
import importlib
import sys
from pathlib import Path
from unittest.mock import patch

mode, scratch_name, module_name = sys.argv[1:]
scratch = Path(scratch_name)
relative = f'theory_experiments/{module_name}.py'
source = Path.cwd() / relative
original_read = Path.read_bytes
original = original_read(source)
changed = original + b'\n# simulated pre-pipeline checkout edit\n'

def need(condition, message):
    if not condition:
        raise AssertionError(message)

def disk_read(path):
    return changed if path == source else original_read(path)

def refused(thunk):
    try:
        thunk()
    except ValueError as error:
        need(f'driven event selector source changed since import: {relative}' in str(error), str(error))
    else:
        raise AssertionError('stale source returned a result')

if mode == 'stale':
    loaded = importlib.import_module(f'theory_experiments.{module_name}')
    need(loaded.LOADED_SOURCE_SHA256 == hashlib.sha256(original).hexdigest(), 'old source loaded')
    need('theory_experiments.candidate_pipeline' not in sys.modules, 'pipeline not yet loaded')

with patch.object(Path, 'read_bytes', disk_read):
    from theory_experiments import candidate_pipeline as pipeline
    from theory_experiments.primitive_screen import Limits
    spec = {'id':'stale_probe','family':'driven_event_selector',
            'contexts':[{'current':[0,1,-1],'fixed':0}],
            'initial':0,'transitions':[[[0,1]]]}
    limits = Limits()
    cache = scratch / 'cache'
    if mode == 'seed':
        result, = pipeline.run_batch([spec], limits, cache, fresh=True)
        hit, = pipeline.run_batch([spec], limits, cache)
        need(hit.reused and hit.report == result.report, 'seed cache works')
        need(pipeline.replay_artifact(result.artifact) == result.report, 'seed replay works')
    else:
        model = pipeline.parse_hypothesis(spec)
        request = pipeline.request_for(model, limits, pipeline.provenance())
        artifact = cache / (pipeline.digest(request) + '.json')
        need(artifact.is_file(), 'exact warm cache request exists')
        before = original_read(artifact)
        absent = scratch / 'absent'
        refused(lambda: pipeline.run_batch([spec], limits, absent))
        need(not absent.exists(), 'no cache created')
        refused(lambda: pipeline.run_batch([spec], limits, cache))
        refused(lambda: pipeline.run_batch([spec], limits, cache, fresh=True))
        refused(lambda: pipeline.compute(model, limits, request))
        refused(lambda: pipeline.read_entry(artifact, request))
        refused(lambda: pipeline.replay_artifact(artifact))
        need(original_read(artifact) == before, 'cache unchanged')
need(original_read(source) == original, 'repository source unchanged')
'''


class DrivenEventSelectorPreloadedSourceTests(unittest.TestCase):
    def test_adapter_and_shared_helper_preloaded_before_pipeline_refuse_warm_cache(self) -> None:
        for module in ("driven_event_selector", "primitive_screen"):
            with self.subTest(module=module), tempfile.TemporaryDirectory() as temporary:
                for mode in ("seed", "stale"):
                    flags = ["-O"] if sys.flags.optimize else []
                    result = subprocess.run(
                        [sys.executable, *flags, "-c", IMPORT_PROBE, mode, temporary, module],
                        cwd=pipeline.ROOT, capture_output=True, text=True, timeout=20, check=False,
                    )
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
