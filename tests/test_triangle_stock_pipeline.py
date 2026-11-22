"""Submitted triangle-stock identities: bounded results and source-safe replay."""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.primitive_screen import Limits

MODEL_PATH = "theory_experiments/triangle_stock.py"
PASS = "no_counterexample_within_bounds"
FAIL = "counterexample"


def specification(**changes: object) -> dict[str, object]:
    result: dict[str, object] = {
        "id": "submitted_quadratic", "family": "triangle_stock", "modulus": 1,
        "default_forms": [[0, 1, 0], [1, 0, 0], [1, 1, 0]],
        "overrides": [], "gains": ["4", "4", "4"],
    }
    result.update(changes)
    return result


class TriangleStockPipelineTests(unittest.TestCase):
    def test_supplied_identity_and_mismatched_gain_have_narrow_scope(self) -> None:
        specs = [specification(), specification(id="wrong_gain", gains=["4", "4", "3"])]
        results = pipeline.run_batch(specs, fresh=True)
        self.assertEqual([result.report["status"] for result in results], [PASS, FAIL])
        for spec, result in zip(specs, results, strict=True):
            self.assertEqual(pipeline.parse_hypothesis(spec).specification(), spec)
            self.assertEqual(result.card()["family"], "triangle_stock")
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            self.assertEqual(result.report["rejection_scope"],
                             "only_submitted_quasipolynomial_and_gain_law")
            self.assertEqual(result.report["evidence_kind"],
                             "computation_with_explicit_algebraic_or_bounded_scope")
            self.assertFalse(result.reused)
            self.assertIsNone(result.artifact)
            self.assertEqual(result.report["checks"][0]["id"], "triangle_stock_split_gain")
        self.assertEqual(results[0].report["checks"][0]["planned"], 18)
        self.assertEqual(results[0].report["checks"][0]["checked"], 18)
        self.assertIs(results[0].report["scope"]["identity_certified_on_submitted_integer_domain"], True)
        self.assertIs(results[1].report["scope"]["identity_certified_on_submitted_integer_domain"], False)
        witness = results[1].report["checks"][0]["witness"]
        values = witness["inputs"]
        self.assertEqual(Fraction(witness["actual"]),
                         values["plus_stock"] + values["minus_stock"]
                         - Fraction(values["claimed_gain"]) * values["input_stock"])
        self.assertNotEqual(Fraction(witness["actual"]), 0)
        self.assertEqual(pipeline.exit_code(results), 1)

    def test_case_budget_is_not_a_counterexample_or_completed_identity(self) -> None:
        short, = pipeline.run_batch([specification()], Limits(max_cases=17))
        full, = pipeline.run_batch([specification()], Limits(max_cases=18))
        self.assertEqual(short.report["status"], "inconclusive")
        self.assertEqual(short.report["checks"][0]["checked"], 17)
        self.assertIs(short.report["scope"]["identity_certified_on_submitted_integer_domain"], False)
        self.assertIsNone(short.report["checks"][0]["witness"])
        self.assertEqual(full.report["status"], PASS)
        self.assertNotEqual(short.key, full.key)
        self.assertEqual(pipeline.exit_code((short,)), 3)

    def test_zero_stock_and_nonzero_origin_are_unsupported_not_rejected(self) -> None:
        specs = [specification(id="zero_stock", default_forms=[]),
                 specification(id="nonzero_origin", default_forms=[[1, 0, 1]])]
        results = pipeline.run_batch(specs)
        self.assertEqual([result.report["status"] for result in results], ["unsupported"] * 2)
        self.assertEqual(pipeline.exit_code(results), 3)
        for result in results:
            self.assertIsNone(result.report["checks"][0]["witness"])
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            self.assertIs(result.report["scope"]["identity_certified_on_submitted_integer_domain"], False)

    def test_temporary_mixed_cache_fresh_replay_and_adapter_hash(self) -> None:
        specs = [specification(), specification(id="wrong_gain", gains=["4", "4", "3"]),
                 specification(id="zero_stock", default_forms=[])]
        expected = hashlib.sha256((pipeline.ROOT / MODEL_PATH).read_bytes()).hexdigest()
        self.assertIn(MODEL_PATH, pipeline.SOURCE_PATHS)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            first = pipeline.run_batch(specs, cache_dir=cache, fresh=True)
            before = {path: path.read_bytes() for path in cache.iterdir()}
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache recomputed")):
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
            self.assertEqual([result.reused for result in duplicate], [False, True])
            self.assertEqual(before, {path: path.read_bytes() for path in cache.iterdir()})

    def test_canonical_input_and_whole_batch_validation(self) -> None:
        model = pipeline.parse_hypothesis(specification(gains=["8/2", "4", "4"]))
        self.assertEqual(model.specification()["gains"], ["4", "4", "4"])
        for changes in ({"extra": True}, {"modulus": True}, {"gains": [4, 4, 4]}):
            with self.subTest(changes=changes), tempfile.TemporaryDirectory() as temporary:
                cache = Path(temporary) / "absent"
                with self.assertRaises((ValueError, TypeError)):
                    pipeline.run_batch([specification(), specification(**changes)], cache_dir=cache)
                self.assertFalse(cache.exists())

    def test_direct_compute_and_cache_read_refuse_changed_disk(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            result, = pipeline.run_batch([specification()], cache_dir=Path(temporary))
            request = result.report["request"]
            model = pipeline.parse_hypothesis(request["candidate"])
            original_read = Path.read_bytes
            for relative in (MODEL_PATH, "theory_experiments/primitive_screen.py"):
                source = pipeline.ROOT / relative
                changed = original_read(source) + b"\n# simulated post-import edit\n"

                def disk_read(path: Path) -> bytes:
                    return changed if path == source else original_read(path)

                with self.subTest(relative=relative), patch.object(Path, "read_bytes", disk_read):
                    with self.assertRaisesRegex(ValueError, "triangle stock source changed since import"):
                        pipeline.compute(model, Limits(), request)
                    with self.assertRaisesRegex(ValueError, "triangle stock source changed since import"):
                        pipeline.read_entry(result.artifact, request)


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
        need(f'triangle stock source changed since import: {relative}' in str(error), str(error))
    else:
        raise AssertionError('stale source returned a result')

if mode == 'stale':
    loaded = importlib.import_module(f'theory_experiments.{module_name}')
    need(loaded.LOADED_SOURCE_SHA256 == hashlib.sha256(original).hexdigest(), 'old source loaded')
    need('theory_experiments.candidate_pipeline' not in sys.modules, 'pipeline not yet loaded')

with patch.object(Path, 'read_bytes', disk_read):
    from theory_experiments import candidate_pipeline as pipeline
    from theory_experiments.primitive_screen import Limits
    spec = {'id':'stale_probe','family':'triangle_stock','modulus':1,
            'default_forms':[[1,0,0],[0,1,0],[1,1,0]],'overrides':[], 'gains':['4','4','4']}
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


class TriangleStockPreloadedSourceTests(unittest.TestCase):
    def test_adapter_and_shared_helper_preloaded_before_pipeline_refuse_warm_cache(self) -> None:
        for module in ("triangle_stock", "primitive_screen"):
            with self.subTest(module=module), tempfile.TemporaryDirectory() as temporary:
                for mode in ("seed", "stale"):
                    flags = ["-O"] if sys.flags.optimize else []
                    result = subprocess.run(
                        [sys.executable, *flags, "-c", IMPORT_PROBE, mode, temporary, module],
                        cwd=pipeline.ROOT, capture_output=True, text=True, timeout=20, check=False,
                    )
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
