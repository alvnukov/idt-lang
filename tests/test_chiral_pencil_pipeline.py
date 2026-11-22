"""Scoped weighted-pencil batches, temporary caches and stale-import refusal."""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import probe_weighted_chiral_pencil as reference
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.primitive_screen import Limits

MODEL_PATH = "theory_experiments/chiral_pencil.py"
PASS = "no_counterexample_within_bounds"
FAIL = "counterexample"


def synthetic_specs() -> list[dict[str, object]]:
    """Independent archived constructor supplies inputs, never expected verdicts."""
    signs = reference.exterior_witness()
    lookup = {edge: str(1 - 2 * ((signs >> j) & 1))
              for j, edge in enumerate(reference.EDGES)}
    weights = [lookup[edge] for edge in reference.WE]
    corrupt = weights.copy()
    corrupt[0] = str(2 * int(corrupt[0]))
    zero = weights.copy()
    zero[0] = "0"
    return [{"id": name, "family": "chiral_pencil", "weights": values}
            for name, values in (("synthetic_valid", weights),
                                 ("synthetic_corrupt", corrupt),
                                 ("synthetic_zero", zero))]


class ChiralPencilPipelineTests(unittest.TestCase):
    def test_mixed_fresh_batch_preserves_scope_and_unsupported_status(self) -> None:
        specs = synthetic_specs()
        results = pipeline.run_batch(specs, Limits(max_cases=5000), fresh=True)
        self.assertEqual([result.report["status"] for result in results],
                         [PASS, FAIL, "unsupported"])
        for spec, result in zip(specs, results, strict=True):
            self.assertEqual(pipeline.parse_hypothesis(spec).specification(), spec)
            self.assertEqual(result.card()["family"], "chiral_pencil")
            self.assertEqual(result.report["proof_status"], "not_attempted")
            self.assertEqual(result.report["empirical_status"], "not_tested")
            self.assertEqual(result.report["scope"]["scientific_status"], "unassessed")
            self.assertEqual(result.report["rejection_scope"],
                             "specified_weighted_support_and_rank_holdout_only")
            self.assertFalse(result.reused)
            self.assertIsNone(result.artifact)
        self.assertEqual(pipeline.exit_code(results), 1)
        self.assertEqual(pipeline.exit_code((results[2],)), 3)
        witness = results[1].report["checks"][0]["witness"]
        self.assertEqual(witness["inputs"]["direct_symmetric_rational_rank"], 10)
        check = results[2].report["checks"][0]
        self.assertEqual((check["checked"], check["planned"]), (0, 0))
        self.assertIsNone(check["witness"])

    def test_budget_and_zero_are_not_false_rejections(self) -> None:
        valid, _, zero = synthetic_specs()
        short = pipeline.run_batch([valid, zero], Limits(max_cases=1))
        self.assertEqual([result.report["status"] for result in short],
                         ["inconclusive", "unsupported"])
        self.assertEqual(pipeline.exit_code(short), 3)
        for result in short:
            self.assertIsNone(result.report["checks"][0]["witness"])
        full, = pipeline.run_batch([valid], Limits(max_cases=5000))
        self.assertNotEqual(short[0].key, full.key)

    def test_temporary_cache_replay_and_adapter_provenance(self) -> None:
        specs = synthetic_specs()
        limits = Limits(max_cases=5000)
        expected_hash = hashlib.sha256((pipeline.ROOT / MODEL_PATH).read_bytes()).hexdigest()
        self.assertIn(MODEL_PATH, pipeline.SOURCE_PATHS)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary) / "cache"
            fresh = pipeline.run_batch(specs, limits, cache, fresh=True)
            before = {path: path.read_bytes() for path in cache.iterdir()}
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache recomputed")):
                cached = pipeline.run_batch(specs, limits, cache)
            for original, hit in zip(fresh, cached, strict=True):
                self.assertTrue(hit.reused)
                self.assertEqual(original.key, hit.key)
                self.assertEqual(original.report, hit.report)
                self.assertEqual(hit.report["request"]["provenance"]["source_sha256"][MODEL_PATH],
                                 expected_hash)
                self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            repeated = pipeline.run_batch([specs[0], specs[0]], limits, fresh=True)
            self.assertEqual([result.reused for result in repeated], [False, True])
            self.assertEqual(before, {path: path.read_bytes() for path in cache.iterdir()})

    def test_entire_batch_is_validated_before_cache_creation(self) -> None:
        specs = synthetic_specs()
        invalid = dict(specs[0], unexpected=True)
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary) / "absent"
            with self.assertRaises((TypeError, ValueError)):
                pipeline.run_batch([specs[0], invalid], cache_dir=cache)
            self.assertFalse(cache.exists())

    def test_direct_compute_and_cache_read_check_current_disk_too(self) -> None:
        spec = synthetic_specs()[2]
        with tempfile.TemporaryDirectory() as temporary:
            result, = pipeline.run_batch([spec], cache_dir=Path(temporary))
            request = result.report["request"]
            model = pipeline.parse_hypothesis(spec)
            original_read = Path.read_bytes
            for relative in (MODEL_PATH, "theory_experiments/primitive_screen.py"):
                source = pipeline.ROOT / relative
                changed = original_read(source) + b"\n# simulated post-import edit\n"

                def disk_read(path: Path) -> bytes:
                    return changed if path == source else original_read(path)

                with self.subTest(relative=relative), patch.object(Path, "read_bytes", disk_read):
                    with self.assertRaisesRegex(ValueError, "chiral pencil source changed since import"):
                        pipeline.compute(model, Limits(), request)
                    with self.assertRaisesRegex(ValueError, "chiral pencil source changed since import"):
                        pipeline.read_entry(result.artifact, request)


# Simulate comment-only edits without touching repository files. The seed
# process imports all modules against the changed bytes; the stale process
# preloads exactly one old module before the pipeline snapshots new disk bytes.
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
old_hash = hashlib.sha256(original).hexdigest()
new_hash = hashlib.sha256(changed).hexdigest()

def need(condition, message):
    if not condition:
        raise AssertionError(message)

def disk_read(path):
    return changed if path == source else original_read(path)

def refused(thunk):
    try:
        thunk()
    except ValueError as error:
        need(f'chiral pencil source changed since import: {relative}' in str(error), str(error))
    else:
        raise AssertionError('stale source produced a report')

if mode == 'stale':
    loaded = importlib.import_module(f'theory_experiments.{module_name}')
    need(loaded.LOADED_SOURCE_SHA256 == old_hash, 'old module hash')
    need('theory_experiments.candidate_pipeline' not in sys.modules, 'pipeline not yet imported')

with patch.object(Path, 'read_bytes', disk_read):
    from theory_experiments import candidate_pipeline as pipeline
    from theory_experiments.primitive_screen import Limits
    spec = {'id': 'stale_probe', 'family': 'chiral_pencil', 'weights': ['0'] * 40}
    limits = Limits(max_cases=1)
    cache = scratch / 'cache'
    need(pipeline.LOADED_SOURCE_HASHES[relative] == new_hash, 'pipeline snapshots disk')
    if mode == 'seed':
        first, = pipeline.run_batch([spec], limits, cache, fresh=True)
        hit, = pipeline.run_batch([spec], limits, cache)
        need(hit.reused and first.report == hit.report, 'seed cache works')
        need(pipeline.replay_artifact(first.artifact) == first.report, 'seed replay works')
    else:
        model = pipeline.parse_hypothesis(spec)
        request = pipeline.request_for(model, limits, pipeline.provenance())
        artifact = cache / (pipeline.digest(request) + '.json')
        need(artifact.is_file(), 'exact stale request cache entry exists')
        before = original_read(artifact)
        absent = scratch / 'absent'
        refused(lambda: pipeline.run_batch([spec], limits, absent))
        need(not absent.exists(), 'no cache created')
        refused(lambda: pipeline.run_batch([spec], limits, cache))
        refused(lambda: pipeline.run_batch([spec], limits, cache, fresh=True))
        refused(lambda: pipeline.read_entry(artifact, request))
        refused(lambda: pipeline.compute(model, limits, request))
        refused(lambda: pipeline.replay_artifact(artifact))
        need(original_read(artifact) == before, 'cache unchanged')
need(original_read(source) == original, 'repository source unchanged')
'''


class ChiralPencilImportProvenanceTests(unittest.TestCase):
    def test_preloaded_adapter_and_primitive_helpers_cannot_bless_new_disk_hashes(self) -> None:
        for module in ("chiral_pencil", "primitive_screen"):
            with self.subTest(module=module), tempfile.TemporaryDirectory() as temporary:
                for mode in ("seed", "stale"):
                    flags = ["-O"] if sys.flags.optimize else []
                    result = subprocess.run(
                        [sys.executable, *flags, "-c", IMPORT_PROBE, mode, temporary, module],
                        cwd=pipeline.ROOT, capture_output=True, text=True, timeout=20,
                        check=False,
                    )
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
