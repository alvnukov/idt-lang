"""A module already loaded before a checkout edit cannot bless a relay report."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Keep each import-order probe in its own interpreter. A comment-only simulated
# edit leaves the actual science code untouched. The seed run sees the same new
# bytes from the start, so its cache key can genuinely match the stale process's
# on-disk provenance; it is not merely a cache miss under a different digest.
IMPORT_PROBE = """
import hashlib
import importlib
import sys
from pathlib import Path
from unittest.mock import patch

mode, scratch_name, module_name = sys.argv[1:]
scratch = Path(scratch_name)
relative = f'theory_experiments/{module_name}.py'
source = Path.cwd() / relative
original_read_bytes = Path.read_bytes
original_bytes = original_read_bytes(source)
changed_bytes = original_bytes + b'\\n# simulated pre-pipeline checkout edit\\n'
old_hash = hashlib.sha256(original_bytes).hexdigest()
new_hash = hashlib.sha256(changed_bytes).hexdigest()

def need(condition, message):
    if not condition:
        raise AssertionError(message)

def simulate_disk_read(path):
    return changed_bytes if path == source else original_read_bytes(path)

def refused(thunk, label):
    try:
        thunk()
    except ValueError as error:
        need(f'marked relay source changed since import: {relative}' in str(error),
             f'{label}: wrong failure: {error}')
    else:
        raise AssertionError(f'{label}: stale adapter returned instead of refusing')

if mode == 'stale':
    loaded = importlib.import_module(f'theory_experiments.{module_name}')
    need(loaded.LOADED_SOURCE_SHA256 == old_hash, 'module preloaded against old source')
    need('theory_experiments.candidate_pipeline' not in sys.modules,
         'must not arrive through an already-loaded pipeline')

with patch.object(Path, 'read_bytes', simulate_disk_read):
    from theory_experiments import candidate_pipeline as pipeline
    from theory_experiments.candidate_history import History, record_batch
    from theory_experiments.primitive_screen import Limits, load_json

    spec = {'family': 'marked_relay', 'id': 'provenance_probe',
            'transitions': [[0, 0, 0, 0]], 'marker_classes': [0],
            'origin_contract': 'fixed', 'origin': 0, 'program': 'through_six'}
    limits = Limits(max_cases=1)
    cache = scratch / 'prior-cache'
    need(pipeline.LOADED_SOURCE_HASHES[relative] == new_hash, 'pipeline snapshotted new source')
    need(pipeline.provenance()['source_sha256'][relative] == new_hash, 'disk probe shows new source')
    if mode == 'seed':
        first, = pipeline.run_batch([spec], limits, cache, fresh=True)
        need(not first.reused and first.artifact.is_file(), 'create ordinary fresh cache entry')
        need(first.report['status'] == 'counterexample', 'ordinary finite probe ran')
        hit, = pipeline.run_batch([spec], limits, cache)
        need(hit.reused and hit.report == first.report, 'ordinary cache hit works')
        need(pipeline.replay_artifact(first.artifact) == first.report, 'ordinary replay works')
    else:
        need(loaded.LOADED_SOURCE_SHA256 == old_hash, 'pipeline reused preloaded module')
        model = pipeline.parse_hypothesis(spec)
        request = pipeline.request_for(model, limits, pipeline.provenance())
        artifact = cache / (pipeline.digest(request) + '.json')
        need(artifact.is_file(), 'would hit prior cache at this exact request key')
        need(load_json(artifact)['report']['request'] == request, 'prior request is current-disk request')
        before = original_read_bytes(artifact)
        missing = scratch / 'missing-cache'
        refused(lambda: pipeline.run_batch([spec], limits, missing), 'cache miss')
        need(not missing.exists(), 'no empty cache directory created before failure')
        refused(lambda: pipeline.run_batch([spec], limits, cache), 'cache hit')
        refused(lambda: pipeline.run_batch([spec], limits, cache, fresh=True), 'fresh run')
        refused(lambda: pipeline.read_entry(artifact, request), 'cache verification')
        refused(lambda: pipeline.compute(model, limits, request), 'direct verification')
        refused(lambda: pipeline.replay_artifact(artifact), 'replay')
        need(original_read_bytes(artifact) == before, 'prior cache unchanged')

        history = History(scratch / 'history')
        refused(lambda: record_batch([spec], limits, cache, history=history), 'history run')
        need(not (history.root / 'baselines').exists(), 'operational error did not pin a baseline')
        errors = list((history.root / 'observations').glob('*.json.gz'))
        need(len(errors) == 1, 'operational error was retained separately')
        saved = history.get('observations', errors[0].name.removesuffix('.json.gz'))
        need(saved['reports'] == [] and str(saved['execution_error']).startswith('ValueError:'),
             'no candidate verdict was retained for the error')

need(original_read_bytes(source) == original_bytes, 'repository source was not edited')
"""


class RelayImportProvenanceTests(unittest.TestCase):
    def _run_probe(self, module: str) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            for mode in ("seed", "stale"):
                with self.subTest(module=module, mode=mode):
                    command = [sys.executable]
                    if sys.flags.optimize:
                        command.append("-O")
                    command.extend(("-c", IMPORT_PROBE, mode, scratch, module))
                    result = subprocess.run(
                        command,
                        cwd=ROOT,
                        capture_output=True,
                        text=True,
                        check=False,
                        timeout=15,
                    )
                    self.assertEqual(
                        result.returncode, 0, result.stdout + result.stderr
                    )

    def test_relay_code_preloaded_before_pipeline_has_separate_source_hash(
        self,
    ) -> None:
        self._run_probe("marked_relay")

    def test_shared_primitive_helpers_preloaded_before_pipeline_have_separate_hash(
        self,
    ) -> None:
        self._run_probe("primitive_screen")
