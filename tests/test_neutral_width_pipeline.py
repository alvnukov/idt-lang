"""Descriptive neutral-current comparisons with temporary, source-guarded caches."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import neutral_current_width as width
from theory_experiments.primitive_screen import Limits

MODEL_PATH = "theory_experiments/neutral_current_width.py"
PASS = "no_counterexample_within_bounds"


def specification(count: int = 3, **changes: object) -> dict[str, object]:
    result: dict[str, object] = {
        "id": f"supplied_{count}", "family": "neutral_current_width",
        "species": [f"nu_{j}" for j in range(count)],
        "mass_regime": "all_negligible", "bridge": "standard_invisible_left_current_only",
        "left_current_matrix": [[[str(int(i == j)), "0"] for j in range(count)]
                                for i in range(count)],
    }
    result.update(changes)
    return result


class NeutralWidthPipelineTests(unittest.TestCase):
    def test_far_and_near_comparisons_are_completion_not_candidate_rejection(self) -> None:
        results = pipeline.run_batch([specification(3), specification(4)], fresh=True)
        for count, result in zip((3, 4), results, strict=True):
            report = result.report
            self.assertEqual(report["status"], PASS)
            self.assertEqual(report["proof_status"], "not_attempted")
            self.assertEqual(report["empirical_status"], "not_tested")
            self.assertEqual(report["evidence_kind"], "descriptive_completion_only")
            self.assertEqual(report["rejection_scope"],
                             "published_summary_comparison_not_candidate_rejection")
            self.assertEqual(report["scope"]["candidate_verdict"], "not_assessed")
            self.assertEqual(report["scope"]["prediction"]["effective_species"], str(count))
            self.assertEqual(report["scope"]["execution_status"], "complete")
            self.assertEqual(report["scope"]["comparison"]["candidate_ranking"], "not_attempted")
            check, = report["checks"]
            self.assertIsNone(check["witness"])
            self.assertEqual((check["checked"], check["planned"]), (count * count, count * count))
            self.assertEqual(result.card()["family"], "neutral_current_width")
        self.assertEqual(pipeline.exit_code(results), 0)

    def test_unmapped_and_budgeted_inputs_are_not_rejections(self) -> None:
        specs = [specification(bridge="unmapped"),
                 specification(mass_regime="threshold_or_unknown"), specification()]
        results = pipeline.run_batch(specs, Limits(max_cases=1))
        self.assertEqual([result.report["status"] for result in results],
                         ["unsupported", "unsupported", "inconclusive"])
        self.assertEqual(pipeline.exit_code(results), 3)
        for result in results:
            self.assertNotIn("comparison", result.report["scope"])
            self.assertNotIn("effective_species", result.report["scope"]["prediction"])
            self.assertIsNone(result.report["checks"][0]["witness"])
            self.assertEqual(result.report["empirical_status"], "not_tested")

    def test_temporary_cache_fresh_replay_and_pinned_data_provenance(self) -> None:
        specs = [specification(3), specification(4), specification(bridge="unmapped")]
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary)
            first = pipeline.run_batch(specs, cache_dir=cache, fresh=True)
            before = {path: path.read_bytes() for path in cache.iterdir()}
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache recomputed")):
                hits = pipeline.run_batch(specs, cache_dir=cache)
            for original, hit in zip(first, hits, strict=True):
                self.assertTrue(hit.reused)
                self.assertEqual(original.report, hit.report)
                sources = hit.report["request"]["provenance"]["source_sha256"]
                self.assertEqual(sources[width.DATA_PATH], width.DATA_SHA256)
                self.assertEqual(sources[MODEL_PATH], width.LOADED_SOURCE_SHA256)
                self.assertEqual(pipeline.replay_artifact(hit.artifact), hit.report)
            fresh = pipeline.run_batch(specs, cache_dir=cache, fresh=True)
            self.assertTrue(all(not result.reused for result in fresh))
            self.assertEqual(before, {path: path.read_bytes() for path in cache.iterdir()})

    def test_canonical_fields_and_invalid_batch_do_not_create_cache(self) -> None:
        spec = specification(1)
        spec["left_current_matrix"] = [[["2/2", "0/2"]]]
        canonical = pipeline.parse_hypothesis(spec).specification()
        self.assertEqual(canonical["left_current_matrix"], [[["1", "0"]]])
        for changes in ({"extra_width": "1"}, {"acceptance_threshold": "3"},
                        {"data_path": "/tmp/candidate_selected.json"}):
            with self.subTest(changes=changes), tempfile.TemporaryDirectory() as temporary:
                cache = Path(temporary) / "absent"
                with self.assertRaises((TypeError, ValueError)):
                    pipeline.run_batch([specification(), specification(**changes)], cache_dir=cache)
                self.assertFalse(cache.exists())

    def test_changed_data_and_code_refuse_existing_cache_fresh_and_replay(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            cache = Path(temporary) / "cache"
            result, = pipeline.run_batch([specification()], cache_dir=cache)
            request = result.report["request"]
            candidate = pipeline.parse_hypothesis(request["candidate"])
            original_read = Path.read_bytes
            for relative in (MODEL_PATH, "theory_experiments/primitive_screen.py", width.DATA_PATH):
                source = pipeline.ROOT / relative
                changed = original_read(source) + b"\n"

                def disk_read(path: Path) -> bytes:
                    return changed if path == source else original_read(path)

                before = original_read(result.artifact)
                with self.subTest(relative=relative), patch.object(Path, "read_bytes", disk_read):
                    actions = (
                        lambda: pipeline.run_batch([specification()], cache_dir=cache),
                        lambda: pipeline.run_batch([specification()], cache_dir=cache, fresh=True),
                        lambda: pipeline.read_entry(result.artifact, request),
                        lambda: pipeline.compute(candidate, Limits(), request),
                        lambda: pipeline.replay_artifact(result.artifact),
                    )
                    for action in actions:
                        with self.assertRaisesRegex(ValueError, "neutral.current.*source|receipt.*digest"):
                            action()
                self.assertEqual(original_read(result.artifact), before)


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
        need('neutral-current source changed since import' in str(error), str(error))
    else:
        raise AssertionError('stale source returned a result')

if mode == 'stale':
    loaded = importlib.import_module(f'theory_experiments.{module_name}')
    need(loaded.LOADED_SOURCE_SHA256 == hashlib.sha256(original).hexdigest(), 'old source loaded')
    need('theory_experiments.candidate_pipeline' not in sys.modules, 'pipeline not yet loaded')

with patch.object(Path, 'read_bytes', disk_read):
    from theory_experiments import candidate_pipeline as pipeline
    from theory_experiments.primitive_screen import Limits
    spec = {'id':'stale_probe','family':'neutral_current_width','species':['nu'],
            'mass_regime':'all_negligible','bridge':'standard_invisible_left_current_only',
            'left_current_matrix':[[['1','0']]]}
    limits = Limits()
    cache = scratch / 'cache'
    if mode == 'seed':
        result, = pipeline.run_batch([spec], limits, cache, fresh=True)
        hit, = pipeline.run_batch([spec], limits, cache)
        need(hit.reused and hit.report == result.report, 'seed hit works')
        need(pipeline.replay_artifact(result.artifact) == result.report, 'seed replay works')
    else:
        candidate = pipeline.parse_hypothesis(spec)
        request = pipeline.request_for(candidate, limits, pipeline.provenance())
        artifact = cache / (pipeline.digest(request) + '.json')
        need(artifact.is_file(), 'exact warm cache request exists')
        before = original_read(artifact)
        absent = scratch / 'absent'
        refused(lambda: pipeline.run_batch([spec], limits, absent))
        need(not absent.exists(), 'no cache created')
        refused(lambda: pipeline.run_batch([spec], limits, cache))
        refused(lambda: pipeline.run_batch([spec], limits, cache, fresh=True))
        refused(lambda: pipeline.compute(candidate, limits, request))
        refused(lambda: pipeline.read_entry(artifact, request))
        refused(lambda: pipeline.replay_artifact(artifact))
        need(original_read(artifact) == before, 'cache unchanged')
need(original_read(source) == original, 'repository source unchanged')
'''


class NeutralWidthPreloadedSourceTests(unittest.TestCase):
    def test_adapter_and_shared_helper_preloaded_before_pipeline_refuse_warm_cache(self) -> None:
        for module in ("neutral_current_width", "primitive_screen"):
            with self.subTest(module=module), tempfile.TemporaryDirectory() as temporary:
                for mode in ("seed", "stale"):
                    flags = ["-O"] if sys.flags.optimize else []
                    result = subprocess.run(
                        [sys.executable, *flags, "-c", IMPORT_PROBE, mode, temporary, module],
                        cwd=pipeline.ROOT, capture_output=True, text=True, timeout=20, check=False,
                    )
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
