"""Cache equivalence, fail-closed evidence handling and compact CLI contracts."""

from __future__ import annotations

import io
import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts.screen_hypotheses import main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import primitive_screen as primitive
from theory_experiments.primitive_screen import Limits, canonical_json, object_fields


def specifications(*names: str) -> list[object]:
    return [pipeline.controls()[name].specification() for name in names]


class PipelineTests(unittest.TestCase):
    def test_batch_single_and_legacy_checks_agree(self) -> None:
        specs = specifications(*pipeline.controls())
        batch = pipeline.run_batch(specs)
        singles = tuple(pipeline.run_batch([spec])[0] for spec in specs)
        self.assertEqual([r.report for r in batch], [r.report for r in singles])
        for result, candidate in zip(batch[:3], primitive.builtin_candidates().values()):
            self.assertEqual(result.report["checks"], [check.specification()
                             for check in primitive.evaluate(candidate, Limits())])
        self.assertEqual(pipeline.exit_code(batch), 1)

    def test_cache_hit_never_executes_and_retains_full_report(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            first = pipeline.run_batch(specifications("qm_born", "sm_bad_charge"), cache_dir=path)
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache hit executed")):
                second = pipeline.run_batch(specifications("qm_born", "sm_bad_charge"), cache_dir=path)
            self.assertEqual([r.report for r in first], [r.report for r in second])
            self.assertFalse(any(r.reused for r in first))
            self.assertTrue(all(r.reused for r in second))
            self.assertEqual(len(list(path.iterdir())), 2)
            for result in second:
                assert result.artifact is not None
                self.assertEqual(pipeline.replay_artifact(result.artifact), result.report)
                self.assertEqual(result.card()["proof_status"], "not_attempted")

    def test_identical_requests_deduplicate_but_keep_order(self) -> None:
        with patch.object(pipeline, "compute", wraps=pipeline.compute) as compute:
            results = pipeline.run_batch(specifications("qm_born", "sm_reference", "qm_born"))
        self.assertEqual(compute.call_count, 2)
        self.assertEqual([r.reused for r in results], [False, False, True])
        self.assertEqual(results[0].report, results[2].report)

    def test_bounds_change_key_and_do_not_promote_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            first = pipeline.run_batch(specifications("non_psd"), Limits(reference_radius=1), path)[0]
            second = pipeline.run_batch(specifications("non_psd"), Limits(reference_radius=2), path)[0]
            self.assertNotEqual(first.key, second.key)
            self.assertFalse(second.reused)
            self.assertEqual(first.report["status"], "no_counterexample_within_bounds")
            self.assertEqual(second.report["status"], "counterexample")
        limited = pipeline.run_batch(specifications("qm_born"), Limits(max_cases=1))
        self.assertEqual(limited[0].card()["status"], "inconclusive")
        self.assertEqual(pipeline.exit_code(limited), 3)

    def test_provenance_and_candidate_changes_invalidate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            baseline = pipeline.run_batch(specifications("qm_born"), cache_dir=path)[0]
            changed = dict(pipeline.provenance())
            changed["runtime"] = {"version": "different runtime"}
            with patch.object(pipeline, "provenance", return_value=changed):
                other = pipeline.run_batch(specifications("qm_born"), cache_dir=path)[0]
            self.assertNotEqual(baseline.key, other.key)
            self.assertFalse(other.reused)
            changed["source_sha256"] = {"test": "changed dependency"}
            with patch.object(pipeline, "provenance", return_value=changed), patch.object(
                    pipeline, "LOADED_SOURCE_HASHES", changed["source_sha256"]):
                newer = pipeline.run_batch(specifications("qm_born"), cache_dir=path)[0]
            self.assertNotEqual(other.key, newer.key)
            mutated = object_fields(specifications("qm_born")[0])
            mutated["norm_power"] = 2
            self.assertNotEqual(baseline.key, pipeline.run_batch([mutated], cache_dir=path)[0].key)

    def test_corruption_partial_symlink_and_wrong_request_fail_closed(self) -> None:
        for failure in ("truncated", "digest", "key", "symlink"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                result = pipeline.run_batch(specifications("qm_born"), cache_dir=Path(directory))[0]
                artifact = result.artifact
                assert artifact is not None
                if failure == "truncated":
                    artifact.write_text("{", encoding="utf-8")
                elif failure == "symlink":
                    target = Path(directory) / "original.json"
                    artifact.rename(target)
                    artifact.symlink_to(target)
                else:
                    envelope = object_fields(json.loads(artifact.read_text(encoding="utf-8")))
                    if failure == "key":
                        envelope["key"] = "wrong request"
                    else:
                        report = object_fields(envelope["report"])
                        report["status"] = "counterexample"
                        envelope["report"] = report
                    artifact.write_text(canonical_json(envelope), encoding="utf-8")
                before = artifact.read_bytes()
                with self.assertRaises((ValueError, OSError)):
                    pipeline.run_batch(specifications("qm_born"), cache_dir=Path(directory))
                self.assertEqual(artifact.read_bytes(), before)

    def test_oversized_and_nonregular_entries_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = pipeline.run_batch(specifications("qm_born"), cache_dir=path)[0]
            assert result.artifact is not None
            request = object_fields(result.report["request"])
            result.artifact.write_bytes(b" " * 524289)
            with self.assertRaisesRegex(ValueError, "512 KiB"):
                pipeline.read_entry(result.artifact, request)
            with self.assertRaises((ValueError, OSError)):
                pipeline.read_entry(path, request)

    def test_fresh_recomputes_and_rejects_conflict_without_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = pipeline.run_batch(specifications("qm_born"), cache_dir=path)[0]
            assert result.artifact is not None
            with patch.object(pipeline, "compute", wraps=pipeline.compute) as compute:
                fresh = pipeline.run_batch(specifications("qm_born"), cache_dir=path, fresh=True)[0]
            self.assertEqual(compute.call_count, 1)
            self.assertFalse(fresh.reused)
            self.assertEqual(fresh.report, result.report)
            before = result.artifact.read_bytes()
            conflict = dict(result.report)
            conflict["status"] = "counterexample"
            with self.assertRaisesRegex(ValueError, "disagrees"):
                pipeline.publish(result.artifact, conflict, object_fields(result.report["request"]))
            self.assertEqual(result.artifact.read_bytes(), before)
            self.assertFalse(list(path.glob(".screen-*")))

    def test_competing_publishers_are_atomic(self) -> None:
        result = pipeline.run_batch(specifications("sm_reference"))[0]
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / (result.key + ".json")
            request = object_fields(result.report["request"])
            with ThreadPoolExecutor(max_workers=2) as pool:
                pending = [pool.submit(pipeline.publish, target, result.report, request) for _ in range(2)]
                for future in pending:
                    future.result()
            self.assertEqual(pipeline.read_entry(target, request), result.report)
            self.assertEqual(list(Path(directory).iterdir()), [target])

    def test_replay_executes_not_cache_hit_and_rejects_changed_sources(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = pipeline.run_batch(specifications("qm_born"), cache_dir=Path(directory))[0]
            assert result.artifact is not None
            with patch.object(pipeline, "compute", wraps=pipeline.compute) as compute:
                self.assertEqual(pipeline.replay_artifact(result.artifact), result.report)
            self.assertEqual(compute.call_count, 1)
            with patch.object(pipeline, "provenance", return_value={}), self.assertRaisesRegex(ValueError, "sources/runtime"):
                pipeline.replay_artifact(result.artifact)

    def test_source_change_mid_run_aborts_before_publication(self) -> None:
        first = pipeline.provenance()
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(pipeline, "provenance", side_effect=[first, {}]), self.assertRaisesRegex(ValueError, "sources changed"):
                pipeline.run_batch(specifications("qm_born"), cache_dir=Path(directory))
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_old_loaded_code_cannot_claim_new_disk_hashes(self) -> None:
        changed = dict(pipeline.provenance())
        changed["source_sha256"] = {"changed": "on disk only"}
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(pipeline, "provenance", return_value=changed), self.assertRaisesRegex(ValueError, "since import"):
                pipeline.run_batch(specifications("qm_born"), cache_dir=Path(directory))
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_invalid_batch_validates_all_before_writes(self) -> None:
        for specs in ([], specifications("qm_born") * 65, specifications("qm_born") + [{}]):
            with tempfile.TemporaryDirectory() as directory:
                with self.assertRaises(ValueError):
                    pipeline.run_batch(specs, cache_dir=Path(directory))
                self.assertEqual(list(Path(directory).iterdir()), [])

    def test_cli_card_full_input_and_exit_contracts(self) -> None:
        for names, expected in ((["qm_born", "sm_reference"], 0), (["qm_fourth"], 1), (["fourth"], 1)):
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(main(["--builtin", *names, "--no-cache"]), expected)
            for line in output.getvalue().splitlines():
                card = object_fields(json.loads(line))
                self.assertEqual(card["empirical_status"], "not_tested")
                self.assertIn("checks", card)
        with redirect_stdout(io.StringIO()):
            self.assertEqual(main(["--builtin", "qm_born", "--no-cache", "--max-cases", "1"]), 3)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "batch.json"
            for raw in ('[{"id":"x","id":"y"}]', '[NaN]', '[]'):
                source.write_text(raw, encoding="utf-8")
                with redirect_stderr(io.StringIO()):
                    self.assertEqual(main(["--batch-file", str(source), "--no-cache"]), 2)


if __name__ == "__main__":
    unittest.main()
