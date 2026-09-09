"""History detects false rejection as well as false survival, without truth labels."""

from __future__ import annotations

import copy
import io
import json
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts.check_candidate_history import main as history_main
from scripts.import_candidate_campaign import import_campaign
from scripts.screen_hypotheses import main as screen_main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    History,
    compare,
    recheck_history,
    record_batch,
)
from theory_experiments.primitive_screen import Limits, canonical_json, object_fields


def specifications(*names: str) -> list[object]:
    return [pipeline.controls()[name].specification() for name in names]


class CandidateHistoryTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.history = History(self.root / "history")

    def test_all_verdicts_retained_and_freshly_rechecked_without_writes(self) -> None:
        specs = specifications("qm_born", "qm_fourth", "sm_reference", "non_psd")
        run = record_batch(specs, history=self.history)
        self.assertEqual(self.history.get("submissions", run.submission)["candidates"], specs)
        self.assertEqual(self.history.get("observations", run.observation)["reports"],
                         [result.report for result in run.results])
        before = {p: p.read_bytes() for p in self.history.root.rglob("*") if p.is_file()}
        with patch.object(pipeline, "compute", wraps=pipeline.compute) as compute:
            result = recheck_history(self.history)
        self.assertEqual(compute.call_count, 4)
        self.assertEqual(result["status"], "unchanged")
        self.assertEqual(result["candidates"], 4)
        self.assertEqual(before, {p: p.read_bytes() for p in self.history.root.rglob("*") if p.is_file()})

    def test_incomplete_and_unsupported_are_not_rejections(self) -> None:
        spec: object = {"id": "power_two", "family": "power_sum", "dimension": 2, "exponent": 2}
        run = record_batch([spec], history=self.history)
        self.assertEqual(run.results[0].report["status"], "unsupported")
        partial = record_batch(specifications("qm_born"), Limits(max_cases=1), history=self.history)
        self.assertEqual(partial.results[0].report["status"], "inconclusive")
        self.assertEqual(recheck_history(self.history)["status"], "unchanged")

    def test_version_metadata_changes_do_not_disguise_semantic_regressions(self) -> None:
        record_batch(specifications("qm_born"), history=self.history)
        sources = pipeline.provenance()
        sources["runtime"] = {"version": "a different Python release"}
        with patch.object(pipeline, "provenance", return_value=sources):
            result = recheck_history(self.history, record=True)
        self.assertEqual(result["status"], "unchanged")
        self.assertEqual(len(list((self.history.root / "observations").glob("*.json.gz"))), 2)

    def test_false_rejection_and_return_of_rejected_candidate_both_require_review(self) -> None:
        run = record_batch(specifications("qm_born", "qm_fourth"), history=self.history)
        original = pipeline.compute

        def flipped(candidate: pipeline.Hypothesis, limits: Limits,
                    request: dict[str, object]) -> dict[str, object]:
            report = original(candidate, limits, request)
            report["status"] = ("counterexample" if candidate.id == "qm_born"
                                else "no_counterexample_within_bounds")
            return report

        with patch.object(pipeline, "compute", side_effect=flipped):
            changed = recheck_history(self.history, record=True)
            again = record_batch(specifications("qm_born", "qm_fourth"), history=self.history)
        self.assertEqual(changed["status"], "review_required")
        differences = changed["changes"]
        assert isinstance(differences, list)
        self.assertEqual(len(differences), 2)
        self.assertEqual(len(again.changes), 2)
        self.assertNotEqual(again.observation, run.observation)
        self.assertEqual(self.history.baseline(run.submission)["reports"], [r.report for r in run.results])
        self.assertEqual(recheck_history(self.history)["status"], "unchanged")

    def test_same_status_different_assumptions_scope_counts_witness_or_check_is_flagged(self) -> None:
        run = record_batch(specifications("non_psd"), history=self.history)
        old = run.results[0].report
        for change in ("assumptions", "requirement", "checked", "planned", "witness",
                       "scope", "proof_status", "empirical_status", "check_removed", "input"):
            new = copy.deepcopy(old)
            checks = new["checks"]
            assert isinstance(checks, list)
            if change == "check_removed":
                checks.pop()
            elif change == "input":
                request = object_fields(new["request"])
                request["candidate"] = {"id": "another_input"}
                new["request"] = request
            elif change in ("scope", "proof_status", "empirical_status"):
                new[change] = "changed"
            else:
                check = object_fields(checks[0])
                check[change] = "changed"
                checks[0] = check
            with self.subTest(change=change):
                self.assertEqual(len(compare({"reports": [old]}, [new])), 1)
        with self.assertRaisesRegex(ValueError, "drop candidates"):
            compare({"reports": [old]}, [])

    def test_submission_survives_invalid_adapter_and_checker_failure(self) -> None:
        spec: object = {"id": "future_candidate", "family": "not_supported_yet"}
        with self.assertRaises(ValueError):
            record_batch([spec], history=self.history)
        self.assertEqual(len(list((self.history.root / "submissions").glob("*.json"))), 1)
        with (patch.object(pipeline, "compute", side_effect=RuntimeError("broken checker")),
              self.assertRaisesRegex(RuntimeError, "broken checker")):
            record_batch(specifications("qm_born"), history=self.history)
        result = recheck_history(self.history)
        self.assertEqual(result["status"], "review_required")
        self.assertEqual(result["candidates"], 2)
        errors = result["errors"]
        assert isinstance(errors, list)
        self.assertEqual(len(errors), 1)
        self.assertEqual(object_fields(errors[0])["meaning"], "checker_error_not_candidate_rejection")
        self.assertTrue(result["changes"])  # Recovered candidate has no baseline, not a silent pass.

    def test_one_broken_adapter_does_not_skip_neighboring_candidate(self) -> None:
        record_batch(specifications("qm_born", "qm_fourth"), history=self.history)
        original = pipeline.compute
        visited: list[str] = []

        def broken(candidate: pipeline.Hypothesis, limits: Limits,
                   request: dict[str, object]) -> dict[str, object]:
            visited.append(candidate.id)
            if candidate.id == "qm_born":
                raise RuntimeError("adapter unavailable")
            return original(candidate, limits, request)

        with patch.object(pipeline, "compute", side_effect=broken):
            result = recheck_history(self.history)
        self.assertEqual(visited, ["qm_born", "qm_fourth"])
        self.assertEqual(result["status"], "review_required")
        self.assertEqual(result["changes"], [])
        self.assertTrue(result["errors"])

    def test_original_representation_and_bounds_are_preserved(self) -> None:
        spec: object = {"id": "unreduced_fraction", "family": "pair_kernel", "matrix": [["2/2"]]}
        run = record_batch([spec], Limits(reference_radius=1), history=self.history)
        self.assertEqual(self.history.get("submissions", run.submission)["candidates"], [spec])
        normalized = object_fields(run.results[0].report["request"])["candidate"]
        self.assertNotEqual(normalized, spec)
        self.assertEqual(recheck_history(self.history)["status"], "unchanged")
        other = record_batch([spec], Limits(reference_radius=2), history=self.history)
        self.assertNotEqual(run.submission, other.submission)

    def test_duplicates_concurrent_publication_and_no_baseline_refresh(self) -> None:
        specs = specifications("qm_born", "qm_born")
        with ThreadPoolExecutor(max_workers=2) as executor:
            jobs = [executor.submit(record_batch, specs, history=self.history) for _ in range(2)]
            first, second = [job.result() for job in jobs]
        self.assertEqual(first.observation, second.observation)
        self.assertEqual(recheck_history(self.history)["candidates"], 2)
        self.assertEqual(len(list((self.history.root / "observations").glob("*.json.gz"))), 1)

    def test_corrupted_nonbaseline_observation_cannot_be_ignored(self) -> None:
        run = record_batch(specifications("qm_born"), history=self.history)
        record = self.history.get("observations", run.observation)
        record["execution_error"] = "old operational failure"
        record["reports"] = []
        key = self.history.put("observations", record)
        path = self.history.root / "observations" / (key + ".json.gz")
        path.write_bytes(b"truncated gzip")
        with self.assertRaises(OSError):
            recheck_history(self.history)

    def test_missing_records_bad_digest_and_symlinks_fail_closed(self) -> None:
        run = record_batch(specifications("qm_born"), history=self.history)
        with self.assertRaisesRegex(ValueError, "digest"):
            self.history.get("submissions", "../escape")
        path = self.history.root / "submissions" / (run.submission + ".json")
        saved = path.read_bytes()
        path.write_text("{}", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "integrity"):
            recheck_history(self.history)
        path.write_bytes(saved)
        path.unlink()
        with self.assertRaisesRegex(ValueError, "empty"):
            recheck_history(self.history)
        external = self.root / "external.json"
        external.write_bytes(saved)
        path.symlink_to(external)
        with self.assertRaises(OSError):
            self.history.get("submissions", run.submission)
        link = self.root / "history-link"
        link.symlink_to(self.history.root)
        with self.assertRaisesRegex(ValueError, "symlinks"):
            History(link).submit(specifications("qm_born"), Limits())

    def test_bounded_decompression_and_invalid_baseline_fail_closed(self) -> None:
        run = record_batch(specifications("qm_born"), history=self.history)
        with (patch("theory_experiments.candidate_history.MAX_BYTES", 100),
              self.assertRaisesRegex(ValueError, "size limit")):
            self.history.get("observations", run.observation)
        pin = self.history.root / "baselines" / (run.submission + ".json")
        value = object_fields(json.loads(pin.read_text(encoding="utf-8")))
        value["reason"] = " "
        pin.write_text(canonical_json(value), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "review reason"):
            recheck_history(self.history)

    def test_mismatched_report_cannot_be_published_for_another_candidate(self) -> None:
        submission = self.history.submit(specifications("qm_born"), Limits())
        wrong = pipeline.run_batch(specifications("qm_fourth"))[0].report
        with self.assertRaisesRegex(ValueError, "submitted candidate"):
            self.history.observe(submission, [wrong])
        self.assertFalse((self.history.root / "observations").exists())

    def test_source_change_cannot_be_a_green_cross_version_comparison(self) -> None:
        record_batch(specifications("qm_born", "qm_fourth"), history=self.history)
        changed = dict(pipeline.provenance())
        changed["source_sha256"] = {"changed": "after import"}
        with (patch.object(pipeline, "provenance", return_value=changed),
              self.assertRaisesRegex(ValueError, "since import")):
            recheck_history(self.history)

    def test_cli_no_cache_still_archives_and_signals_review(self) -> None:
        args = ["--builtin", "qm_born", "--no-cache", "--history-dir", str(self.history.root)]
        output = io.StringIO()
        with redirect_stdout(output):
            self.assertEqual(screen_main(args), 0)
        card = object_fields(json.loads(output.getvalue()))
        self.assertIsNone(card["artifact"])
        self.assertTrue(card["history"])
        with redirect_stdout(io.StringIO()):
            self.assertEqual(history_main(["--history-dir", str(self.history.root)]), 0)
        original = pipeline.compute

        def mutated(candidate: pipeline.Hypothesis, limits: Limits,
                    request: dict[str, object]) -> dict[str, object]:
            report = original(candidate, limits, request)
            report["status"] = "counterexample"
            return report

        with patch.object(pipeline, "compute", side_effect=mutated), redirect_stdout(io.StringIO()):
            self.assertEqual(screen_main(args), 4)
            self.assertEqual(history_main(["--history-dir", str(self.history.root)]), 4)
        with redirect_stderr(io.StringIO()):
            self.assertEqual(history_main(["--history-dir", str(self.root / "missing")]), 2)

    def test_campaign_import_is_lossless_and_does_not_execute_checker(self) -> None:
        source = self.root / "original"
        evidence = source / "evidence"
        evidence.mkdir(parents=True)
        specs = specifications("qm_born", "qm_fourth")
        (source / "protocol.json").write_text(canonical_json({
            "schema": "idt-finite-search-campaign/1", "limits": Limits().specification(),
            "checker_commit": "original-version"}), encoding="utf-8")
        (source / "candidates-1.json").write_text(canonical_json(specs), encoding="utf-8")
        originals = pipeline.run_batch(specs, cache_dir=evidence)
        with patch.object(pipeline, "compute", side_effect=AssertionError("must not rerun import")):
            result = import_campaign(source, self.history, baseline=True)
        self.assertEqual(result["candidates"], 2)
        records = result["records"]
        assert isinstance(records, list)
        key = object_fields(records[0])["observation"]
        assert isinstance(key, str)
        self.assertEqual(self.history.get("observations", key)["reports"], [r.report for r in originals])
        (source / "candidates-1.json").write_text(canonical_json(specs[:1]), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "lose candidates"):
            import_campaign(source, self.history)


class CommittedCandidateHistoryTests(unittest.TestCase):
    def test_both_initial_generations_and_exact_inputs_are_retained(self) -> None:
        # Fixed content addresses make deletion/substitution of original inputs or
        # observations visible, even if the total number of new candidates grows.
        records = (
            ("61c5bda3691002ee6812319faac2c3d94218af956fab0c2e9d463af8ba1ee48c",
             "3ec3c4ffa482a261b8576079f8711cb204ff66bcf26751846331ab9c60d6b3c8",
             "fa13e0435ebb48c620fdba6d08c8a033a2d2bff28c43694f8b7d31bfc4afdc82"),
            ("90d36a72be5afb1d8ab7e28aa14a64e0ae2d5f1413537b503639652c8b0bd110",
             "a61bcb66e071a233f04d27c53267d209dba7f45e8bbff7b75cf3f31da9cc2703",
             "f4ea9abf98ecf4c1bf78adea5551b0d7da91dcc4c9e07e185cbd45d82b576935"),
            ("ce686eb1e243382e0e69647820c1ed0d31cfa17c7019b2f857166d0249d5403d",
             "5e96fb7212d5dab95a92ecf64938b818747e1f589c2ef9fc4ef23afff056813e",
             "076d5fc3b835a69f04e84d9d1b9bc34d974f84592bbc0e9da64334d17db07ff6"),
            ("bccfee06dffe1192c8f5604429ee1280d241026da8a4ac7d26218b1e6c78a867",
             "3f93e0cadd8e465d5f582207567d6502044ca46d8e67123b7d949b37e4f46fb7",
             "ffa2b96a8b92cdd4075d9629905ed62ed925df4d05461877c9ee84326ee5e1fb"),
            ("136131f4bb98534931a4589890d6d7859d722267fe010ee52255b8add21f9eaa",
             "5d377f28b898f51f258511758a156557773ecbb71b5fbc34ad68216563a16958",
             "59419815e32311fcd37ac819dc5cc26c02f711a49cb2ca78d713135ff70f4f0b"),
        )
        history = History(DEFAULT_HISTORY)
        transitions = 0
        count = 0
        for submission, first, second in records:
            specs = history.get("submissions", submission)["candidates"]
            assert isinstance(specs, list)
            count += len(specs)
            before, after = history.get("observations", first), history.get("observations", second)
            self.assertEqual(before["submission"], submission)
            self.assertEqual(after["submission"], submission)
            observations = after["reports"]
            assert isinstance(observations, list)
            transitions += sum(change["before"] != change["after"] for change in compare(before, observations))
        self.assertEqual(count, 275)
        self.assertEqual(transitions, 12)

    def test_complete_committed_history_has_no_unreviewed_drift(self) -> None:
        result = recheck_history(History(DEFAULT_HISTORY))
        # The initial campaign must never silently shrink; future candidates may be added.
        count = result["candidates"]
        assert isinstance(count, int)
        self.assertGreaterEqual(count, 275)
        self.assertEqual(result["status"], "unchanged", canonical_json(result))


if __name__ == "__main__":
    unittest.main()
