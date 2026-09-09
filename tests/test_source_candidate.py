"""Preserve old primitives without inventing predictions or globally rejecting extensions."""

from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.archive_existing_primitives import (
    inventory_specifications,
    snapshot_source,
)
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.primitive_screen import Limits, load_json, object_fields
from theory_experiments.source_candidate import (
    SourceSnapshot,
    parse_source_candidate,
    sha256_text,
)


def source_specification() -> dict[str, object]:
    text = "structure ExistingBase where\n  context : Nat\n"
    return {"id": "preserved_base", "family": "source_theory", "role": "primitive_base",
            "components": ["context"], "declared_status": "historical candidate; prediction map open",
            "missing_bridges": ["a quantitative readout map"],
            "sources": [SourceSnapshot("Proofs/ExistingBase.lean", 1, 2, sha256_text(text), text).specification()]}


class SourceCandidateTests(unittest.TestCase):
    def test_source_is_retained_not_executed_or_substituted_for_qm(self) -> None:
        spec = source_specification()
        parsed = parse_source_candidate(spec)
        self.assertEqual(parsed.specification(), spec)
        with (patch.object(pipeline, "evaluate_qm", side_effect=AssertionError("no implicit QM")),
              patch.object(pipeline, "evaluate_sm", side_effect=AssertionError("no implicit SM"))):
            result = pipeline.run_batch([spec], Limits(max_cases=1))[0]
        self.assertEqual(result.report["status"], "unsupported")
        self.assertEqual(result.report["proof_status"], "not_attempted")
        self.assertEqual(result.report["empirical_status"], "not_tested")
        self.assertEqual(object_fields(result.report["scope"])["adapter_status"], "missing")
        checks = result.report["checks"]
        assert isinstance(checks, list)
        self.assertEqual(len(checks), 1)
        self.assertEqual(object_fields(checks[0])["checked"], 0)

    def test_historical_claim_text_cannot_upgrade_the_checker_verdict(self) -> None:
        spec = source_specification()
        spec["declared_status"] = "historically called a complete derivation"
        result = pipeline.run_batch([spec])[0]
        self.assertEqual(result.report["status"], "unsupported")
        self.assertEqual(result.report["proof_status"], "not_attempted")

    def test_history_preserves_unsupported_source_and_reports_missing_adapter(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory))
            spec = source_specification()
            recorded = record_batch([spec], history=history)
            saved = history.get("submissions", recorded.submission)
            self.assertEqual(saved["candidates"], [spec])
            result = recheck_history(history)
        self.assertEqual(result["status"], "unchanged")  # Regression result, not physical success.
        self.assertEqual(result["evaluation_status_counts"], {"unsupported": 1})
        gaps = result["source_adapter_missing"]
        assert isinstance(gaps, list)
        self.assertEqual(object_fields(gaps[0])["id"], "preserved_base")

    def test_snapshot_corruption_paths_and_missing_bridges_are_invalid_not_counterexamples(self) -> None:
        for field, value in (("text", "changed\n"), ("first_line", 0), ("last_line", 99999),
                             ("file_sha256", "fake"), ("text_sha256", "0" * 64),
                             ("path", "../outside.lean"), ("path", "/tmp/code.py")):
            spec = source_specification()
            sources = spec["sources"]
            assert isinstance(sources, list)
            snapshot = object_fields(sources[0])
            snapshot[field] = value
            sources[0] = snapshot
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                pipeline.run_batch([spec])
        for field in ("components", "sources", "missing_bridges"):
            spec = source_specification()
            spec[field] = []
            with self.subTest(field=field), self.assertRaises(ValueError):
                parse_source_candidate(spec)

    def test_capture_is_hash_guarded_and_old_snapshot_survives_source_removal(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Proofs/ExistingBase.lean"
            path.parent.mkdir()
            text = "structure ExistingBase where\n  context : Nat\n"
            path.write_text(text, encoding="utf-8")
            selection: dict[str, object] = {"path": "Proofs/ExistingBase.lean", "first_line": 1,
                                            "last_line": 2, "file_sha256": sha256_text(text)}
            snapshot = snapshot_source(selection, root)
            spec = source_specification()
            spec["sources"] = [snapshot]
            history = History(root / "history")
            record_batch([spec], history=history)
            path.write_text("changed source\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "source changed"):
                snapshot_source(selection, root)
            path.unlink()
            self.assertEqual(recheck_history(history)["status"], "unchanged")

    def test_source_cache_and_fresh_computation_agree(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            cache = Path(directory)
            initial = pipeline.run_batch([source_specification()], cache_dir=cache)[0]
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache hit")):
                reused = pipeline.run_batch([source_specification()], cache_dir=cache)[0]
            fresh = pipeline.run_batch([source_specification()], cache_dir=cache, fresh=True)[0]
        self.assertTrue(reused.reused)
        self.assertEqual(initial.report, reused.report)
        self.assertEqual(initial.report, fresh.report)

    def test_existing_inventory_keeps_incompatible_bases_and_all_law_variants(self) -> None:
        specifications = inventory_specifications()
        rows = {str(object_fields(spec)["id"]): object_fields(spec) for spec in specifications}
        self.assertGreaterEqual(len(rows), 24)
        for name in ("context_first_b0_five", "historical_b0_four", "historical_b0_f_q_action",
                     "historical_b1_f_q", "historical_b1_f_q_a", "historical_b1_f_q_aq",
                     "historical_b1_closed_distinction", "historical_b2_loss_accounting",
                     "historical_b2_qm_sector", "historical_b2_full_scope",
                     "historical_b3_witness_compactness", "zero_base_zb1", "zero_base_zb2",
                     "zero_base_u0", "pair_history_lower_law"):
            self.assertIn(name, rows)
        five, four = rows["context_first_b0_five"]["components"], rows["historical_b0_four"]["components"]
        assert isinstance(five, list) and isinstance(four, list)
        self.assertEqual((len(five), len(four)), (5, 4))
        families = rows["u0_law_family_collection"]["components"]
        assert isinstance(families, list)
        self.assertEqual(len(families), 10)
        self.assertTrue(all("variants 0,1,2,3" in str(family) for family in families))

    def test_neutral_singlets_fail_only_imported_minimal_content_not_anomalies(self) -> None:
        spec = copy.deepcopy(pipeline.controls()["sm_reference"].specification())
        spec["id"] = "sm_neutral_singlet_scope_probe"
        fields = spec["fields"]
        assert isinstance(fields, list)
        fields.append({"label": "neutral_singlet", "color": 1, "weak": 1,
                       "hypercharge": "0", "copies": 3})
        result = pipeline.run_batch([spec])[0]
        checks = result.report["checks"]
        assert isinstance(checks, list)
        failed = [object_fields(check)["id"] for check in checks
                  if object_fields(check)["status"] == "counterexample"]
        self.assertEqual(failed, ["sm_minimal_multiplet_content"])
        self.assertEqual(len(checks), 8)
        self.assertEqual(result.report["rejection_scope"],
                         "candidate_plus_stated_imports_and_selected_requirements")
        self.assertEqual(result.report["empirical_status"], "not_tested")


class RegisteredPrimitiveHistoryTests(unittest.TestCase):
    def test_scope_control_is_retained_as_a_target_mismatch(self) -> None:
        history = History(pipeline.ROOT / "data/candidate_history")
        observation = history.get("observations", "30ed804df4454bf4b6bb36cad6042d4bcae97853e03d2fcdf3db562ad6844e41")
        self.assertEqual(observation["submission"],
                         "3009831c2ea6accd739d05716e2658654f3c596e3dac5fd998bd5853ceb13184")
        reports = observation["reports"]
        assert isinstance(reports, list)
        report = object_fields(reports[0])
        checks = report["checks"]
        assert isinstance(checks, list)
        self.assertEqual([object_fields(check)["id"] for check in checks
                          if object_fields(check)["status"] == "counterexample"],
                         ["sm_minimal_multiplet_content"])

    def test_catalogued_primitives_are_in_durable_history(self) -> None:
        root = pipeline.ROOT / "data/candidate_history"
        registry = object_fields(load_json(pipeline.ROOT / "data/existing_primitive_registration.json"))
        records = registry["records"]
        assert isinstance(records, list)
        saved = {str(object_fields(record)["id"]): object_fields(record) for record in records}
        for spec in inventory_specifications():
            identifier = str(object_fields(spec)["id"])
            entry = saved[identifier]
            submission = entry["submission"]
            observation = entry["observation"]
            assert isinstance(submission, str) and isinstance(observation, str)
            history = History(root)
            self.assertEqual(history.get("submissions", submission)["candidates"], [spec])
            self.assertEqual(history.get("observations", observation)["submission"], submission)
        self.assertEqual(registry["meaning"], "retained_with_missing_prediction_adapters_not_physically_tested")


if __name__ == "__main__":
    unittest.main()
