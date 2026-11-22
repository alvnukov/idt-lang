"""Retain P3 probe snapshots without turning them into physical outcomes."""

from __future__ import annotations

import hashlib
import unittest
from unittest.mock import patch

from scripts.archive_existing_primitives import (
    INVENTORY,
    ROOT,
    inventory_specifications,
)
from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES
from theory_experiments import candidate_pipeline
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.primitive_screen import Limits, load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

PHASE_INVENTORY = ROOT / "data/phase_realization_source_inventory.json"
EARLIER_INVENTORIES = (
    INVENTORY,
    ROOT / "data/primitive_campaign_source_inventory.json",
    ROOT / "data/process_origin_source_inventory.json",
)
PHASE_IDS = {
    "affine_contact_phase_and_pulse_census",
    "relay_full_site_contact_detector",
    "equivariant_swap_root_tag_carriers",
    "vacancy_reference_phase_lift_census",
    "catalytic_restored_stock_phase_transport",
    "conditional_serial_phase_trial_witness",
    "single_end_scalar_charge_and_rivals",
}
PHASE_SOURCES = {f"scripts/probe_{name}.py" for name in (
    "affine_contact_fringe", "affine_pulse_holdouts", "catalytic_six_phase_words",
    "catalytic_tag_invariants", "finite_scalar_channels", "native_phase_contacts",
    "phase_frame_covariance", "serial_trial_witness", "transitive_phase_tags", "vacuum_phase_lifts",
)}


class PhaseRealizationInventoryTests(unittest.TestCase):
    def test_pins_retain_the_original_unassessed_results(self) -> None:
        archive = History(DEFAULT_HISTORY)
        for spec in inventory_specifications(PHASE_INVENTORY):
            record = {"schema": SCHEMA, "candidates": [spec], "limits": Limits().specification()}
            key = candidate_pipeline.digest(record)
            self.assertEqual(archive.get("submissions", key), record)
            reports = archive.baseline(key)["reports"]
            if not isinstance(reports, list) or len(reports) != 1:
                self.fail("expected exactly one pinned report")
            report = object_fields(reports[0])
            self.assertEqual((report["status"], report["proof_status"], report["empirical_status"]),
                             ("unsupported", "not_attempted", "not_tested"))

    def test_ids_and_source_coverage(self) -> None:
        self.assertTrue(PHASE_SOURCES <= {f"scripts/{p}.py" for p in TOPIC_BUNDLES["phase_realization"]})
        candidates = [parse_source_candidate(spec) for spec in inventory_specifications(PHASE_INVENTORY)]
        self.assertCountEqual([candidate.id for candidate in candidates], PHASE_IDS)
        self.assertEqual({source.path for candidate in candidates for source in candidate.sources}, PHASE_SOURCES)
        for inventory in EARLIER_INVENTORIES:
            # Only compare earlier IDs; their archived snapshots are not inputs to this new capture.
            rows = object_fields(load_json(inventory))["candidates"]
            if not isinstance(rows, list):
                self.fail(f"expected candidate rows in {inventory.name}")
            self.assertTrue(PHASE_IDS.isdisjoint(object_fields(row)["id"] for row in rows))

    def test_source_digests_and_inclusive_line_snapshots(self) -> None:
        for spec in inventory_specifications(PHASE_INVENTORY):
            for source in parse_source_candidate(spec).sources:
                with self.subTest(path=source.path, first_line=source.first_line):
                    raw = (ROOT / source.path).read_bytes()
                    selected = b"".join(raw.splitlines(keepends=True)[source.first_line - 1:source.last_line])
                    self.assertEqual(selected, source.text.encode("utf-8"))
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), source.file_sha256)
                    self.assertEqual(hashlib.sha256(selected).hexdigest(), source.specification()["text_sha256"])

    def test_archive_inputs_have_no_executable_prediction_adapter(self) -> None:
        specs = inventory_specifications(PHASE_INVENTORY)
        with (
            patch.object(candidate_pipeline, "evaluate_qm", side_effect=AssertionError("no implicit QM adapter")),
            patch.object(candidate_pipeline, "evaluate_sm", side_effect=AssertionError("no implicit SM adapter")),
        ):
            results = candidate_pipeline.run_batch(specs, fresh=True)
        self.assertEqual(len(results), len(PHASE_IDS))
        for spec, result in zip(specs, results, strict=True):
            candidate = parse_source_candidate(spec)
            with self.subTest(candidate=candidate.id):
                report = result.report
                self.assertEqual((report["status"], report["proof_status"], report["empirical_status"]),
                                 ("unsupported", "not_attempted", "not_tested"))
                scope = object_fields(report["scope"])
                self.assertEqual(scope["scientific_status"], "unassessed")
                self.assertEqual(scope["adapter_status"], "missing")
                self.assertEqual(scope["missing_bridges"], list(candidate.missing_bridges))
                checks = report["checks"]
                if not isinstance(checks, list):
                    self.fail("expected adapter checks")
                self.assertEqual(len(checks), 1)
                check = object_fields(checks[0])
                self.assertEqual((check["id"], check["status"], check["checked"]),
                                 ("primitive_prediction_adapter", "unsupported", 0))


if __name__ == "__main__":
    unittest.main()
