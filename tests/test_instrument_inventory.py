"""Check retained instrument sources without treating them as physical predictions."""

from __future__ import annotations

import hashlib
import unittest
from unittest.mock import patch

from scripts.archive_existing_primitives import (
    ROOT,
    inventory_specifications,
)
from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES
from theory_experiments import candidate_pipeline
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.primitive_screen import Limits, load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

INVENTORY = ROOT / "data/instrument_source_inventory.json"
IDS = {
    "affine_memory_contact_records",
    "strictly_alternating_catalyst_clock",
    "affine_mixture_equivalence_libraries",
    "affine_fourth_axis_scope_and_escapes",
    "affine_sequential_reset_walls",
    "midpoint_spectator_ternary_instrument",
}
SOURCES = {f"scripts/probe_{name}.py" for name in (
    "affine_contact_record", "full_affine_record", "affine_preparation_mixtures",
    "affine_fourth_axis", "affine_unread_instruments", "affine_projective_reset",
    "affine_operational_library", "alternating_catalyst_clock", "midpoint_spectator_instrument",
    "midpoint_rule_origins",
)}
EARLIER_INVENTORIES = (
    "existing_primitive_inventory.json",
    "primitive_campaign_source_inventory.json",
    "process_origin_source_inventory.json",
    "phase_realization_source_inventory.json",
    "primitive_relational_endpoint_inventory.json",
    "primitive_opposition_spatial_inventory.json",
    "primitive_signal_relay_inventory.json",
    "primitive_operational_routes_inventory.json",
)


class InstrumentInventoryTests(unittest.TestCase):
    def test_immutable_instrument_baselines_are_unassessed(self) -> None:
        archive = History(DEFAULT_HISTORY)
        for spec in inventory_specifications(INVENTORY):
            record = {"schema": SCHEMA, "candidates": [spec], "limits": Limits().specification()}
            key = candidate_pipeline.digest(record)
            self.assertEqual(archive.get("submissions", key), record)
            reports = archive.baseline(key)["reports"]
            if not isinstance(reports, list) or len(reports) != 1:
                self.fail("exactly one original unassessed baseline required")
            r = object_fields(reports[0])
            self.assertEqual((r["status"], r["proof_status"], r["empirical_status"]),
                             ("unsupported", "not_attempted", "not_tested"))

    def test_ids_source_coverage_and_campaign_registration(self) -> None:
        self.assertTrue(SOURCES <= {f"scripts/{probe}.py" for probe in TOPIC_BUNDLES["instrument_realization"]})
        candidates = [parse_source_candidate(spec) for spec in inventory_specifications(INVENTORY)]
        self.assertCountEqual([candidate.id for candidate in candidates], IDS)
        self.assertEqual({source.path for candidate in candidates for source in candidate.sources}, SOURCES)
        for name in EARLIER_INVENTORIES:
            rows = object_fields(load_json(ROOT / "data" / name))["candidates"]
            if not isinstance(rows, list):
                self.fail(f"expected candidate rows in {name}")
            self.assertTrue(IDS.isdisjoint(object_fields(row)["id"] for row in rows))

    def test_captures_match_the_pinned_source_and_inclusive_lines(self) -> None:
        for spec in inventory_specifications(INVENTORY):
            for source in parse_source_candidate(spec).sources:
                with self.subTest(path=source.path, first_line=source.first_line):
                    raw = (ROOT / source.path).read_bytes()
                    excerpt = b"".join(raw.splitlines(keepends=True)[source.first_line - 1:source.last_line])
                    self.assertEqual(excerpt, source.text.encode("utf-8"))
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), source.file_sha256)
                    self.assertEqual(hashlib.sha256(excerpt).hexdigest(), source.specification()["text_sha256"])

    def test_retained_inputs_do_not_run_a_physical_adapter(self) -> None:
        specs = inventory_specifications(INVENTORY)
        with (
            patch.object(candidate_pipeline, "evaluate_qm", side_effect=AssertionError("no implicit QM adapter")),
            patch.object(candidate_pipeline, "evaluate_sm", side_effect=AssertionError("no implicit SM adapter")),
        ):
            results = candidate_pipeline.run_batch(specs, fresh=True)
        self.assertEqual(len(results), len(IDS))
        for spec, result in zip(specs, results, strict=True):
            candidate = parse_source_candidate(spec)
            with self.subTest(candidate=candidate.id):
                report = result.report
                self.assertEqual((report["status"], report["proof_status"], report["empirical_status"]),
                                 ("unsupported", "not_attempted", "not_tested"))
                scope = object_fields(report["scope"])
                self.assertEqual((scope["adapter_status"], scope["scientific_status"]), ("missing", "unassessed"))
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
