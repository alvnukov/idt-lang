"""Operational identifiability probes remain unsupported source proposals."""

from __future__ import annotations

import hashlib
import unittest
from unittest.mock import patch

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from theory_experiments import candidate_pipeline
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.primitive_screen import Limits, load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

INVENTORY = ROOT / "data/primitive_identifiability_inventory.json"
SOURCES = {
    "boundary_ray_and_graph_distance_aliases": "scripts/probe_boundary_geometry_aliases.py",
    "three_packet_exchange_sector_discriminators": "scripts/probe_three_packet_exchange_sector.py",
    "connected_contact_tomography_scope": "scripts/probe_connected_contact_tomography.py",
    "hidden_orthogonal_exchange_label_countermodel": "scripts/probe_hidden_exchange_colors.py",
    "partial_hidden_overlap_exchange_visibility": "scripts/probe_partial_hidden_exchange.py",
}


class PrimitiveIdentifiabilityInventoryTests(unittest.TestCase):
    def test_each_submission_keeps_its_original_unassessed_report(self) -> None:
        archive = History(DEFAULT_HISTORY)
        for spec in inventory_specifications(INVENTORY):
            request = {"schema": SCHEMA, "limits": Limits().specification(), "candidates": [spec]}
            key = candidate_pipeline.digest(request)
            with self.subTest(candidate=object_fields(spec)["id"]):
                self.assertEqual(request, archive.get("submissions", key))
                rows = archive.baseline(key)["reports"]
                if not isinstance(rows, list) or len(rows) != 1:
                    self.fail("expected the original source report")
                report = object_fields(rows[0])
                self.assertEqual((report["status"], report["proof_status"], report["empirical_status"]),
                                 ("unsupported", "not_attempted", "not_tested"))

    def test_unique_ids_and_exact_campaign_sources(self) -> None:
        from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES

        expected_paths = list(SOURCES.values())
        bundled = [f"scripts/{probe}.py" for probe in TOPIC_BUNDLES["operational_identifiability"]]
        self.assertCountEqual(bundled, expected_paths)
        candidates = [parse_source_candidate(spec) for spec in inventory_specifications(INVENTORY)]
        self.assertCountEqual([candidate.id for candidate in candidates], SOURCES)
        for candidate in candidates:
            self.assertEqual({src.path for src in candidate.sources}, {SOURCES[candidate.id]})
        for inventory in sorted((ROOT / "data").glob("*inventory.json")):
            if inventory != INVENTORY:
                rows = object_fields(load_json(inventory))["candidates"]
                if not isinstance(rows, list):
                    self.fail(f"expected candidate rows in {inventory.name}")
                self.assertTrue(set(SOURCES).isdisjoint(object_fields(row)["id"] for row in rows))

    def test_exact_source_bytes_full_digests_and_bounded_excerpts(self) -> None:
        for spec in inventory_specifications(INVENTORY):
            for source in parse_source_candidate(spec).sources:
                with self.subTest(path=source.path, first_line=source.first_line):
                    raw = (ROOT / source.path).read_bytes()
                    lines = raw.splitlines(keepends=True)
                    self.assertLessEqual(source.last_line, len(lines))
                    excerpt = b"".join(lines[source.first_line - 1:source.last_line])
                    self.assertEqual(excerpt, source.text.encode("utf-8"))
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), source.file_sha256)
                    self.assertEqual(hashlib.sha256(excerpt).hexdigest(), source.specification()["text_sha256"])
                    self.assertLessEqual(len(excerpt), 16384)

    def test_source_retention_does_not_upgrade_or_bind_prediction_checkers(self) -> None:
        specs = inventory_specifications(INVENTORY)
        with (
            patch.object(candidate_pipeline, "evaluate_qm", side_effect=AssertionError("no implicit QM adapter")),
            patch.object(candidate_pipeline, "evaluate_sm", side_effect=AssertionError("no implicit SM adapter")),
            patch.object(candidate_pipeline, "evaluate_triangle_stock", side_effect=AssertionError("no implicit stock adapter")),
            patch.object(candidate_pipeline, "evaluate_neutral_current_width", side_effect=AssertionError("no implicit width adapter")),
        ):
            results = candidate_pipeline.run_batch(specs, fresh=True)
        self.assertEqual(len(results), len(SOURCES))
        for spec, result in zip(specs, results, strict=True):
            candidate = parse_source_candidate(spec)
            with self.subTest(candidate=candidate.id):
                self.assertEqual(object_fields(spec)["family"], "source_theory")
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
