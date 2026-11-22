"""Retain contact/comparator probes as source, never physical predictions."""

from __future__ import annotations

import hashlib
import unittest
from unittest.mock import patch

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from theory_experiments import candidate_pipeline
from theory_experiments.primitive_screen import load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

INVENTORY = ROOT / "data/primitive_contacts_comparators_inventory.json"
IDS = {
    "triangle_signed_exchange_and_heralded_factory",
    "signed_history_same_cloud_join",
    "independent_raw_phase_comparator_wall",
    "autonomous_anonymous_midpoint_symmetry_ceiling",
    "nonzero_weighted_chiral_pencil_diagonal_classification",
    "active_local_angular_rulers_and_transport",
}
SOURCES = {f"scripts/probe_{name}.py" for name in (
    "triangle_exchange_source", "heralded_triangle_factory",
    "signed_phase_join", "independent_phase_comparator", "autonomous_midpoint_repair",
    "weighted_chiral_pencil", "local_angular_rulers",
)}


class PrimitiveContactsComparatorsInventoryTests(unittest.TestCase):
    def test_ids_and_source_coverage(self) -> None:
        from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES

        bundled = {f"scripts/{probe}.py" for probe in TOPIC_BUNDLES["primitive_contacts_and_comparators"]}
        self.assertTrue(SOURCES <= bundled)
        candidates = [parse_source_candidate(spec) for spec in inventory_specifications(INVENTORY)]
        self.assertCountEqual([candidate.id for candidate in candidates], IDS)
        self.assertEqual({source.path for candidate in candidates for source in candidate.sources}, SOURCES)
        for inventory in sorted((ROOT / "data").glob("*inventory.json")):
            if inventory == INVENTORY:
                continue
            rows = object_fields(load_json(inventory))["candidates"]
            if not isinstance(rows, list):
                self.fail(f"expected candidate rows in {inventory.name}")
            self.assertTrue(IDS.isdisjoint(object_fields(row)["id"] for row in rows))

    def test_captures_match_exact_hashes_and_inclusive_lines(self) -> None:
        for spec in inventory_specifications(INVENTORY):
            for source in parse_source_candidate(spec).sources:
                with self.subTest(path=source.path, first_line=source.first_line):
                    raw = (ROOT / source.path).read_bytes()
                    excerpt = b"".join(raw.splitlines(keepends=True)[source.first_line - 1:source.last_line])
                    self.assertEqual(excerpt, source.text.encode("utf-8"))
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), source.file_sha256)
                    self.assertEqual(hashlib.sha256(excerpt).hexdigest(), source.specification()["text_sha256"])
                    self.assertLessEqual(len(excerpt), 16384)

    def test_retained_sources_have_no_implicit_prediction_adapter(self) -> None:
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
