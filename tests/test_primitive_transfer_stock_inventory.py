"""Source retention of transfer/stock probes is not a prediction adapter."""

from __future__ import annotations

import hashlib
import unittest
from unittest.mock import patch

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from theory_experiments import candidate_pipeline
from theory_experiments.primitive_screen import load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

INVENTORY = ROOT / "data/primitive_transfer_stock_inventory.json"
IDS = {
    "unsigned_transfer_triangle_endpoint_realization",
    "bipartite_triangle_incidence_origin",
    "whole_triangle_stock_rigidity_and_bypass_discriminators",
    "native_coherent_partial_data_exchange",
    "prospective_all_herald_reference_sewing_trials",
}
SOURCES = {f"scripts/probe_{name}.py" for name in (
    "unsigned_transfer_triangle", "bipartite_triangle_origin",
    "triangle_stock_rigidity", "triangle_bypass_normalization",
    "native_partial_exchange", "reference_sewing_trials",
)}


class PrimitiveTransferStockInventoryTests(unittest.TestCase):
    def test_unique_ids_and_exact_campaign_sources(self) -> None:
        from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES

        bundled = {f"scripts/{probe}.py" for probe in TOPIC_BUNDLES["transfer_stock_and_trials"]}
        self.assertEqual(SOURCES, bundled)
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

    def test_actual_source_bytes_full_digests_and_bounded_excerpts(self) -> None:
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

    def test_source_proposals_remain_unassessed_without_prediction_adapters(self) -> None:
        specs = inventory_specifications(INVENTORY)
        with (
            patch.object(candidate_pipeline, "evaluate_qm", side_effect=AssertionError("no implicit QM adapter")),
            patch.object(candidate_pipeline, "evaluate_sm", side_effect=AssertionError("no implicit SM adapter")),
            patch.object(candidate_pipeline, "evaluate_triangle_stock", side_effect=AssertionError("no implicit stock adapter")),
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
