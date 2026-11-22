"""Retain reference, pulse and carrier probes without prediction upgrades."""

from __future__ import annotations

import hashlib
import unittest
from unittest.mock import patch

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from theory_experiments import candidate_pipeline
from theory_experiments.primitive_screen import load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

INVENTORY = ROOT / "data/primitive_reference_transport_inventory.json"
IDS = {
    "triangle_joint_cycle_operational_phase_axis",
    "independent_triangle_package_sewing_efficiency_wall",
    "native_reference_fanout_and_prior_contact_preparation",
    "coherent_triangle_pulses_and_conditional_rotation_closure",
    "sparse_chiral_support_census_and_anonymous_carrier",
    "anonymous_relational_chart_return_holonomy",
}
SOURCES = {f"scripts/probe_{name}.py" for name in (
    "triangle_cycle_phase_axis", "triangle_reference_sewing",
    "native_triangle_reference_fanout", "prior_triangle_reference",
    "coherent_triangle_pulses", "sparse_chiral_supports",
    "anonymous_punctured_carrier", "relational_chart_holonomy",
)}


class PrimitiveReferenceTransportInventoryTests(unittest.TestCase):
    def test_unique_ids_and_exact_source_coverage(self) -> None:
        from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES

        bundled = {f"scripts/{probe}.py" for probe in TOPIC_BUNDLES["reference_transport_and_carriers"]}
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

    def test_exact_source_bytes_full_hashes_and_bounded_inclusive_excerpts(self) -> None:
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

    def test_source_retention_has_no_implicit_prediction_adapter(self) -> None:
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
