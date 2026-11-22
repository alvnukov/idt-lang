"""Pin process-origin probe inputs without treating them as physical predictions."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.archive_existing_primitives import (
    INVENTORY,
    ROOT,
    inventory_specifications,
    snapshot_source,
)
from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES
from theory_experiments import candidate_pipeline
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.primitive_screen import Limits, load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

PROCESS_INVENTORY = ROOT / "data/process_origin_source_inventory.json"
EARLIER_INVENTORIES = (INVENTORY, ROOT / "data/primitive_campaign_source_inventory.json")
PROCESS_IDS = {
    "alternating_shuttle_boolean_and_relay",
    "six_mark_incidence_and_pair_holdouts",
    "phase_forward_memory_and_comparator",
    "six_phase_occupation_exclusive_packet",
    "occupation_square_curvature_signs",
    "packet_charge_pairing_constraints",
    "conditional_charge_readout_and_flavor_anchors",
}
PROCESS_SOURCES = {f"scripts/probe_{name}.py" for name in (
    "boolean_shuttle_origin",
    "joint_relay_phase",
    "serial_phase_memory",
    "six_mark_phase_origin",
    "phase_pair_holdout",
    "local_phase_comparator",
    "occupation_square_signs",
    "packet_charge_pairings",
    "neutron_charge_anchor",
    "flavor_charge_connectivity",
    "six_phase_exclusive_packet",
)}


class ProcessOriginSourceInventoryTests(unittest.TestCase):
    def test_every_captured_proposal_has_its_original_unassessed_pin(self) -> None:
        archive = History(DEFAULT_HISTORY)
        for spec in inventory_specifications(PROCESS_INVENTORY):
            record = {"schema": SCHEMA, "candidates": [spec], "limits": Limits().specification()}
            key = candidate_pipeline.digest(record)
            self.assertEqual(archive.get("submissions", key), record)
            reports = archive.baseline(key)["reports"]
            if not isinstance(reports, list) or len(reports) != 1:
                self.fail("expected exactly one pinned report")
            report = object_fields(reports[0])
            self.assertEqual((report["status"], report["empirical_status"], report["proof_status"]),
                             ("unsupported", "not_tested", "not_attempted"))

    def test_coverage_and_disjoint_ids(self) -> None:
        candidates = [parse_source_candidate(spec) for spec in inventory_specifications(PROCESS_INVENTORY)]
        self.assertCountEqual([candidate.id for candidate in candidates], PROCESS_IDS)
        self.assertEqual({source.path for candidate in candidates for source in candidate.sources}, PROCESS_SOURCES)
        replayable = {f"scripts/{probe}.py" for topic in ("local_shuttles", "phase_memory", "chiral_observations")
                      for probe in TOPIC_BUNDLES[topic]}
        self.assertTrue(PROCESS_SOURCES <= replayable)
        for inventory in EARLIER_INVENTORIES:
            # The earlier inventories' current working-copy source bytes are not part of this test.
            rows = object_fields(load_json(inventory))["candidates"]
            if not isinstance(rows, list):
                self.fail(f"expected candidate rows in {inventory.name}")
            self.assertTrue(PROCESS_IDS.isdisjoint(object_fields(row)["id"] for row in rows))

    def test_exact_inclusive_line_captures_and_whole_file_guard(self) -> None:
        specifications = inventory_specifications(PROCESS_INVENTORY)
        for spec in specifications:
            for source in parse_source_candidate(spec).sources:
                with self.subTest(path=source.path, first_line=source.first_line):
                    raw = (ROOT / source.path).read_bytes()
                    selected = b"".join(raw.splitlines(keepends=True)[source.first_line - 1:source.last_line])
                    self.assertEqual(selected, source.text.encode("utf-8"))
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), source.file_sha256)
                    self.assertEqual(hashlib.sha256(selected).hexdigest(), source.specification()["text_sha256"])

        source = parse_source_candidate(specifications[0]).sources[0]
        selection = {"path": source.path, "first_line": source.first_line, "last_line": source.last_line,
                     "file_sha256": source.file_sha256}
        raw = (ROOT / source.path).read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            copy = root / source.path
            copy.parent.mkdir()
            copy.write_bytes(raw)
            snapshot = snapshot_source(selection, root)
            self.assertEqual(snapshot, source.specification())
            copy.write_bytes(raw + b"\n# outside the captured span\n")
            with self.assertRaisesRegex(ValueError, "source changed"):
                snapshot_source(selection, root)
            copy.unlink()
            self.assertEqual(parse_source_candidate(specifications[0]).sources[0].specification(), snapshot)

    def test_interpreter_retains_sources_without_physical_evaluation(self) -> None:
        specifications = inventory_specifications(PROCESS_INVENTORY)
        with (
            patch.object(candidate_pipeline, "evaluate_qm", side_effect=AssertionError("no implicit QM adapter")),
            patch.object(candidate_pipeline, "evaluate_sm", side_effect=AssertionError("no implicit SM adapter")),
        ):
            results = candidate_pipeline.run_batch(specifications, fresh=True)
        self.assertEqual(len(results), len(PROCESS_IDS))
        for spec, result in zip(specifications, results, strict=True):
            candidate = parse_source_candidate(spec)
            with self.subTest(candidate=candidate.id):
                self.assertEqual(result.report["status"], "unsupported")
                self.assertEqual(result.report["proof_status"], "not_attempted")
                self.assertEqual(result.report["empirical_status"], "not_tested")
                scope = object_fields(result.report["scope"])
                self.assertEqual(scope["scientific_status"], "unassessed")
                self.assertEqual(scope["adapter_status"], "missing")
                self.assertEqual(scope["missing_bridges"], list(candidate.missing_bridges))
                checks = result.report["checks"]
                if not isinstance(checks, list):
                    self.fail("expected adapter checks")
                self.assertEqual(len(checks), 1)
                check = object_fields(checks[0])
                self.assertEqual((check["id"], check["status"], check["checked"]),
                                 ("primitive_prediction_adapter", "unsupported", 0))


if __name__ == "__main__":
    unittest.main()
