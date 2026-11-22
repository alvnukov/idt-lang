"""Check that campaign proposals are retained as source, not physical results."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.archive_existing_primitives import (
    INVENTORY,
    ROOT,
    inventory_specifications,
    snapshot_source,
)
from theory_experiments.candidate_history import History, recheck_history, record_batch
from theory_experiments.primitive_screen import load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

CAMPAIGN_INVENTORY = ROOT / "data/primitive_campaign_source_inventory.json"
CAMPAIGN_IDS = {
    "rank_two_transparent_signed_exchange",
    "ranked_pair_event_routing",
    "persistent_rotor_event_supply",
    "alternative_prepared_readouts",
    "commuting_noncommuting_phase_carriers",
    "copy_record_erasure_proposals",
    "signed_exterior_slots_charge",
    "local_transport_species_cones",
    "unread_gap_collision_sampler",
}


class PrimitiveCampaignSourceInventoryTests(unittest.TestCase):
    def test_campaign_ids_are_complete_unique_and_disjoint_from_historical_inventory(self) -> None:
        campaign_ids = [parse_source_candidate(spec).id for spec in inventory_specifications(CAMPAIGN_INVENTORY)]
        self.assertCountEqual(campaign_ids, CAMPAIGN_IDS)

        # Compare only the identifiers. Historical source snapshots live in history;
        # their inventory need not describe the current working copies of those files.
        earlier_rows = object_fields(load_json(INVENTORY))["candidates"]
        if not isinstance(earlier_rows, list):
            self.fail("historical inventory candidates must be a list")
        earlier_ids = {object_fields(row)["id"] for row in earlier_rows}
        self.assertTrue(CAMPAIGN_IDS.isdisjoint(earlier_ids))

    def test_each_capture_matches_exact_source_bytes_and_inclusive_lines(self) -> None:
        for spec in inventory_specifications(CAMPAIGN_INVENTORY):
            candidate = parse_source_candidate(spec)
            for source in candidate.sources:
                with self.subTest(candidate=candidate.id, path=source.path, first_line=source.first_line):
                    raw = (ROOT / source.path).read_bytes()
                    lines = raw.decode("utf-8").splitlines(keepends=True)
                    self.assertEqual(source.file_sha256, hashlib.sha256(raw).hexdigest())
                    self.assertEqual(source.text, "".join(lines[source.first_line - 1:source.last_line]))
                    self.assertEqual(source.specification()["text_sha256"],
                                     hashlib.sha256(source.text.encode("utf-8")).hexdigest())

    def test_archived_captures_survive_source_changes_without_claiming_physical_results(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            specifications = inventory_specifications(CAMPAIGN_INVENTORY)
            history = History(root / "history")
            for spec in specifications:
                candidate = parse_source_candidate(spec)
                with self.subTest(candidate=candidate.id):
                    recorded = record_batch([spec], history=history, fresh=True)
                    self.assertEqual(history.get("submissions", recorded.submission)["candidates"], [spec])
                    report = recorded.results[0].report
                    self.assertEqual(report["status"], "unsupported")
                    self.assertEqual(report["proof_status"], "not_attempted")
                    self.assertEqual(report["empirical_status"], "not_tested")
                    scope = object_fields(report["scope"])
                    self.assertEqual(scope["adapter_status"], "missing")
                    self.assertEqual(scope["scientific_status"], "unassessed")
                    self.assertEqual(scope["missing_bridges"], list(candidate.missing_bridges))
                    checks = report["checks"]
                    if not isinstance(checks, list):
                        self.fail("expected a list of adapter checks")
                    self.assertEqual(len(checks), 1)
                    check = object_fields(checks[0])
                    self.assertEqual((check["id"], check["status"], check["checked"]),
                                     ("primitive_prediction_adapter", "unsupported", 0))

            original = parse_source_candidate(specifications[0]).sources[0]
            selection = {"path": original.path, "first_line": original.first_line, "last_line": original.last_line,
                         "file_sha256": original.file_sha256}
            copied_source = root / original.path
            copied_source.parent.mkdir()
            copied_source.write_bytes((ROOT / original.path).read_bytes())
            self.assertEqual(snapshot_source(selection, root), original.specification())
            # A change outside the selected span must also invalidate a new capture.
            with copied_source.open("ab") as target:
                target.write(b"\noutside retained lines\n")
            with self.assertRaisesRegex(ValueError, "source changed"):
                snapshot_source(selection, root)
            copied_source.unlink()

            replayed = recheck_history(history)
            self.assertEqual(replayed["status"], "unchanged")
            self.assertEqual(replayed["evaluation_status_counts"], {"unsupported": len(CAMPAIGN_IDS)})


if __name__ == "__main__":
    unittest.main()
