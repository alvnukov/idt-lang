"""Operational-route archives retain source evidence, not physical verdicts."""

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
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    History,
    recheck_history,
    record_batch,
)
from theory_experiments.primitive_screen import load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate

ROUTES_INVENTORY = ROOT / "data/primitive_operational_routes_inventory.json"
CAMPAIGN_INVENTORY = ROOT / "data/primitive_campaign_source_inventory.json"
ROUTE_SOURCES = {
    "unsigned_four_label_neutral_contrast": {"probe_unsigned_neutral_motifs"},
    "uncolored_cycle_graph_abelianized_carrier": {"probe_uncolored_cycle_carrier"},
    "unsigned_complement_packets_asynchronous_resolution": {
        "probe_asynchronous_pair_resolver",
        "probe_unsigned_background_readout",
    },
    "aligned_raw_family_ckm_hidden_spares": {
        "probe_ckm_raw_family_wall",
        "probe_ckm_blank_ports",
    },
    "coherent_duplicate_detector_row_density": {
        "probe_unread_row_duplication",
        "probe_native_row_probability",
    },
    "native_frames_heralded_rational_instruments": {
        "probe_native_qutrit_frames",
        "probe_native_rational_pentagon",
    },
    "balanced_phase_independent_source_composition": {
        "probe_balanced_phase_composition",
    },
    "autonomous_orthogonal_program_collision": {"probe_autonomous_mixer_program"},
}


class PrimitiveOperationalRoutesInventoryTests(unittest.TestCase):
    def check_unsupported(self, report: dict[str, object]) -> None:
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(report["proof_status"], "not_attempted")
        self.assertEqual(report["empirical_status"], "not_tested")
        scope = object_fields(report["scope"])
        self.assertEqual(scope["adapter_status"], "missing")
        self.assertEqual(scope["scientific_status"], "unassessed")
        checks = report["checks"]
        if not isinstance(checks, list):
            self.fail("expected an array of adapter checks")
        self.assertEqual(len(checks), 1)
        check = object_fields(checks[0])
        self.assertEqual(
            (check["id"], check["status"], check["checked"]),
            ("primitive_prediction_adapter", "unsupported", 0),
        )

    def test_eight_distinct_ids_do_not_replace_earlier_proposals(self) -> None:
        specs = inventory_specifications(ROUTES_INVENTORY)
        identifiers = [parse_source_candidate(spec).id for spec in specs]
        self.assertCountEqual(identifiers, ROUTE_SOURCES)
        self.assertEqual(len(set(identifiers)), 8)
        for earlier_inventory in (INVENTORY, CAMPAIGN_INVENTORY):
            # Historical inventories need not match today's working source files.
            rows = object_fields(load_json(earlier_inventory))["candidates"]
            if not isinstance(rows, list):
                self.fail("historical candidates must be an array")
            earlier_ids = {object_fields(row)["id"] for row in rows}
            self.assertTrue(set(identifiers).isdisjoint(earlier_ids))

    def test_only_short_exact_frozen_module_spans_are_captured(self) -> None:
        all_paths: set[str] = set()
        for spec in inventory_specifications(ROUTES_INVENTORY):
            candidate = parse_source_candidate(spec)
            self.assertEqual(candidate.role, "route")
            self.assertGreaterEqual(len(candidate.missing_bridges), 3)
            expected = {f"scripts/{name}.py" for name in ROUTE_SOURCES[candidate.id]}
            self.assertEqual({source.path for source in candidate.sources}, expected)
            for source in candidate.sources:
                with self.subTest(id=candidate.id, path=source.path, line=source.first_line):
                    all_paths.add(source.path)
                    self.assertLessEqual(source.last_line - source.first_line + 1, 40)
                    raw = (ROOT / source.path).read_bytes()
                    lines = raw.decode("utf-8").splitlines(keepends=True)
                    self.assertEqual(source.file_sha256, hashlib.sha256(raw).hexdigest())
                    self.assertEqual(
                        source.text,
                        "".join(lines[source.first_line - 1 : source.last_line]),
                    )
                    self.assertEqual(
                        source.specification()["text_sha256"],
                        hashlib.sha256(source.text.encode("utf-8")).hexdigest(),
                    )
        self.assertEqual(len(all_paths), 12)

    def test_each_route_keeps_its_missing_bridges_and_unsupported_adapter(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            for spec in inventory_specifications(ROUTES_INVENTORY):
                candidate = parse_source_candidate(spec)
                with self.subTest(id=candidate.id):
                    run = record_batch([spec], history=history, fresh=True)
                    self.assertFalse(run.changes)
                    self.assertEqual(
                        history.get("submissions", run.submission)["candidates"], [spec]
                    )
                    report = run.results[0].report
                    self.check_unsupported(report)
                    self.assertEqual(
                        object_fields(report["scope"])["missing_bridges"],
                        list(candidate.missing_bridges),
                    )
                    request = object_fields(report["request"])
                    self.assertEqual(request["candidate"], spec)

    def test_retained_submissions_are_bijective_to_this_inventory(self) -> None:
        expected = {
            parse_source_candidate(spec).id: spec
            for spec in inventory_specifications(ROUTES_INVENTORY)
        }
        history = History(DEFAULT_HISTORY)
        seen: list[str] = []
        for path in sorted((DEFAULT_HISTORY / "submissions").glob("*.json")):
            submission = history.get("submissions", path.stem)
            rows = submission["candidates"]
            if not isinstance(rows, list):
                self.fail("submitted candidates must be an array")
            for spec in rows:
                identifier = object_fields(spec)["id"]
                if not isinstance(identifier, str) or identifier not in expected:
                    continue
                with self.subTest(id=identifier):
                    seen.append(identifier)
                    self.assertEqual(rows, [expected[identifier]])
                    baseline = history.baseline(path.stem)
                    self.assertEqual(baseline["submission"], path.stem)
                    reports = baseline["reports"]
                    if not isinstance(reports, list):
                        self.fail("baseline reports must be an array")
                    self.assertEqual(len(reports), 1)
                    report = object_fields(reports[0])
                    self.check_unsupported(report)
                    self.assertEqual(
                        object_fields(report["request"])["candidate"], expected[identifier]
                    )
        self.assertCountEqual(seen, expected)

    def test_snapshots_replay_after_source_changes_and_removal(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            specs = inventory_specifications(ROUTES_INVENTORY)
            selections = object_fields(load_json(ROUTES_INVENTORY))["candidates"]
            if not isinstance(selections, list):
                self.fail("inventory candidates must be an array")
            sources = object_fields(selections[0])["sources"]
            if not isinstance(sources, list):
                self.fail("inventory sources must be an array")
            original = parse_source_candidate(specs[0]).sources[0]
            copied_source = root / original.path
            copied_source.parent.mkdir()
            copied_source.write_bytes((ROOT / original.path).read_bytes())
            self.assertEqual(snapshot_source(sources[0], root), original.specification())

            history = History(root / "history")
            for spec in specs:
                record_batch([spec], history=history, fresh=True)
            # Full-file pinning detects mutations even outside selected source lines.
            with copied_source.open("ab") as target:
                target.write(b"\noutside archived span\n")
            with self.assertRaisesRegex(ValueError, "source changed"):
                snapshot_source(sources[0], root)
            copied_source.unlink()

            replay = recheck_history(history)
            self.assertEqual(replay["status"], "unchanged")
            self.assertEqual(replay["submissions"], 8)
            self.assertEqual(replay["evaluation_status_counts"], {"unsupported": 8})
            self.assertEqual(replay["changes"], [])
            self.assertEqual(replay["errors"], [])


if __name__ == "__main__":
    unittest.main()
