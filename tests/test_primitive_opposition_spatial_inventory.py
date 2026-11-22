"""Frozen opposition/spatial sources remain unsupported, not physical verdicts."""

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

SPATIAL_INVENTORY = ROOT / "data/primitive_opposition_spatial_inventory.json"
EARLIER_INVENTORIES = (
    INVENTORY,
    ROOT / "data/primitive_campaign_source_inventory.json",
    ROOT / "data/primitive_operational_routes_inventory.json",
)
SOURCE_FAMILIES = {
    "three_opposition_sheet_clock_active_readout": {"probe_three_opposition_origin", "probe_opposition_clock_scatter", "probe_opposition_readout"},
    "matching_echo_natural_root_selector": {"probe_matching_echo_selector", "probe_matching_transport"},
    "cube_parity_capacity_readout_alternatives": {"probe_erased_bit_readouts", "probe_parity_capacity"},
    "six_packet_matter_exterior_carrier_cubic_rival": {"probe_six_packet_sectors", "probe_six_packet_matter", "probe_packet_exchange_transport"},
    "heralded_rus_sector_phase_resource": {"probe_heralded_sector_phase"},
    "neutral_two_state_referenced_phase_wall": {"probe_neutral_phase_controller"},
    "irrational_catalytic_phase_finite_seed": {"probe_catalytic_sector_phase"},
    "neutral_three_state_approximate_phase_controller": {"probe_three_state_phase_controller"},
    "trusted_three_axis_independent_source_parity": {"probe_three_axis_source_parity"},
    "native_multiphoton_hidden_exchange_cycles": {"probe_packet_triad_phase", "probe_packet_exchange_cycles"},
    "collision_spatial_modes_free_pair_light": {"probe_diamond_collision_walk", "probe_routed_diamond_cones", "probe_collision_light_pair"},
    "oriented_cell_reciprocal_wave_primitive": {"probe_oriented_cell_wave"},
    "weak_gravity_collision_clock_rod_bridge": {"probe_collision_clock_gravity"},
    "opposition_clock_path_memory_spin_lifts": {"probe_opposition_spin_lift"},
}


class PrimitiveOppositionSpatialInventoryTests(unittest.TestCase):
    def check_unsupported(self, report: dict[str, object]) -> None:
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(report["proof_status"], "not_attempted")
        self.assertEqual(report["empirical_status"], "not_tested")
        scope = object_fields(report["scope"])
        self.assertEqual(scope["adapter_status"], "missing")
        self.assertEqual(scope["scientific_status"], "unassessed")
        self.assertEqual(
            scope["source_boundary"],
            "snapshots_are_retained_input_not_executed_code_or_checked_proof",
        )
        checks = report["checks"]
        if not isinstance(checks, list):
            self.fail("adapter checks must be an array")
        self.assertEqual(len(checks), 1)
        check = object_fields(checks[0])
        self.assertEqual(
            (check["id"], check["status"], check["checked"]),
            ("primitive_prediction_adapter", "unsupported", 0),
        )

    def test_fourteen_distinct_ids_preserve_earlier_candidates(self) -> None:
        identifiers = [
            parse_source_candidate(spec).id
            for spec in inventory_specifications(SPATIAL_INVENTORY)
        ]
        self.assertCountEqual(identifiers, SOURCE_FAMILIES)
        self.assertEqual(len(set(identifiers)), 14)
        for inventory in EARLIER_INVENTORIES:
            # Earlier sources may have changed; compare retained proposal IDs only.
            rows = object_fields(load_json(inventory))["candidates"]
            if not isinstance(rows, list):
                self.fail("inventory candidates must be an array")
            earlier_ids = {object_fields(row)["id"] for row in rows}
            self.assertTrue(set(identifiers).isdisjoint(earlier_ids))

    def test_only_bounded_exact_frozen_research_modules_are_captured(self) -> None:
        all_paths: set[str] = set()
        snapshots = 0
        for spec in inventory_specifications(SPATIAL_INVENTORY):
            candidate = parse_source_candidate(spec)
            self.assertEqual(object_fields(spec)["family"], "source_theory")
            self.assertEqual(candidate.role, "route")
            self.assertGreaterEqual(len(candidate.missing_bridges), 4)
            self.assertEqual(
                {source.path for source in candidate.sources},
                {f"scripts/{name}.py" for name in SOURCE_FAMILIES[candidate.id]},
            )
            for source in candidate.sources:
                with self.subTest(id=candidate.id, path=source.path, line=source.first_line):
                    snapshots += 1
                    all_paths.add(source.path)
                    self.assertLessEqual(source.last_line - source.first_line + 1, 40)
                    self.assertLessEqual(len(source.text.encode("utf-8")), 8192)
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
        self.assertEqual(len(all_paths), 23)
        self.assertEqual(snapshots, 44)

    def test_fresh_and_repeat_reports_stay_unsupported_with_exact_bridges(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            for spec in inventory_specifications(SPATIAL_INVENTORY):
                candidate = parse_source_candidate(spec)
                with self.subTest(id=candidate.id):
                    first = record_batch([spec], history=history, fresh=True)
                    second = record_batch([spec], history=history, fresh=True)
                    self.assertFalse(first.changes)
                    self.assertFalse(second.changes)
                    self.assertEqual(first.submission, second.submission)
                    self.assertEqual(first.observation, second.observation)
                    self.assertEqual(
                        history.get("submissions", first.submission)["candidates"], [spec]
                    )
                    for run in (first, second):
                        report = run.results[0].report
                        self.check_unsupported(report)
                        self.assertEqual(
                            object_fields(report["scope"])["missing_bridges"],
                            list(candidate.missing_bridges),
                        )
                        self.assertEqual(
                            object_fields(report["request"])["candidate"], spec
                        )
            replay = recheck_history(history)
            self.assertEqual(replay["status"], "unchanged")
            self.assertEqual(replay["submissions"], 14)
            self.assertEqual(replay["evaluation_status_counts"], {"unsupported": 14})
            self.assertEqual(replay["changes"], [])
            self.assertEqual(replay["errors"], [])

    def test_canonical_submissions_are_bijective_and_not_operational_adapters(self) -> None:
        expected = {
            parse_source_candidate(spec).id: spec
            for spec in inventory_specifications(SPATIAL_INVENTORY)
        }
        history = History(DEFAULT_HISTORY)
        seen: list[str] = []
        for path in sorted((DEFAULT_HISTORY / "submissions").glob("*.json")):
            rows = history.get("submissions", path.stem)["candidates"]
            if not isinstance(rows, list):
                self.fail("submitted candidates must be an array")
            for spec in rows:
                identifier = object_fields(spec)["id"]
                if not isinstance(identifier, str) or identifier not in expected:
                    continue
                with self.subTest(id=identifier):
                    seen.append(identifier)
                    self.assertEqual(rows, [expected[identifier]])
                    self.assertEqual(object_fields(spec)["family"], "source_theory")
                    baseline = history.baseline(path.stem)
                    self.assertEqual(baseline["submission"], path.stem)
                    reports = baseline["reports"]
                    if not isinstance(reports, list):
                        self.fail("baseline reports must be an array")
                    self.assertEqual(len(reports), 1)
                    report = object_fields(reports[0])
                    self.check_unsupported(report)
                    self.assertEqual(
                        object_fields(report["request"])["candidate"],
                        expected[identifier],
                    )
        self.assertCountEqual(seen, expected)

    def test_all_full_file_pins_reject_changes_outside_selected_spans(self) -> None:
        rows = object_fields(load_json(SPATIAL_INVENTORY))["candidates"]
        if not isinstance(rows, list):
            self.fail("inventory candidates must be an array")
        selections: dict[str, object] = {}
        for row in rows:
            sources = object_fields(row)["sources"]
            if not isinstance(sources, list):
                self.fail("inventory sources must be an array")
            for source in sources:
                selections.setdefault(str(object_fields(source)["path"]), source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative, selection in selections.items():
                with self.subTest(path=relative):
                    copy = root / relative
                    copy.parent.mkdir(parents=True, exist_ok=True)
                    copy.write_bytes((ROOT / relative).read_bytes())
                    snapshot_source(selection, root)
                    with copy.open("ab") as target:
                        target.write(b"\noutside retained source spans\n")
                    with self.assertRaisesRegex(ValueError, "source changed"):
                        snapshot_source(selection, root)
                    copy.unlink()

    def test_archived_snapshots_replay_without_live_source_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            specs = inventory_specifications(SPATIAL_INVENTORY)
            history = History(root / "history")
            for spec in specs:
                record_batch([spec], history=history, fresh=True)
            # This fresh root contains no live scripts: replay uses retained bytes.
            self.assertFalse((root / "scripts").exists())
            replay = recheck_history(history)
            self.assertEqual(replay["status"], "unchanged")
            self.assertEqual(replay["submissions"], 14)
            self.assertEqual(replay["evaluation_status_counts"], {"unsupported": 14})
            self.assertEqual(replay["changes"], [])
            self.assertEqual(replay["errors"], [])


if __name__ == "__main__":
    unittest.main()
