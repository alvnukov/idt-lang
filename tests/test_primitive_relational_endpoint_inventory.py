"""Four relational endpoint proposals are retained sources, not new verdicts."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from theory_experiments.candidate_history import (
    DEFAULT_HISTORY,
    History,
    recheck_history,
    record_batch,
)
from theory_experiments.primitive_screen import object_fields
from theory_experiments.source_candidate import parse_source_candidate

INVENTORY = ROOT / "data/primitive_relational_endpoint_inventory.json"
SOURCES = {
    "binary_worldline_window_opposition_origin": "probe_binary_window_oppositions",
    "tetrahedral_directed_cycle_origin": "probe_tetrahedral_cycle_origin",
    "local_path_reunion_internal_signal_geometry": "probe_internal_signal_geometry",
    "conditional_opposition_magic_square_completion": "probe_opposition_magic_square",
}


class PrimitiveRelationalEndpointInventoryTests(unittest.TestCase):
    def assert_source_only(self, report: dict[str, object], spec: object) -> None:
        self.assertEqual(report["status"], "unsupported")
        self.assertEqual(report["proof_status"], "not_attempted")
        self.assertEqual(report["empirical_status"], "not_tested")
        scope = object_fields(report["scope"])
        self.assertEqual(scope["adapter_status"], "missing")
        self.assertEqual(scope["scientific_status"], "unassessed")
        self.assertEqual(
            scope["missing_bridges"], object_fields(spec)["missing_bridges"]
        )
        self.assertEqual(object_fields(report["request"])["candidate"], spec)
        checks = report["checks"]
        if not isinstance(checks, list):
            self.fail("source reports require an array of adapter checks")
        self.assertEqual(len(checks), 1)
        check = object_fields(checks[0])
        self.assertEqual(
            (check["id"], check["status"], check["checked"]),
            ("primitive_prediction_adapter", "unsupported", 0),
        )

    def test_four_frozen_module_digests_and_bounded_exact_spans(self) -> None:
        specs = inventory_specifications(INVENTORY)
        self.assertCountEqual([parse_source_candidate(s).id for s in specs], SOURCES)
        for spec in specs:
            candidate = parse_source_candidate(spec)
            with self.subTest(id=candidate.id):
                self.assertEqual(object_fields(spec)["family"], "source_theory")
                self.assertEqual(candidate.role, "route")
                self.assertGreaterEqual(len(candidate.missing_bridges), 5)
                self.assertEqual(
                    {s.path for s in candidate.sources},
                    {f"scripts/{SOURCES[candidate.id]}.py"},
                )
                for source in candidate.sources:
                    raw = (ROOT / source.path).read_bytes()
                    lines = raw.decode("utf-8").splitlines(keepends=True)
                    self.assertEqual(source.file_sha256, hashlib.sha256(raw).hexdigest())
                    self.assertLessEqual(source.last_line - source.first_line + 1, 40)
                    self.assertEqual(
                        source.text,
                        "".join(lines[source.first_line - 1 : source.last_line]),
                    )
                    self.assertEqual(
                        source.specification()["text_sha256"],
                        hashlib.sha256(source.text.encode("utf-8")).hexdigest(),
                    )

    def test_fresh_repeat_and_snapshot_replay_remain_unsupported(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory) / "history")
            for spec in inventory_specifications(INVENTORY):
                first = record_batch([spec], history=history, fresh=True)
                second = record_batch([spec], history=history, fresh=True)
                self.assertFalse(first.changes)
                self.assertFalse(second.changes)
                self.assertEqual(first.submission, second.submission)
                self.assertEqual(first.observation, second.observation)
                self.assert_source_only(first.results[0].report, spec)
            result = recheck_history(history)
            self.assertEqual(result["status"], "unchanged")
            self.assertEqual(result["submissions"], 4)
            self.assertEqual(result["evaluation_status_counts"], {"unsupported": 4})
            self.assertEqual(result["changes"], [])
            self.assertEqual(result["errors"], [])

    def test_canonical_history_contains_each_exact_source_once(self) -> None:
        expected = {
            parse_source_candidate(spec).id: spec
            for spec in inventory_specifications(INVENTORY)
        }
        history = History(DEFAULT_HISTORY)
        seen: list[str] = []
        for path in (DEFAULT_HISTORY / "submissions").glob("*.json"):
            rows = history.get("submissions", path.stem)["candidates"]
            if not isinstance(rows, list):
                self.fail("submission candidates must be an array")
            for spec in rows:
                identifier = object_fields(spec)["id"]
                if not isinstance(identifier, str) or identifier not in expected:
                    continue
                seen.append(identifier)
                self.assertEqual(rows, [expected[identifier]])
                reports = history.baseline(path.stem)["reports"]
                if not isinstance(reports, list):
                    self.fail("baseline reports must be an array")
                self.assertEqual(len(reports), 1)
                self.assert_source_only(object_fields(reports[0]), expected[identifier])
        self.assertCountEqual(seen, expected)


if __name__ == "__main__":
    unittest.main()
