"""The local-return probes can run without making their physics adapters exist."""

import unittest
from pathlib import Path

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES
from theory_experiments.candidate_history import DEFAULT_HISTORY, History
from theory_experiments.primitive_screen import object_fields
from theory_experiments.source_candidate import parse_source_candidate


class MarkedRelayHistoryTests(unittest.TestCase):
    def test_retained_sources_and_running_probes_have_different_contracts(self) -> None:
        specs = inventory_specifications(
            ROOT / "data/primitive_signal_relay_inventory.json"
        )
        expected = {parse_source_candidate(s).id: s for s in specs}
        owners = {
            "raw_opposition_flag_false_reunion_controls": {"probe_flag_local_reunions"},
            "finite_marked_signal_relay_minimality": {"probe_minimal_signal_relay"},
            "binary_edge_sign_transport_finite_relay": {
                "probe_relay_loop_parity",
                "probe_minimal_signal_relay",
            },
        }
        self.assertCountEqual(expected, owners)
        self.assertEqual(
            set(TOPIC_BUNDLES["marked_relays"]), set.union(*owners.values())
        )
        for key, spec in expected.items():
            candidate = parse_source_candidate(spec)
            self.assertEqual(
                {Path(s.path).stem for s in candidate.sources}, owners[key]
            )
            self.assertTrue(candidate.missing_bridges)
        archive = History(DEFAULT_HISTORY)
        seen: list[str] = []
        for path in (DEFAULT_HISTORY / "submissions").glob("*.json"):
            rows = archive.get("submissions", path.stem)["candidates"]
            if not isinstance(rows, list):
                self.fail("invalid submission")
            for row in rows:
                archived_id = object_fields(row)["id"]
                if not isinstance(archived_id, str) or archived_id not in expected:
                    continue
                self.assertEqual(rows, [expected[archived_id]])
                reports = archive.baseline(path.stem)["reports"]
                if not isinstance(reports, list):
                    self.fail("invalid baseline")
                self.assertEqual(len(reports), 1)
                report = object_fields(reports[0])
                self.assertEqual(report["status"], "unsupported")
                self.assertEqual(report["empirical_status"], "not_tested")
                self.assertEqual(report["proof_status"], "not_attempted")
                self.assertEqual(
                    object_fields(report["scope"])["adapter_status"], "missing"
                )
                seen.append(archived_id)
        self.assertCountEqual(seen, owners)
