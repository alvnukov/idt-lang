"""Source-level research packets keep immutable, unassessed baselines."""

import hashlib
import unittest

from scripts.archive_existing_primitives import ROOT, inventory_specifications
from scripts.replay_primitive_probe_campaign import TOPIC_BUNDLES
from theory_experiments import candidate_pipeline
from theory_experiments.candidate_history import DEFAULT_HISTORY, SCHEMA, History
from theory_experiments.primitive_screen import Limits
from theory_experiments.source_candidate import parse_source_candidate

PACKS = {
    "primitive_event_origin_inventory.json": ("single_event_origins", {
        "unary_chain_first_passage_detector": "probe_unary_first_passage_detector",
        "reciprocal_petals_with_port_memory": "probe_reciprocal_detector_petals",
        "reversible_marker_detector_sector": "probe_reversible_excitation_detector",
        "driven_context_rate_memory_requirement": "probe_driven_readout_memory",
        "driven_event_trace_memory_witness": "probe_event_memory_witness",
        "second_delft_context_rotor_scope": "probe_delft_second_rotor",
    }),
    "primitive_observer_clock_inventory.json": ("local_observer_clocks", {
        "internal_port_latch_reference_clock": "probe_internal_detector_clocks",
        "matched_detuned_petal_reference": "probe_matched_vernier_petals",
        "externally_stimulated_carry_slip": "probe_trigger_carry_slip",
        "periodic_calendar_contact_alias": "probe_calendar_carry_alias",
        "coprime_raw_signed_encounters": "probe_coprime_signed_encounters",
    }),
}


class RetainedEventResearchTests(unittest.TestCase):
    def test_campaign_and_immutable_source_bytes(self):
        for filename, (bundle, ids) in PACKS.items():
            self.assertCountEqual(ids.values(), TOPIC_BUNDLES[bundle])
            specs = inventory_specifications(ROOT / "data" / filename)
            self.assertCountEqual((s["id"] for s in specs), ids)
            for spec in specs:
                row = parse_source_candidate(spec)
                with self.subTest(id=row.id):
                    self.assertEqual({s.path for s in row.sources}, {f"scripts/{ids[row.id]}.py"})
                    for src in row.sources:
                        raw = (ROOT / src.path).read_bytes()
                        self.assertEqual(src.file_sha256, hashlib.sha256(raw).hexdigest())
                        self.assertEqual(src.text.encode(), b"".join(
                            raw.splitlines(keepends=True)[src.first_line-1:src.last_line]))

    def test_pinned_original_reports_and_replay(self):
        archive = History(DEFAULT_HISTORY)
        for filename in PACKS:
            specs = inventory_specifications(ROOT / "data" / filename)
            results = candidate_pipeline.run_batch(specs, fresh=True)
            for spec, outcome in zip(specs, results, strict=True):
                with self.subTest(id=spec["id"]):
                    request = {"schema": SCHEMA, "limits": Limits().specification(), "candidates": [spec]}
                    key = candidate_pipeline.digest(request)
                    self.assertEqual(request, archive.get("submissions", key))
                    stored, = archive.baseline(key)["reports"]
                    for r in (stored, outcome.report):
                        self.assertEqual((r["status"], r["proof_status"], r["empirical_status"]),
                                         ("unsupported", "not_attempted", "not_tested"))
                    self.assertEqual(outcome.report["scope"]["scientific_status"], "unassessed")
                    self.assertEqual(outcome.report["scope"]["adapter_status"], "missing")
                    self.assertEqual(len(outcome.report["checks"]), 1)
                    self.assertEqual(outcome.report["checks"][0]["id"], "primitive_prediction_adapter")
