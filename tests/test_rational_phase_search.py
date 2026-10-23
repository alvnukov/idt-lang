"""Fixed rational probes preserve exact evidence and finite-only claim boundaries."""

from __future__ import annotations

import copy
import gzip
import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from scripts.search_rational_phases import main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import rational_phase_search as phase
from theory_experiments.candidate_history import History
from theory_experiments.primitive_screen import canonical_json, load_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate


def array(value: object) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("expected test array")
    return value


def state(value: object) -> phase.State:
    a, b = array(value)
    return Fraction(str(a)), Fraction(str(b))


def independent_p(model: phase.RationalModel, x: phase.State) -> str:
    a, b = x
    plus = ((a+1)**2 + model.eta*b*b)**model.power
    minus = ((a-1)**2 + model.eta*b*b)**model.power
    return str(plus/(plus+minus))


class RationalPhaseSearchTests(unittest.TestCase):
    report: dict[str, object]
    rows: list[dict[str, object]]

    @classmethod
    def setUpClass(cls) -> None:
        cls.report = phase.campaign(phase.load_config())
        cls.rows = [object_fields(row) for row in array(cls.report["candidates"])]

    def test_grid_exact_deduplicated_and_sorted(self) -> None:
        values = phase.coordinates()
        self.assertEqual(len(values), 89)
        self.assertEqual(values, tuple(sorted(set(values))))
        self.assertEqual(values[0], -2)
        self.assertEqual(values[-1], 2)
        self.assertIn(Fraction(1, 8), values)
        self.assertNotIn(Fraction(1, 9), values)
        self.assertTrue(all(type(value) is Fraction for value in values))

    def test_config_rejects_tuning_floats_bools_and_extra_keys(self) -> None:
        self.assertEqual(phase.load_config(), phase.campaign_config())
        for key, value in (("denominator_max", 9), ("matrix_depth", True),
                           ("coordinate_radius", 2.0), ("max_multiplications", 9),
                           ("clip_products_to_grid", 0), ("plane_seeds", [[1, 0]]),
                           ("scalar_seeds", [[True, 0]])):
            config = phase.campaign_config()
            config[key] = value
            with self.subTest(key=key), self.assertRaises((ValueError, TypeError)):
                phase.validate_config(config)
        config = phase.campaign_config()
        config["extra"] = 0
        with self.assertRaises(ValueError):
            phase.validate_config(config)

    def test_all_five_retained_with_exact_coverage_and_no_upgrades(self) -> None:
        self.assertEqual(len(self.rows), 5)
        self.assertEqual(len({m.id for m in phase.candidates()}), 5)
        self.assertEqual([object_fields(r["coverage"])["scanned_tuples"] for r in self.rows],
                         [89, 7921, 7921, 7921, 7921])
        self.assertEqual([object_fields(r["coverage"])["selected_units"] for r in self.rows],
                         [2, 178, 12, 6, 12])
        for row in self.rows:
            self.assertEqual(row["candidate_verdict"], "unchanged")
            self.assertEqual(object_fields(row["source_proposal_screen"])["status"], "unsupported")
        self.assertEqual(self.report["empirical_status"], "not_tested")
        self.assertIsNone(self.report["archival"])

    def test_full_matrix_independently_recomputed_no_product_clipping(self) -> None:
        outside_grid_seen = False
        grid = set(phase.coordinates())
        for model, row in zip(phase.candidates(), self.rows, strict=True):
            matrix = object_fields(row["continuation"])
            units = [state(u) for u in array(row["selected_units"])]
            unique = [array(r) for r in array(matrix["unique_rows"])]
            indices = array(matrix["row_indices"])
            self.assertEqual(matrix["matrix_cells"], len(units)**2)
            for i, x in enumerate(units):
                compressed = unique[int(str(indices[i]))]
                a, b = x
                for j, u in enumerate(units):
                    c, d = u
                    following = (a*c+model.k*b*d, a*d+b*c)
                    outside_grid_seen |= any(part not in grid for part in following)
                    self.assertEqual(compressed[j], independent_p(model, following))
            self.assertTrue(matrix["matrix_complete"])
            self.assertEqual(matrix["action_comparisons_performed"], matrix["action_comparisons_planned"])
            self.assertEqual(matrix["invalid_current_readouts"], 0)
            self.assertEqual(matrix["invalid_matrix_cells"], 0)
        self.assertTrue(outside_grid_seen)

    def test_expected_witnesses_independent_same_map_same_action(self) -> None:
        expected = [("1/10", "16/25"), ("1/3", "1/9"), ("1/82", "256/337")]
        for model, row, (current, next_x) in zip(phase.candidates()[2:], self.rows[2:], expected, strict=True):
            matrix = object_fields(row["continuation"])
            witness = object_fields(matrix["first_witness"])
            x, y, u = state(witness["state_x"]), state(witness["state_y"]), state(witness["action"])
            expected_x = ((Fraction(-1, 3), Fraction(-2, 3)) if model.eta == 2 else
                          (Fraction(-4, 5), Fraction(-3, 5)))
            self.assertEqual(x, expected_x)
            self.assertEqual(y, (expected_x[0], -expected_x[1]))
            self.assertEqual(u, expected_x)
            self.assertEqual(independent_p(model, x), current)
            self.assertEqual(independent_p(model, y), current)
            self.assertEqual(independent_p(model, model.multiply(x, u)), next_x)
            self.assertEqual(independent_p(model, model.multiply(y, u)), "1")
            self.assertEqual(object_fields(witness["next_x"])["p"], next_x)
            self.assertEqual(object_fields(witness["next_y"])["p"], "1")

    def test_scalar_dual_controls_and_row_partitions(self) -> None:
        self.assertEqual([object_fields(r["continuation"])["distinct_full_rows"] for r in self.rows],
                         [2, 2, 12, 6, 12])
        for row in self.rows[:2]:
            matrix = object_fields(row["continuation"])
            self.assertIsNone(matrix["first_witness"])
            self.assertEqual(matrix["result"], "no_witness_in_selected_matrix")
            self.assertTrue(all(object_fields(p)["distinct_full_continuation_rows"] == 1
                                for p in array(matrix["current_readout_partition"])))
        dual = object_fields(self.rows[1]["continuation"])
        self.assertEqual(dual["same_current_unordered_pairs"], 2*(89*88//2))
        self.assertEqual(dual["action_comparisons_performed"], 2*(89*88//2)*178)

    def test_all_nine_trace_points_open_is_not_rejected(self) -> None:
        expected = [(2, 0, 0), (2, 176, 0), (4, 8, 10), (2, 4, 4), (4, 8, 10)]
        for row, counts in zip(self.rows, expected, strict=True):
            summary = object_fields(array(row["trace_summaries"])[0])
            self.assertEqual((summary["closed"], summary["open"], summary["nonbinary"]), counts)
            for raw in array(row["traces"]):
                trace = object_fields(raw)
                self.assertEqual(len(array(trace["trace"])), 9)
                self.assertFalse(trace["invalid_readout"])
                self.assertTrue(trace["visited_state_weights_equal_seed"])
                self.assertEqual(trace["candidate_verdict"], "unchanged")
        dual_model = phase.candidates()[1]
        dual = phase.probe_orbit(dual_model, (Fraction(1), Fraction(1)), phase.ONE)
        self.assertEqual(dual["orbit_status"], "open_within_bound")
        self.assertIsNone(dual["first_exact_state_repetition"])
        self.assertEqual({object_fields(p)["p"] for p in array(dual["trace"])}, {"1"})

    def test_previous_rational_leads_recomputed(self) -> None:
        leads = object_fields(load_json(phase.ROOT / "data/native_phase_search/rational_extension_leads.json"))
        mapping = {"rational_phase_weighted_two_v1": phase.candidates()[3],
                   "rational_phase_gaussian_v1": phase.candidates()[2]}
        for value in array(leads["candidates"]):
            lead = object_fields(value)
            model = mapping[str(lead["id"])]
            spec = object_fields(lead["specification"])
            trace = phase.probe_orbit(model, state(spec["multiplier"]), state(spec["seed"]))
            old_rows = [*array(lead["observations"]), lead["next_state_observation"]]
            for old, new in zip(old_rows, array(trace["trace"]), strict=True):
                old_row, new_row = object_fields(old), object_fields(new)
                for key in ("state", "weight", "plus_weight", "minus_weight", "denominator", "p"):
                    self.assertEqual(old_row[key], new_row[key])

    def test_signature_intersections_and_i3_controls(self) -> None:
        comparison = object_fields(self.report["signature_comparisons"])
        self.assertEqual(list(object_fields(comparison["distinct_counts"]).values()), [2, 2, 7, 4, 7])
        pairs = {(str(object_fields(r)["left"]), str(object_fields(r)["right"])): object_fields(r)
                 for r in array(comparison["pairs"])}
        models = phase.candidates()
        self.assertEqual(pairs[(models[0].id, models[1].id)]["intersection"], 2)
        self.assertEqual(pairs[(models[2].id, models[3].id)]["intersection"], 2)
        self.assertEqual(pairs[(models[3].id, models[4].id)]["intersection"], 2)
        self.assertEqual(pairs[(models[2].id, models[4].id)]["intersection"], 3)
        self.assertEqual([object_fields(r["equal_one_i3"])["actual"] for r in self.rows], ["0"]*4+["36"])

    def test_invalid_ports_and_zero_denominator_retained(self) -> None:
        zero = phase.port_readout(Fraction(0), Fraction(0))
        self.assertEqual(zero["issues"], ["zero_denominator"])
        self.assertIsNone(zero["p"])
        negative = phase.port_readout(Fraction(-1), Fraction(2))
        self.assertEqual(negative["issues"], ["negative_weight"])
        self.assertIsNone(negative["p"])
        self.assertEqual(phase.port_readout(Fraction(-2), Fraction(1))["issues"],
                         ["negative_weight", "negative_denominator"])
        indefinite = phase.RationalModel("invalid_test", False, -1, -1)
        matrix = phase.continuation_matrix(indefinite, [(Fraction(0), Fraction(1))])
        self.assertEqual(matrix["invalid_current_readouts"], 1)
        self.assertIn("issues", object_fields(array(matrix["current_readouts"])[0]))

    def test_invalid_continuations_are_diagnostics_not_positive_witnesses(self) -> None:
        hostile = phase.RationalModel("hostile_test_only", False, 0, -1)
        # Both current ports are valid with p=1, but (2,1)^2=(4,4) is invalid.
        points = [(Fraction(1), Fraction(0)), (Fraction(2), Fraction(1))]
        matrix = phase.continuation_matrix(hostile, points)
        self.assertTrue(all(object_fields(r)["valid"] for r in array(matrix["current_readouts"])))
        self.assertEqual(matrix["invalid_matrix_cells"], 1)
        self.assertIsNone(matrix["first_witness"])
        self.assertEqual(matrix["action_comparisons_performed"], 2)
        self.assertTrue(any(isinstance(cell, dict) for row in array(matrix["unique_rows"])
                            for cell in array(row)))

    def test_deterministic_digest_and_changed_source_guards(self) -> None:
        evidence = {k: v for k, v in self.report.items() if k != "report_sha256"}
        self.assertEqual(pipeline.digest(evidence), self.report["report_sha256"])
        self.assertEqual(phase.campaign(phase.campaign_config()), self.report)
        hashes = phase.source_hashes()
        changed = {**hashes, phase.SOURCE_PATHS[0]: "0"*64}
        with patch.object(phase, "source_hashes", return_value=changed), self.assertRaises(ValueError):
            phase.campaign(phase.campaign_config())
        with patch.object(phase, "source_hashes", side_effect=[hashes, changed]), self.assertRaises(ValueError):
            phase.campaign(phase.campaign_config())

    def test_retained_campaign_scientific_payload_replays_exactly(self) -> None:
        fixture = phase.ROOT / "data/rational_phase_search/campaign-v1.json.gz"
        saved = object_fields(json.loads(gzip.decompress(fixture.read_bytes())))
        saved_evidence = {key: value for key, value in saved.items() if key != "report_sha256"}
        self.assertEqual(pipeline.digest(saved_evidence), saved["report_sha256"])
        saved_candidates = [object_fields(row) for row in array(saved["candidates"])]
        self.assertEqual(len(saved_candidates), len(self.rows))
        for retained, fresh in zip(saved_candidates, self.rows, strict=True):
            # Request/source hashes may change; every scientific probe must replay.
            self.assertEqual({key: value for key, value in retained.items() if key != "source_proposal_screen"},
                             {key: value for key, value in fresh.items() if key != "source_proposal_screen"})
        provenance_only = {"archival", "source_sha256", "screen_provenance", "report_sha256", "candidates"}
        self.assertEqual({key: value for key, value in saved.items() if key not in provenance_only},
                         {key: value for key, value in self.report.items() if key not in provenance_only})
        self.assertEqual(saved["config"], self.report["config"])
        self.assertEqual(saved["signature_comparisons"], self.report["signature_comparisons"])
        self.assertEqual(saved["boundaries"], self.report["boundaries"])

    def test_source_proposals_full_specs_and_bounded_snapshots(self) -> None:
        specs = phase.source_proposals(phase.campaign_config(), phase.source_hashes())
        self.assertLessEqual(len(canonical_json(specs).encode()), 131072)
        for model, raw in zip(phase.candidates(), specs, strict=True):
            proposal = parse_source_candidate(raw)
            self.assertEqual(proposal.id, model.id)
            self.assertEqual(proposal.role, "lower_law")
            self.assertEqual(proposal.declared_status, "exploratory_finite")
            self.assertEqual(json.loads(proposal.components[0]), model.specification())
            self.assertEqual(proposal.missing_bridges, phase.MISSING_BRIDGES)
            self.assertEqual(proposal.sources[0].text,
                             (phase.ROOT / "theory_experiments/rational_phase_search.py").read_text())

    def test_temp_history_all_five_unsupported_append_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory))
            first = phase.campaign(phase.campaign_config(), history=history)
            saved = {p.relative_to(directory): p.read_bytes() for p in Path(directory).rglob("*") if p.is_file()}
            second = phase.campaign(phase.campaign_config(), history=history)
            self.assertEqual(first, second)
            self.assertEqual(saved, {p.relative_to(directory): p.read_bytes() for p in Path(directory).rglob("*") if p.is_file()})
            archival = object_fields(first["archival"])
            submission = history.get("submissions", str(archival["submission"]))
            observation = history.get("observations", str(archival["observation"]))
            self.assertEqual(len(array(submission["candidates"])), 5)
            self.assertEqual([object_fields(r)["status"] for r in array(observation["reports"])], ["unsupported"]*5)
            self.assertNotIn("sources", canonical_json(first["candidates"]))

    def test_inputs_archived_before_probe_execution_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory))
            with (patch.object(phase, "candidate_evidence", side_effect=RuntimeError("probe crash")),
                  self.assertRaisesRegex(RuntimeError, "probe crash")):
                phase.campaign(phase.campaign_config(), history=history)
            submissions = list((history.root/"submissions").glob("*.json"))
            self.assertEqual(len(submissions), 1)
            saved = history.get("submissions", submissions[0].stem)
            self.assertEqual(len(array(saved["candidates"])), 5)

    def test_cli_deterministic_gzip_exclusive_and_compact_stdout(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output, duplicate = Path(directory)/"evidence.json.gz", Path(directory)/"same.json.gz"
            # Reuse verified calculation; this test targets publication only.
            with patch("scripts.search_rational_phases.campaign", return_value=copy.deepcopy(self.report)):
                for path in (output, duplicate):
                    stream = io.StringIO()
                    with redirect_stdout(stream):
                        self.assertEqual(main(["--output", str(path)]), 0)
                    self.assertLess(len(stream.getvalue().encode()), 2048)
                self.assertEqual(output.read_bytes(), duplicate.read_bytes())
                self.assertEqual(json.loads(gzip.decompress(output.read_bytes())), self.report)
                before = output.read_bytes()
                with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    main(["--output", str(output)])
                self.assertEqual(output.read_bytes(), before)
                for args in (["--record-history"], ["--history-dir", directory],
                             ["--output", str(Path(directory)/"bad.txt")]):
                    with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                        main(args)


if __name__ == "__main__":
    unittest.main()
