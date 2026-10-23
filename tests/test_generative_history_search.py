"""Independent event-expansion oracles and immutable finite-campaign evidence."""

from __future__ import annotations

import copy
import gzip
import hashlib
import io
import json
import tempfile
import time
import unittest
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import FrozenInstanceError
from fractions import Fraction
from itertools import product
from pathlib import Path
from unittest.mock import patch

from scripts.search_generative_histories import main
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import generative_history_search as search
from theory_experiments.candidate_history import History, recheck_history
from theory_experiments.primitive_screen import canonical_json, object_fields
from theory_experiments.source_candidate import parse_source_candidate


def array(value: object) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("expected array")
    return value


def events(n: search.Bag) -> list[int]:
    return [j for j, count in enumerate(n) for _ in range(count)]


def counts(labels: list[int], m: int) -> search.Bag:
    return tuple(labels.count(j) for j in range(m))


def oracle_serial(x: search.Bag, y: search.Bag) -> search.Bag:
    return counts([(i+j) % len(x) for i in events(x) for j in events(y)], len(x))


def oracle_normal(x: search.Bag) -> search.Bag:
    labels = events(x)
    if len(x) == 3:
        return labels.count(0)-labels.count(2), labels.count(1)-labels.count(2)
    return tuple(labels.count(j)-labels.count(j+len(x)//2) for j in range(len(x)//2))


def oracle_weight(model: search.Variant, x: search.Bag) -> Fraction:
    labels = events(x)
    if model.kernel2:
        return sum((Fraction(model.kernel2[(i-j) % len(x)], 2) for i in labels for j in labels), Fraction())
    if model.readout == "raw_cardinality":
        return Fraction(len(labels))
    d = oracle_normal(x)
    if model.readout == "residual_l1":
        return Fraction(sum(abs(v) for v in d))
    a = sum(v*v for v in d)
    if model.readout == "diagonal_square":
        return Fraction(a*a)
    b = d[0]*d[1]-d[0]*d[3]+d[1]*d[2]+d[2]*d[3]
    return Fraction(a*a-2*b*b)


def check(row: dict[str, object], name: str) -> dict[str, object]:
    return object_fields(object_fields(row["checks"])[name])


class GenerativeHistorySearchTests(unittest.TestCase):
    report: dict[str, object]
    rows: dict[str, dict[str, object]]

    @classmethod
    def setUpClass(cls) -> None:
        start = time.monotonic()
        cls.report = search.campaign(search.load_config())
        if time.monotonic()-start > 30:
            raise AssertionError("fixed campaign exceeded generous 30-second local runtime bound")
        cls.rows = {str(object_fields(object_fields(r)["candidate_specification"])["id"]): object_fields(r)
                    for r in array(cls.report["candidates"])}

    def test_fixed_config_and_frozen_models(self) -> None:
        self.assertEqual(search.load_config(), search.campaign_config())
        for key, bad in (("bag_total_bound", 3), ("all_ordered_pairs", 1), ("clip_operation_outputs", True),
                         ("bag_total_bound", 2.0), ("candidate_ids", []), ("kernel_selection", {})):
            config = search.campaign_config()
            config[key] = bad
            with self.subTest(key=key), self.assertRaises((ValueError, TypeError)):
                search.validate_config(config)
        with self.assertRaises(ValueError):
            search.validate_config({**search.campaign_config(), "extra": 0})
        with self.assertRaises(FrozenInstanceError):
            attribute = "m"
            setattr(search.candidates()[0], attribute, 3)

    def test_raw_event_operations_quotient_and_descent_independent(self) -> None:
        for m, size in ((2, 6), (3, 10), (4, 15), (6, 28), (8, 45)):
            domain = search.bags(m)
            self.assertEqual(len(domain), size)
            self.assertEqual(domain, tuple(sorted(set(domain))))
            self.assertTrue(all(sum(x) <= 2 for x in domain))
            for x, y in product(domain, repeat=2):
                raw = oracle_serial(x, y)
                self.assertEqual(search.serial(x, y), raw)
                self.assertEqual(search.union(x, y), counts(events(x)+events(y), m))
                self.assertEqual(search.normal(x), oracle_normal(x))
                self.assertEqual(search.reduced_serial(oracle_normal(x), oracle_normal(y), m), oracle_normal(raw))
                for gen in search.generators(m):
                    inserted = counts(events(x)+events(gen), m)
                    self.assertEqual(oracle_normal(inserted), oracle_normal(x))
                    self.assertEqual(oracle_normal(oracle_serial(inserted, y)), oracle_normal(raw))
                    self.assertEqual(oracle_normal(oracle_serial(y, inserted)), oracle_normal(raw))
            operation = object_fields(object_fields(self.report["operation_checks"])[str(m)])
            for name in ("normal_addition", "normal_serial", "alternative_descent", "serial_descent"):
                probe = object_fields(operation[name])
                expected = size*size*(2*len(search.generators(m)) if "descent" in name else 1)
                self.assertEqual((probe["planned"], probe["performed"], probe["failures"]), (expected, expected, 0))
            self.assertEqual(object_fields(operation["maximum_descent_output_cardinality"])["serial"],
                             10 if m == 3 else 8)
            self.assertFalse(operation["outputs_clipped"])

    def test_all27_retained_complete_coverage_and_independent_weights(self) -> None:
        self.assertEqual(len(self.rows), 27)
        for model in search.candidates():
            row = self.rows[model.id]
            size, gen_count = len(search.bags(model.m)), len(search.generators(model.m))
            for name, count in (("empty_zero", 1), ("two_alternative_interference", size**2),
                                ("nonnegative_bounded_inputs", size), ("readout_invariance", size*gen_count),
                                ("serial_weight_multiplicativity", size**2), ("i3", size**3)):
                self.assertEqual((check(row, name)["planned"], check(row, name)["performed"]), (count, count))
            for x in search.bags(model.m):
                self.assertEqual(Fraction(model.weight2(x), 2), oracle_weight(model, x))
            self.assertEqual(row["candidate_verdict"], "unchanged")
            self.assertEqual(row["registration_status"], "not_registered")
            self.assertEqual(object_fields(row["source_proposal_screen"])["status"], "unsupported")
        self.assertEqual(self.report["empirical_status"], "not_tested")
        self.assertIsNone(self.report["archival"])

    def test_inapplicable_pair_formula_and_nonadditivity_diagnostic(self) -> None:
        for model in search.candidates()[5:]:
            self.assertEqual(check(self.rows[model.id], "raw_pair_quotient_formula")["result"],
                             "not_applicable_no_calculation")
        raw = self.rows["history_c4_raw_cardinality"]
        self.assertEqual(check(raw, "two_alternative_interference")["failures"], 0)
        for model in search.candidates()[:5]:
            self.assertNotEqual(check(self.rows[model.id], "two_alternative_interference")["failures"], 0)

    def test_pair_baselines_and_product_counterexamples(self) -> None:
        for model in search.candidates()[:5]:
            row = self.rows[model.id]
            self.assertEqual(check(row, "raw_pair_quotient_formula")["failures"], 0)
            self.assertEqual(check(row, "i3")["failures"], 0)
            failed = check(row, "serial_weight_multiplicativity")["failures"]
            self.assertEqual(failed == 0, model.m in (2, 3, 4))
            if model.m in (6, 8):
                n = counts([0, 1], model.m)
                self.assertEqual(oracle_weight(model, oracle_serial(n, n)), 6)
                self.assertEqual(oracle_weight(model, n)**2, 4)

    def test_first_weight_witnesses_replay_from_literal_events(self) -> None:
        for model in search.candidates():
            row = self.rows[model.id]
            for name in ("nonnegative_bounded_inputs", "readout_invariance", "serial_weight_multiplicativity",
                         "two_alternative_interference", "i3"):
                probe = check(row, name)
                if probe["first_witness"] is None:
                    self.assertEqual(probe["failures"], 0)
                    continue
                witness = object_fields(probe["first_witness"])
                x = tuple(int(str(v)) for v in array(witness["x"]))
                wx = oracle_weight(model, x)
                if name == "nonnegative_bounded_inputs":
                    self.assertLess(wx, 0)
                    self.assertEqual(str(wx), witness["weight"])
                elif name == "readout_invariance":
                    gen = tuple(int(str(v)) for v in array(witness["generator"]))
                    after = oracle_weight(model, counts(events(x)+events(gen), model.m))
                    self.assertNotEqual(wx, after)
                    self.assertEqual((str(wx), str(after)), (witness["before"], witness["after"]))
                else:
                    y = tuple(int(str(v)) for v in array(witness["y"]))
                    wy = oracle_weight(model, y)
                    if name == "serial_weight_multiplicativity":
                        actual, expected = oracle_weight(model, oracle_serial(x, y)), wx*wy
                    else:
                        actual = oracle_weight(model, counts(events(x)+events(y), model.m))-wx-wy
                        expected = Fraction()
                        if name == "i3":
                            z = tuple(int(str(v)) for v in array(witness["z"]))
                            actual = (oracle_weight(model, counts(events(x)+events(y)+events(z), model.m))
                                      -oracle_weight(model, counts(events(x)+events(y), model.m))
                                      -oracle_weight(model, counts(events(x)+events(z), model.m))
                                      -oracle_weight(model, counts(events(y)+events(z), model.m))
                                      +wx+wy+oracle_weight(model, z))
                    self.assertNotEqual(actual, expected)
                    self.assertEqual(str(actual), witness["actual"])

    def test_negative_controls_and_quartic_survivor(self) -> None:
        raw = self.rows["history_c4_raw_cardinality"]
        self.assertEqual(check(raw, "serial_weight_multiplicativity")["failures"], 0)
        self.assertEqual(check(raw, "i3")["failures"], 0)
        witness = object_fields(check(raw, "readout_invariance")["first_witness"])
        self.assertEqual((witness["x"], witness["before"], witness["after"]), ([0]*4, "0", "2"))
        l1 = next(m for m in search.candidates() if m.readout == "residual_l1")
        plus, minus = counts([0], 4), counts([2], 4)
        i3 = (oracle_weight(l1, counts([0, 0, 2], 4))-oracle_weight(l1, counts([0, 0], 4))
              -2*oracle_weight(l1, counts([0, 2], 4))+2*oracle_weight(l1, plus)+oracle_weight(l1, minus))
        self.assertEqual(i3, 2)
        for name in ("history_c4_diagonal_square", "history_c8_quartic"):
            self.assertEqual(object_fields(self.rows[name]["equal_one_i3"])["actual"], "36")
            self.assertNotEqual(check(self.rows[name], "i3")["failures"], 0)
        self.assertEqual(check(self.rows["history_c8_quartic"], "serial_weight_multiplicativity")["performed"], 2025)
        self.assertEqual(check(self.rows["history_c8_quartic"], "serial_weight_multiplicativity")["failures"], 0)

    def test_kernel_grid_survivors_without_rejecting_irrational_lead(self) -> None:
        survivors = {m: [v.kernel2[1] for v in search.candidates() if v.group == f"c{m}_kernel_grid"
                         and check(self.rows[v.id], "serial_weight_multiplicativity")["failures"] == 0] for m in (6, 8)}
        self.assertEqual(survivors, {6: [-2, 1], 8: []})
        self.assertEqual(object_fields(array(self.report["untested_leads"])[0])["status"],
                         "untested_not_rejected_by_rational_grid")

    def test_presentation_map_products_and_bounded_weights(self) -> None:
        maps = object_fields(object_fields(self.report["presentation_maps"])["maps"])
        self.assertEqual(len(maps), 3)
        for name, raw in maps.items():
            row = object_fields(raw)
            m = 3 if name.startswith("c3_") else 6
            self.assertEqual(object_fields(row["label_products"])["performed"], m*m)
            self.assertEqual(object_fields(row["label_products"])["failures"], 0)
            self.assertEqual(object_fields(row["bounded_weights"])["performed"], len(search.bags(m)))
            self.assertEqual(object_fields(row["bounded_weights"])["failures"], 0)
        scalar = next(v for v in search.candidates() if v.id == "history_c6_kernel_a2_n2")
        plane = next(v for v in search.candidates() if v.id == "history_c6_kernel_a2_p1")
        mapping = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]
        for n in search.bags(6):
            self.assertEqual(oracle_weight(scalar, n), sum((-1)**j*n[j] for j in range(6))**2)
            a = sum(n[j]*mapping[j][0] for j in range(6))
            b = sum(n[j]*mapping[j][1] for j in range(6))
            self.assertEqual(oracle_weight(plane, n), a*a-a*b+b*b)

    def test_all90_selection_hypotheses_and_isolated_zero_trap(self) -> None:
        for m, count, checks, selected in ((3, 9, 90, ["selection_c3_a2_-1_b2_0"]),
                                           (4, 81, 2430, ["selection_c4_a2_0_b2_-2"])):
            selection = object_fields(object_fields(self.report["kernel_selection"])[str(m)])
            self.assertEqual(selection["hypothesis_count"], count)
            self.assertEqual(selection["reference_checks_planned"], checks)
            self.assertEqual(selection["reference_checks_performed"], checks)
            self.assertEqual(selection["selected_within_declared_kernel_class"], selected)
        c4 = object_fields(object_fields(self.report["kernel_selection"])["4"])
        isolated_survivors = [object_fields(r) for r in array(c4["kernels"])
                              if object_fields(object_fields(r)["isolated_cancellation_zero"])["failures"] == 0]
        self.assertEqual(len(isolated_survivors), 9)
        failures = [object_fields(r["reference_invariance"])["failures"] for r in isolated_survivors]
        self.assertEqual(sorted(int(str(v)) for v in failures), [0]+[18]*8)
        trap = search.Variant("literal_trap", "test", 4, "kernel_pair", (2, -4, -2, -4))
        self.assertEqual(oracle_weight(trap, counts([0], 4)), 1)
        self.assertEqual(oracle_weight(trap, counts([0, 1, 3], 4)), -7)

    def test_source_binding_full_variant_specs_and_all_kernel_hypotheses(self) -> None:
        hashes = search.source_hashes()
        archive = object_fields(self.report["exact_source_archive"])
        self.assertEqual(pipeline.digest(archive), self.report["exact_source_archive_sha256"])
        for path, value in archive.items():
            text = object_fields(value)["text"]
            self.assertIsInstance(text, str)
            self.assertEqual(hashlib.sha256(str(text).encode()).hexdigest(), hashes[path])
            self.assertEqual(str(text), (search.ROOT/path).read_text())
        specs = search.source_proposals(search.campaign_config(), hashes, pipeline.digest(archive))
        self.assertEqual(len(specs), 11)
        self.assertLessEqual(len(canonical_json(specs).encode()), 131072)
        seen_variants, seen_kernels = [], []
        for value in specs:
            proposal = parse_source_candidate(value)
            self.assertEqual(proposal.role, "law_family_collection")
            self.assertIn("exact_source_archive_sha256="+pipeline.digest(archive), proposal.components)
            for component in proposal.components:
                if component.startswith("{"):
                    seen_variants.append(json.loads(component))
                elif component.startswith("["):
                    seen_kernels.extend(json.loads(component))
        self.assertEqual(seen_variants, [v.specification() for v in search.candidates()])
        self.assertEqual(len(seen_kernels), 90)
        self.assertEqual({canonical_json(v) for v in seen_kernels},
                         {canonical_json(v) for m in (3, 4) for v in search.kernel_hypotheses(m)})

    def test_deterministic_report_digest_and_import_capture_finish_guards(self) -> None:
        self.assertEqual(pipeline.digest({k: v for k, v in self.report.items() if k != "report_sha256"}),
                         self.report["report_sha256"])
        self.assertEqual(search.campaign(search.campaign_config()), self.report)
        hashes = search.source_hashes()
        changed = {**hashes, search.SOURCE_PATHS[0]: "0"*64}
        with patch.object(search, "source_hashes", return_value=changed), self.assertRaises(ValueError):
            search.campaign(search.campaign_config())
        with self.assertRaisesRegex(ValueError, "archive capture"):
            search.source_archive(changed)
        with patch.object(search, "source_hashes", side_effect=[hashes, changed]), self.assertRaises(ValueError):
            search.campaign(search.campaign_config())
        with patch.object(search, "source_hashes", side_effect=[hashes, hashes, changed]), self.assertRaises(ValueError):
            search.campaign(search.campaign_config())

    def test_saved_full_scientific_report_replays_without_optional_skip(self) -> None:
        fixture = search.ROOT/"data/generative_history_search/campaign-v1.json.gz"
        saved = object_fields(json.loads(gzip.decompress(fixture.read_bytes())))
        self.assertEqual(pipeline.digest({k: v for k, v in saved.items() if k != "report_sha256"}), saved["report_sha256"])
        archive = object_fields(saved["exact_source_archive"])
        self.assertEqual(pipeline.digest(archive), saved["exact_source_archive_sha256"])
        hashes = object_fields(saved["source_sha256"])
        for path, raw in archive.items():
            entry = object_fields(raw)
            self.assertEqual(hashlib.sha256(str(entry["text"]).encode()).hexdigest(), hashes[path])
            self.assertEqual(entry["sha256"], hashes[path])

        def scientific_payload(report: dict[str, object]) -> dict[str, object]:
            metadata = {"archival", "source_sha256", "exact_source_archive", "exact_source_archive_sha256",
                        "screen_provenance", "report_sha256"}
            payload = copy.deepcopy({k: v for k, v in report.items() if k not in metadata})
            rows = []
            for raw in array(payload["candidates"]):
                row = object_fields(raw)
                # Status and meaning remain compared; only the source-bound request ID varies.
                row["source_proposal_screen"] = {k: v for k, v in object_fields(row["source_proposal_screen"]).items()
                                                  if k != "request_key"}
                rows.append(row)
            payload["candidates"] = rows
            return payload

        self.assertEqual(scientific_payload(saved), scientific_payload(self.report))

    def test_temporary_history_unsupported_immutable_replay_and_crash_preservation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory))
            first = search.campaign(search.campaign_config(), history=history)
            saved = {p.relative_to(directory): p.read_bytes() for p in Path(directory).rglob("*") if p.is_file()}
            self.assertEqual(search.campaign(search.campaign_config(), history=history), first)
            recheck_history(history)
            self.assertEqual(saved, {p.relative_to(directory): p.read_bytes() for p in Path(directory).rglob("*") if p.is_file()})
            archive = object_fields(first["archival"])
            submission = history.get("submissions", str(archive["submission"]))
            self.assertEqual(len(array(submission["candidates"])), 11)
        with tempfile.TemporaryDirectory() as directory:
            history = History(Path(directory))
            with (patch.object(search, "candidate_evidence", side_effect=RuntimeError("probe crash")),
                  self.assertRaisesRegex(RuntimeError, "probe crash")):
                search.campaign(search.campaign_config(), history=history)
            self.assertEqual(len(list((history.root/"submissions").glob("*.json"))), 1)

    def test_cli_read_only_deterministic_gzip_no_overwrite_and_argument_guards(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch("scripts.search_generative_histories.campaign", return_value=copy.deepcopy(self.report)) as run:
                with redirect_stdout(io.StringIO()):
                    self.assertEqual(main([]), 0)
                self.assertIsNone(run.call_args.kwargs["history"])
                self.assertEqual(list(root.iterdir()), [])
                outputs = [root/"one.json.gz", root/"two.json.gz"]
                for path in outputs:
                    stream = io.StringIO()
                    with redirect_stdout(stream):
                        self.assertEqual(main(["--output", str(path)]), 0)
                    self.assertLess(len(stream.getvalue().encode()), 2048)
                self.assertEqual(outputs[0].read_bytes(), outputs[1].read_bytes())
                self.assertEqual(json.loads(gzip.decompress(outputs[0].read_bytes())), self.report)
                before = outputs[0].read_bytes()
                for args in (["--output", str(outputs[0])], ["--record-history"], ["--history-dir", directory],
                             ["--output", str(root/"bad.txt")]):
                    with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                        main(args)
                self.assertEqual(outputs[0].read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
