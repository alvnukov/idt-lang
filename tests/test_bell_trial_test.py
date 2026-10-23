"""Independent oracles and false-rejection controls for the fixed-N local null."""

from __future__ import annotations

import copy
import io
import itertools
import json
import math
import os
import tempfile
import unittest
import zipfile
from contextlib import redirect_stderr, redirect_stdout
from fractions import Fraction as F
from pathlib import Path
from typing import cast
from unittest.mock import patch

from scripts import replay_hensen2015 as replay_script
from scripts.replay_hensen2015 import main
from theory_experiments import bell_trial_test as bell
from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import History, record_batch, semantic_report
from theory_experiments.primitive_screen import Limits, load_json, object_fields


def fixtures() -> list[object]:
    values = load_json(pipeline.ROOT / "data/bell_local_response_controls.json")
    assert isinstance(values, list)
    return cast(list[object], values)


def closed_form(n: int, k: int, q: F) -> F:
    return sum((math.comb(n, j) * q**j * (1-q)**(n-j) for j in range(k, n+1)), F())


def row(timestamp: str = "2015-06-26 17:24:12.119993", **changes: int) -> str:
    values = [1, 2, 5426350, 0, 5675700, 1, 0, 0, 10379, 10371, 0, 0, 0, 0, 0, 0]
    for key, value in changes.items():
        values[int(key[1:])-1] = value
    return timestamp + "," + ",".join(str(value) for value in values) + "\n"


def tree_distribution(probabilities: tuple[F, ...]) -> list[F]:
    distribution = [F(0)] * 4
    def visit(node: int, depth: int, wins: int, mass: F) -> None:
        if depth == 3:
            distribution[wins] += mass
            return
        p = probabilities[node]
        visit(2*node+1, depth+1, wins, mass*(1-p))
        visit(2*node+2, depth+1, wins+1, mass*p)
    visit(0, 0, 0, F(1))
    return distribution


class BellTrialTests(unittest.TestCase):
    def test_all_sixteen_tables_and_common_null_report(self) -> None:
        specs = fixtures()
        self.assertEqual(len(specs), 16)
        self.assertEqual(len({tuple(object_fields(spec)[key] for key in ("A0", "A1", "B0", "B1"))
                              for spec in specs}), 16)
        reports = pipeline.run_batch(specs)
        for result in reports:
            details = object_fields(result.report["scope"])
            prediction = object_fields(details["prediction"])
            self.assertIn(prediction["winning_cells"], (1, 3))
            self.assertEqual(prediction["conservative_class_cap"], str(bell.Q))
            self.assertEqual(details["shared_null_test_id"], bell.SHARED_NULL_TEST)
            self.assertEqual(result.report["status"], "no_counterexample_within_bounds")
            self.assertEqual(result.report["empirical_status"], "conditional_statistical_exclusion")
            self.assertEqual(details["candidate_verdict"], "unconditional_verdict_not_established")
            self.assertEqual(details["observation_origin"], "reviewed_count_replay_not_raw_reexecution")
            self.assertEqual(result.report["proof_status"], "not_attempted")
        self.assertEqual(len({json.dumps(object_fields(r.report["scope"])["assessment"], sort_keys=True)
                              for r in reports}), 1)

    def test_prediction_is_data_independent(self) -> None:
        candidate = bell.parse_bell_local_response(fixtures()[0])
        with patch.object(bell, "reviewed_counts", side_effect=AssertionError("data read")):
            self.assertEqual(bell.predict_local_null(candidate)["winning_cells"], 3)
        with patch.object(bell, "predict_local_null", side_effect=ValueError("prediction first")), patch.object(
                bell, "reviewed_counts", side_effect=AssertionError("data read")), self.assertRaisesRegex(
                    ValueError, "prediction first"):
            bell.evaluate_bell_local_response(candidate, Limits())

    def test_strict_schema_unknown_bridge_and_no_source_label_binding(self) -> None:
        good = object_fields(fixtures()[0])
        for key, value in (("A0", True), ("A1", 0), ("B0", "1"), ("B1", 2),
                           ("is_local", True), ("family", "source_theory")):
            changed = dict(good, **{key: value})
            with self.assertRaises((ValueError, TypeError)):
                bell.parse_bell_local_response(changed)
        for key in ("experiment", "bridge"):
            report = pipeline.run_batch([dict(good, **{key: "unbound"})])[0].report
            self.assertEqual(report["status"], "unsupported")
            self.assertEqual(report["empirical_status"], "not_tested")
        low = pipeline.run_batch([good], Limits(max_cases=1))[0].report
        self.assertEqual(low["status"], "inconclusive")
        self.assertEqual(low["empirical_status"], "not_tested")

    def test_exact_recurrence_against_integer_comb_oracle(self) -> None:
        for n in range(9):
            for q in (F(0), F(1, 3), F(3, 4), F(1)):
                self.assertEqual(bell.tail_row(n, q), tuple(closed_form(n, k, q) for k in range(n+2)))
        actual = bell.assess_counts(245, 196)
        p = F(str(object_fields(actual["tail"])["exact"]))
        self.assertEqual(p, closed_form(245, 196, bell.Q))
        self.assertEqual(object_fields(actual["tail"])["decimal_display"], "0.0391746435587900276")
        self.assertGreater(p, F(39, 1000))  # paper .039 is rounded, not literal <= .039
        self.assertLess(p, F(1, 20))
        self.assertEqual(actual["critical_wins"], 196)
        self.assertGreater(bell.tail_row(245, bell.Q)[195], F(1, 20))

    def test_threshold_independent_of_k_alpha_equality_and_invalid_inputs(self) -> None:
        self.assertEqual({bell.assess_counts(4, k, F(1, 2), F(5, 16))["critical_wins"]
                          for k in range(5)}, {3})
        self.assertEqual(bell.assess_counts(4, 3, F(1, 2), F(5, 16))["status"],
                         "conditional_statistical_exclusion")
        self.assertEqual(bell.assess_counts(4, 2, F(1, 2), F(5, 16))["status"], "not_excluded")
        for n, k, q, alpha in ((0, 0, F(1, 2), F(1, 20)), (513, 0, F(1, 2), F(1, 20)),
                                (4, -1, F(1, 2), F(1, 20)), (4, 5, F(1, 2), F(1, 20)),
                                (4, 2, F(-1), F(1, 20)), (4, 2, F(2), F(1, 20)),
                                (4, 2, F(1, 2), F(0)), (4, 2, F(1, 2), F(2)),
                                (True, 0, F(1, 2), F(1, 20))):
            with self.assertRaises(ValueError):
                bell.assess_counts(n, k, q, alpha)
        bell.tail_row(1, F(1))
        with self.assertRaises(ValueError):
            bell.tail_row(True, F(1))
        with self.assertRaises(ValueError):
            bell.tail_row(1, cast(F, 1))
        with self.assertRaises(ValueError):
            bell.tail_row(512, F(1, 10**14))
        self.assertLess(len(bell.number(bell.tail_row(266, F(1, 10**14))[266])["exact"]), 4000)
        with self.assertRaisesRegex(ValueError, "resource budget"):
            bell.tail_row(267, F(1, 10**14))

    def test_memory_tree_and_probabilistic_mixtures(self) -> None:
        q = F(3, 4)
        # Independently enumerate every depth-three binary tree whose seven
        # conditional win probabilities are selected from 0,q/2,q (3^7 trees).
        for probabilities in itertools.product((F(0), q/2, q), repeat=7):
            distribution = tree_distribution(probabilities)
            for k in range(4):
                self.assertLessEqual(sum(distribution[k:], F()), closed_form(3, k, q))
        # Random local-table mixtures remain <=3/4 under independent uniform settings.
        winning_cells = [cast(int, bell.predict_local_null(bell.parse_bell_local_response(spec))["winning_cells"])
                         for spec in fixtures()]
        weights = [F(index+1, 136) for index in range(16)]
        self.assertEqual(sum(weights), 1)
        self.assertLessEqual(sum((w*F(cells, 4) for w, cells in zip(weights, winning_cells)), F()), q)

    def test_fair_marginals_do_not_imply_joint_setting_contract(self) -> None:
        table = bell.BellLocalResponse("correlated_settings", bell.EXPERIMENT, bell.BRIDGE, 1, 1, 1, -1)
        cells = cast(list[dict[str, object]], bell.predict_local_null(table)["cells"])
        joint = {(0, 0): F(1, 2), (1, 1): F(1, 2)}
        self.assertEqual(sum(p for (a, _), p in joint.items() if a == 0), F(1, 2))
        self.assertEqual(sum(p for (_, b), p in joint.items() if b == 0), F(1, 2))
        self.assertEqual(sum((joint.get((cast(int, c["a"]), cast(int, c["b"])), F())
                              for c in cells if c["win"]), F()), 1)

    def test_cap_weakening_and_optional_stopping_are_not_hidden(self) -> None:
        self.assertLess(bell.tail_row(245, F(3, 4))[196], bell.tail_row(245, bell.Q)[196])
        weaker = bell.assess_counts(245, 196, F(4, 5))
        self.assertEqual(weaker["status"], "not_excluded")
        # Exact null mass of ever crossing repeated fixed-N boundaries exceeds alpha.
        alpha, q = F(1, 5), F(3, 4)
        surviving = {0: F(1)}
        rejected = F()
        for n in range(1, 31):
            next_mass: dict[int, F] = {}
            for k, mass in surviving.items():
                for outcome, probability in ((0, 1-q), (1, q)):
                    count = k+outcome
                    next_mass[count] = next_mass.get(count, F()) + mass*probability
            surviving = {}
            for count, mass in next_mass.items():
                if closed_form(n, count, q) <= alpha:
                    rejected += mass
                else:
                    surviving[count] = mass
        self.assertGreater(rejected, alpha)
        self.assertIn("fixed_data_independent_N_not_optional_stopping", bell.ASSUMPTIONS)
        self.assertTrue(any("two_sigma" in item for item in bell.LIMITATIONS))

    def test_window_marker_and_readout_boundaries_no_click_is_retained(self) -> None:
        valid = tuple(int(x) for x in row().strip().split(",")[1:])
        self.assertEqual(bell.filter_reasons(valid), [])
        for index, left, right, offset in ((2, 5426350, 5426350+52450, 0),
                                           (4, 5425700, 5425700+52450, 250000)):
            for value, accepted in ((left-1, False), (left, True), (right-1, True), (right, False)):
                values = list(valid)
                values[index] = value+offset
                self.assertEqual(not bell.filter_reasons(tuple(values)), accepted)
        for marker, accepted in ((0, True), (1, False), (250, False), (251, True)):
            values = list(valid)
            values[14] = marker
            self.assertEqual(not bell.filter_reasons(tuple(values)), accepted)
        self.assertEqual([bell.readout_sign(t) for t in (0, 10620, 10621, 14320, 14321)], [-1, -1, 1, 1, -1])
        reduced = bell.reduce_records(row())
        self.assertEqual((reduced["N"], reduced["K"]), (1, 1))
        records = cast(list[dict[str, object]], reduced["records"])
        self.assertEqual((records[0]["x"], records[0]["y"]), (-1, -1))
        self.assertEqual(records[0]["source_fields"], row().strip().split(","))

    def test_filter_failures_all_retained_and_input_errors_not_physics(self) -> None:
        bad_herald = row(c4=1)
        bad_marker = row("2015-06-26 17:24:13.119993", c15=250)
        bad_excite = row("2015-06-26 17:24:14.119993", c13=1)
        reduced = bell.reduce_records(bad_herald+bad_marker+bad_excite)
        self.assertEqual((reduced["released_rows"], reduced["N"]), (3, 0))
        self.assertEqual(len(cast(list[object], reduced["records"])), 3)
        for malformed in ("", row()+row(), row("2015-06-26 17:24:13.119993")+row(),
                          row().replace(",10379,", ",nan,"), row(c7=2), row(c11=-1),
                          row().replace("2015-06-26", "2015-99-99"), row().replace(",0,0\n", ",0\n")):
            with self.assertRaises(ValueError):
                bell.reduce_records(malformed)
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "missing.txt"
            with self.assertRaises(OSError):
                bell.replay(missing)
            missing.write_bytes(b"x" * bell.RAW_SIZE)
            with self.assertRaisesRegex(ValueError, "digest"):
                bell.replay(missing)

    def test_registry_recipe_count_tampering_and_unknown_bounds_do_not_default_to_zero(self) -> None:
        registry = bell.reviewed_counts()
        cases: tuple[tuple[str, dict[str, object]], ...] = (("recipe", {}), ("reviewed_counts", {}), ("raw", {}))
        for key, value in cases:
            changed = copy.deepcopy(registry)
            changed[key] = value
            with patch.object(bell, "load_json", return_value=changed), self.assertRaises(ValueError):
                bell.reviewed_counts()
        provenance = object_fields(registry["provenance"])
        self.assertIn("not verified", str(provenance["fixed_N_provenance"]))
        self.assertIn("not a certified", str(provenance["tau_status"]))

    def test_cache_replay_history_and_source_change_guards(self) -> None:
        spec = fixtures()[0]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = pipeline.run_batch([spec], cache_dir=root / "cache")
            with patch.object(pipeline, "compute", side_effect=AssertionError("cache hit executed")):
                second = pipeline.run_batch([spec], cache_dir=root / "cache")
            self.assertTrue(second[0].reused)
            self.assertEqual(first[0].report, second[0].report)
            assert first[0].artifact is not None
            self.assertEqual(pipeline.replay_artifact(first[0].artifact), first[0].report)
            record_batch([spec], history=History(root / "history"))
            self.assertEqual(semantic_report(first[0].report), semantic_report(second[0].report))
            with patch.object(bell, "source_hashes", return_value={}), self.assertRaisesRegex(ValueError, "since import"):
                pipeline.run_batch([spec], cache_dir=root / "cache")
        original = pipeline.provenance()
        with patch.object(pipeline, "provenance", side_effect=[original, {}]), self.assertRaisesRegex(
                ValueError, "during batch"):
            pipeline.run_batch([spec], fresh=True)
        with patch.object(bell, "source_hashes", side_effect=[bell.LOADED_SOURCE_HASHES, {}]), self.assertRaisesRegex(
                ValueError, "since import"):
            bell.evaluate_bell_local_response(bell.parse_bell_local_response(spec), Limits())

    def test_raw_assessment_finishes_before_final_source_guard(self) -> None:
        reduced = dict(object_fields(bell.reviewed_counts()["reviewed_counts"]))
        original = bell.assess_counts
        def assessment_with_edit(n: int, k: int) -> dict[str, object]:
            hashes.return_value = {}
            return original(n, k)
        with patch.object(bell, "read_pinned_raw", return_value=b"ignored"), patch.object(
                bell, "reduce_records", return_value=reduced), patch.object(
                bell, "source_hashes", return_value=bell.LOADED_SOURCE_HASHES) as hashes, patch.object(
                bell, "assess_counts", side_effect=assessment_with_edit), self.assertRaisesRegex(ValueError, "during replay"):
            bell.replay(Path("unused"))

    def test_opt_in_fetch_pins_archive_member_and_refuses_overwrite(self) -> None:
        import hashlib
        content = b"source-only-test"
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            archive.writestr("bell_open_data.txt", content)
            archive.writestr("../never-extracted.py", b"raise RuntimeError('never execute')")
        packed = buffer.getvalue()
        with tempfile.TemporaryDirectory() as directory, patch.object(
                replay_script, "ARCHIVE_SIZE", len(packed)), patch.object(
                replay_script, "ARCHIVE_SHA256", hashlib.sha256(packed).hexdigest()), patch.object(
                replay_script, "RAW_SIZE", len(content)), patch.object(
                replay_script, "RAW_SHA256", hashlib.sha256(content).hexdigest()), patch(
                "scripts.replay_hensen2015.urllib.request.urlopen", return_value=io.BytesIO(packed)) as download:
            target = Path(directory) / "data.txt"
            replay_script.fetch_release(target)
            self.assertEqual(target.read_bytes(), content)
            self.assertEqual([p.name for p in Path(directory).iterdir()], ["data.txt"])
            download.assert_called_once_with(replay_script.MIRROR_URL, timeout=30)
            with self.assertRaisesRegex(ValueError, "raw file"):
                replay_script.fetch_release(target)
            self.assertEqual(target.read_bytes(), content)

    def test_cli_refuses_overwrite_and_deterministic_output(self) -> None:
        report = {"execution_status": "complete", "assessment": bell.assess_counts(4, 3)}
        with tempfile.TemporaryDirectory() as directory, patch("scripts.replay_hensen2015.replay", return_value=report):
            output = Path(directory) / "report.json"
            argv = ["--raw-file", "unused", "--output", str(output)]
            with redirect_stdout(io.StringIO()):
                self.assertEqual(main(argv), 0)
                first = output.read_bytes()
                self.assertEqual(main(argv), 0)
                self.assertEqual(output.read_bytes(), first)
            output.write_text("do not overwrite")
            with redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(main(argv), 2)
            self.assertIn("not physics rejection", errors.getvalue())
            self.assertEqual(output.read_text(), "do not overwrite")

    @unittest.skipUnless(os.environ.get("IDT_HENSEN2015_RAW"), "set IDT_HENSEN2015_RAW for pinned released CSV")
    def test_actual_pinned_released_csv_without_optional_dependencies(self) -> None:
        report = bell.replay(Path(os.environ["IDT_HENSEN2015_RAW"]))
        reduced = object_fields(report["reduction"])
        self.assertEqual({k: reduced[k] for k in ("released_rows", "herald", "also_markers", "N", "K", "matrix")},
                         bell.reviewed_counts()["reviewed_counts"])
        self.assertEqual(len(cast(list[object], reduced["records"])), 4746)
        self.assertEqual(len(cast(list[object], reduced["accepted_row_ids"])), 245)
        self.assertEqual(report["observation_origin"], "pinned_released_candidate_records_reexecuted")


if __name__ == "__main__":
    unittest.main()
