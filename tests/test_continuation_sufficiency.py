"""Finite continuation certificates, independent replay, and strict boundaries."""

from __future__ import annotations

import contextlib
import copy
import hashlib
import io
import itertools
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import check_continuation_sufficiency as cli
from theory_experiments import continuation_sufficiency as checker
from theory_experiments.primitive_screen import canonical_json, object_fields


def model(transitions: list[list[int]], readouts: list[str], adapter: list[int]) -> dict[str, object]:
    return {"schema": checker.MODEL_SCHEMA, "transitions": transitions,
            "readouts": [[x] for x in readouts], "adapter": adapter}


def certificate(value: object) -> dict[str, object]:
    return object_fields(checker.analyze(value)["certificate"])


def bind(value: object, cert: dict[str, object]) -> dict[str, object]:
    return {**cert, "model_sha256": hashlib.sha256(
        canonical_json(checker.normalize_model(value)).encode()).hexdigest()}


class ContinuationSufficiencyTests(unittest.TestCase):
    def test_single_state_and_zero_actions(self) -> None:
        for value in (model([], ["-2/3"], [42]), model([[0]], ["3"], [-42])):
            report = checker.analyze(value)
            self.assertEqual(report["status"], "predictively_sufficient_for_declared_words")
            self.assertEqual(report["adapter_update"], {"status": "stable"})
            self.assertTrue(checker.verify_certificate(value, report["certificate"]))

    def test_zero_actions_and_empty_word_counterexample(self) -> None:
        value = model([], ["-2", "7/3"], [0, 0])
        cert = certificate(value)
        self.assertEqual(cert["word"], [])
        self.assertEqual(cert["origin"], [0, 1])
        self.assertEqual(checker.analyze(value)["status"], "observable_counterexample")
        self.assertTrue(checker.verify_certificate(value, cert))

    def test_rational_vectors_canonicalize_without_probability_assumptions(self) -> None:
        value = {"schema": checker.MODEL_SCHEMA, "transitions": [[1, 0]],
                 "readouts": [["-4/6", "200"], ["-2/3", "200/1"]], "adapter": [0, 0]}
        normalized = checker.normalize_model(value)
        self.assertEqual(normalized["readouts"], [["-2/3", "200"], ["-2/3", "200"]])
        self.assertTrue(checker.verify_certificate(value, certificate(normalized)))

    def test_positive_cycle_and_claim_boundary(self) -> None:
        value = checker.demo_models()["constant_readout_cycle"]
        report = checker.analyze(value)
        self.assertEqual(report["status"], "predictively_sufficient_for_declared_words")
        self.assertEqual(report["candidate_verdict"], "unchanged")
        self.assertEqual(report["proof_status"], "concrete_certificate_not_lean_checked")
        self.assertEqual(report["empirical_status"], "not_tested")
        self.assertEqual(report["scope"], checker.SCOPE)
        pairs = object_fields(report["certificate"])["pairs"]
        assert isinstance(pairs, list)
        self.assertEqual(len(pairs), 9)

    def test_delayed_reversible_cycles_have_no_arbitrary_depth_cutoff(self) -> None:
        for delay in (0, 1, 2, 7, 30, 61):
            size = delay + 3
            value = model([[*range(1, size), 0]], ["0"] * (size - 1) + ["1"],
                          [0, 0, *range(1, size - 1)])
            cert = certificate(value)
            self.assertEqual(cert["origin"], [0, 1])
            self.assertEqual(cert["word"], [0] * (delay + 1))
            self.assertTrue(checker.verify_certificate(value, cert))

    def test_structural_update_failure_is_not_observable_failure(self) -> None:
        value = checker.demo_models()["predictive_pass_update_failure"]
        report = checker.analyze(value)
        self.assertEqual(report["status"], "predictively_sufficient_for_declared_words")
        self.assertEqual(report["adapter_update"], {"status": "structural_update_failure",
                         "pair": [0, 1], "action": 0, "successors": [2, 3]})
        self.assertEqual(report["candidate_verdict"], "unchanged")

    def test_phase_flip_supplied_fixture(self) -> None:
        value = checker.demo_models()["three_state_phase_flip"]
        report = checker.analyze(value)
        self.assertEqual(report["status"], "observable_counterexample")
        self.assertEqual(object_fields(report["certificate"])["word"], [0])
        self.assertEqual(object_fields(report["certificate"])["origin"], [0, 1])

    def test_order_sensitive_two_action_witness(self) -> None:
        value = model([[0, 2, 2, 3], [0, 0, 3, 3]], ["0", "0", "0", "1"], [0, 0, 1, 2])
        cert = certificate(value)
        self.assertEqual(cert["word"], [0, 1])
        self.assertFalse(checker.verify_certificate(value, {**cert, "word": [1, 0]}))

    def test_all_resource_bounds_are_supported(self) -> None:
        value = {"schema": checker.MODEL_SCHEMA, "transitions": [list(range(64)) for _ in range(16)],
                 "readouts": [["-999999999999/999999999999"] * 16 for _ in range(64)],
                 "adapter": [-(2**31), 2**31 - 1, *range(62)]}
        self.assertTrue(checker.verify_certificate(value, certificate(value)))
        constant = model([list(range(64))] * 16, ["0"] * 64, [0] * 64)
        cert = certificate(constant)
        pairs = cert["pairs"]
        assert isinstance(pairs, list)
        self.assertEqual(len(pairs), 4096)
        self.assertTrue(checker.verify_certificate(constant, cert))

    def test_malformed_models_are_input_errors(self) -> None:
        good = model([[1, 0]], ["0", "0"], [0, 0])
        invalid: list[object] = [None, [], {**good, "extra": 0},
            {key: val for key, val in good.items() if key != "adapter"},
            {**good, "schema": "future"}, {**good, "readouts": []},
            {**good, "readouts": [["0"]] * 65}, {**good, "readouts": [["0"] * 17] * 2},
            {**good, "readouts": [[], []]}, {**good, "readouts": [["0"], ["0", "0"]]},
            {**good, "transitions": [[0]]}, {**good, "transitions": [[0, 2]]},
            {**good, "transitions": [[0, -1]]}, {**good, "transitions": [[0, True]]},
            {**good, "transitions": [[0, 1.0]]}, {**good, "transitions": [[0, 1]] * 17},
            {**good, "transitions": {"0": [0, 1]}}, {**good, "transitions": [[0, None]]},
            {**good, "adapter": [0]}, {**good, "adapter": [False, 0]},
            {**good, "adapter": [0.0, 0]}, {**good, "adapter": [2**31, 0]},
            {**good, "adapter": [-(2**31) - 1, 0]}]
        for fraction in (0, 0.5, True, "1/0", "1.0", "NaN", "1/01", "1" * 13):
            invalid.append({**good, "readouts": [[fraction], ["0"]]})
        for value in invalid:
            with self.subTest(value=value), self.assertRaises((ValueError, TypeError)):
                checker.analyze(value)

    def test_certificate_domains_and_exact_fields(self) -> None:
        value = model([[0, 1]], ["0", "0"], [0, 0])
        good = certificate(value)
        invalid: list[object] = [None, {}, {**good, "schema": "future"},
            {**good, "kind": "future"}, {**good, "extra": 0},
            {**good, "pairs": []}, {**good, "pairs": [[0, 0]]},
            {**good, "pairs": [[0, 0], [0, 1], [1, 0], [1, 1], [0, 0]]},
            {**good, "pairs": [[0, 0], [0, 1], [1, 0], [1, 2]]},
            {**good, "pairs": [[0, 0], [0, 1], [1, 0], [1, True]]},
            {**good, "pairs": [[0, 0], [0, 1], [1, 0], [1, -1]]},
            {**good, "model_sha256": "stale"}]
        for cert in invalid:
            with self.subTest(cert=cert):
                self.assertFalse(checker.verify_certificate(value, cert))
        self.assertFalse(checker.verify_certificate({}, good))

    def test_positive_certificate_checks_successor_closure(self) -> None:
        value = checker.demo_models()["predictive_pass_update_failure"]
        cert = certificate(value)
        pairs = cert["pairs"]
        assert isinstance(pairs, list)
        self.assertIn([2, 3], pairs)
        cert["pairs"] = [pair for pair in pairs if pair != [2, 3]]
        self.assertFalse(checker.verify_certificate(value, cert))

    def test_full_model_digest_binds_readouts_actions_adapter_and_order(self) -> None:
        value = model([[0, 2, 2, 3], [0, 0, 3, 3]], ["0", "0", "0", "1"], [0, 0, 1, 2])
        cert = certificate(value)
        alternatives = [model([[0, 2, 2, 3], [0, 0, 3, 3]], ["0", "0", "0", "2"], [0, 0, 1, 2]),
                        model([[0, 2, 2, 3], [0, 0, 3, 3]], ["0", "0", "0", "1"], [1, 1, 0, 2]),
                        model([[0, 0, 3, 3], [0, 2, 2, 3]], ["0", "0", "0", "1"], [0, 0, 1, 2]),
                        model([[0, 2, 2, 3], [0, 0, 2, 3]], ["0", "0", "0", "1"], [0, 0, 1, 2])]
        for alternative in alternatives:
            self.assertFalse(checker.verify_certificate(alternative, cert))

    def test_rebinding_digest_cannot_hide_semantic_tampering(self) -> None:
        value = model([], ["0", "0"], [0, 0])
        positive = certificate(value)
        changed = model([], ["0", "1"], [0, 0])
        self.assertFalse(checker.verify_certificate(changed, bind(changed, positive)))
        negative = certificate(changed)
        self.assertFalse(checker.verify_certificate(value, bind(value, negative)))
        unequal_adapter = model([], ["0", "1"], [0, 1])
        self.assertFalse(checker.verify_certificate(unequal_adapter, bind(unequal_adapter, negative)))

    def test_word_certificate_rejects_invalid_origin_or_word(self) -> None:
        value = checker.demo_models()["three_state_phase_flip"]
        cert = certificate(value)
        changes: tuple[dict[str, object], ...] = (
            {"origin": [0, 2]}, {"origin": [0, 3]}, {"origin": [True, 1]},
            {"origin": [0]}, {"word": []}, {"word": [1]}, {"word": [False]},
            {"word": [0.0]}, {"word": [0] * 10}, {"word": [0, None]})
        for change in changes:
            self.assertFalse(checker.verify_certificate(value, {**cert, **change}))

    def test_verification_does_not_call_search_or_analysis(self) -> None:
        for value in checker.demo_models().values():
            cert = certificate(value)
            with (patch.object(checker, "_search", side_effect=AssertionError("search used")),
                  patch.object(checker, "analyze", side_effect=AssertionError("analysis used"))):
                self.assertTrue(checker.verify_certificate(value, cert))

    def test_genuine_long_witness_is_outside_limits_not_false_evidence(self) -> None:
        value = checker.demo_models()["three_state_phase_flip"]
        cert = {**certificate(value), "word": [0] * 11}
        # Replay independently: eleven phase flips genuinely distinguish these
        # states, although this N=3 schema accepts at most N²=9 action letters.
        left, right = 0, 1
        transition = [0, 2, 1]
        readouts = ["4/5", "4/5", "0"]
        for _ in range(11):
            left, right = transition[left], transition[right]
        self.assertNotEqual(readouts[left], readouts[right])
        self.assertTrue(checker.verify_certificate(value, {**cert, "word": [0] * 9}))
        self.assertFalse(checker.verify_certificate(value, cert))
        with (patch.object(cli, "load_json", side_effect=[value, cert]),
              contextlib.redirect_stdout(io.StringIO()) as output,
              contextlib.redirect_stderr(io.StringIO()) as errors):
            self.assertEqual(cli.main(["--model-file", "model.json", "--certificate-file", "cert.json"]), 2)
        self.assertEqual(output.getvalue(), "")
        self.assertIn("certificate not accepted (invalid or outside supported limits)", errors.getvalue())
        self.assertIn("not candidate rejection", errors.getvalue())
        self.assertNotIn("candidate_verdict", errors.getvalue())

    def test_analyzer_treats_invalid_generated_evidence_as_checker_error(self) -> None:
        value = model([], ["0"], [0])
        with patch.object(checker, "_search", return_value={}), self.assertRaisesRegex(ValueError, "checker error"):
            checker.analyze(value)
        with patch.object(checker, "verify_certificate", return_value=False), self.assertRaisesRegex(ValueError, "checker error"):
            checker.analyze(value)

    def test_exhaustive_two_state_models_against_bounded_word_enumeration(self) -> None:
        # Independent oracle: enumerate all words through N²-1, then replay from
        # every kernel pair; no visited-pair search or certificate logic reused.
        for flat, labels, outputs in itertools.product(itertools.product(range(2), repeat=4),
                                                       itertools.product(range(2), repeat=2),
                                                       itertools.product(range(2), repeat=2)):
            actions = [list(flat[:2]), list(flat[2:])]
            sufficient = True
            for length in range(4):
                for word in itertools.product(range(2), repeat=length):
                    for left, right in itertools.product(range(2), repeat=2):
                        if labels[left] != labels[right]:
                            continue
                        for action in word:
                            left, right = actions[action][left], actions[action][right]
                        if outputs[left] != outputs[right]:
                            sufficient = False
            value = model(actions, list(map(str, outputs)), list(labels))
            self.assertEqual(checker.analyze(value)["status"] == "predictively_sufficient_for_declared_words",
                             sufficient)

    def test_cli_determinism_no_writes_or_rejection_exit(self) -> None:
        from unittest.mock import mock_open
        value = checker.demo_models()["three_state_phase_flip"]
        outputs: list[str] = []
        for _ in range(2):
            with (patch.object(cli, "load_json", return_value=value),
                  patch("builtins.open", mock_open()) as opened,
                  patch.object(Path, "write_text", side_effect=AssertionError("write")),
                  patch.object(Path, "write_bytes", side_effect=AssertionError("write")),
                  contextlib.redirect_stdout(io.StringIO()) as output):
                self.assertEqual(cli.main(["--model-file", "not-read.json"]), 0)
                # Path.read_bytes uses io.open; builtins.open would indicate new IO.
                opened.assert_not_called()
            outputs.append(output.getvalue())
        self.assertEqual(outputs[0], outputs[1])
        self.assertIn('"observable_counterexample"', outputs[0])
        self.assertIn('"candidate_verdict":"unchanged"', outputs[0])

    def test_cli_strict_json_and_external_certificate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path, cert_path = Path(directory) / "model.json", Path(directory) / "cert.json"
            value = checker.demo_models()["three_state_phase_flip"]
            path.write_text(canonical_json(value))
            cert_path.write_text(canonical_json(certificate(value)))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(cli.main(["--model-file", str(path), "--certificate-file", str(cert_path)]), 0)
            for raw in ('null', '{"schema":"x","schema":"y"}', '{"x":0.5}', '{"x":NaN}', "[" * 1100):
                path.write_text(raw)
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(cli.main(["--model-file", str(path)]), 2)
            path.write_text(canonical_json(value))
            for raw_cert in ({}, None, {**certificate(value), "word": []}):
                cert_path.write_text(canonical_json(raw_cert))
                with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(cli.main(["--model-file", str(path), "--certificate-file", str(cert_path)]), 2)
            path.write_text(" " * 131073)
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(cli.main(["--model-file", str(path)]), 2)

    def test_cli_demo_and_incompatible_arguments(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(cli.main(["--demo"]), 0)
        self.assertIn("predictive_pass_update_failure", output.getvalue())
        for argv in ([], ["--demo", "--model-file", "x"], ["--demo", "--certificate-file", "x"]):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                cli.main(argv)
            self.assertEqual(error.exception.code, 2)

    def test_source_provenance_guard(self) -> None:
        values = checker.demo_models()
        for name in ("LOADED_SOURCE_HASHES", "LOADED_MODULE_SHA256", "LOADED_HELPER_SHA256"):
            with patch.object(cli, name, "stale"), self.assertRaisesRegex(ValueError, "since import"):
                cli.evidence(values)
        before = copy.deepcopy(cli.LOADED_SOURCE_HASHES)
        with (patch.object(cli, "_source_hashes", side_effect=[before, {}]),
              self.assertRaisesRegex(ValueError, "during analysis")):
            cli.evidence(values)


if __name__ == "__main__":
    unittest.main()
