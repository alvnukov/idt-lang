from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from scripts.screen_primitives import main
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    PairKernel,
    PowerSum,
    aggregate_status,
    builtin_candidates,
    evaluate,
    load_json,
    parse_candidate,
    parse_limits,
    quadratic,
    replay,
    screen,
    tensor,
)


class PrimitiveScreenTests(unittest.TestCase):
    def test_square_control_has_no_counterexample_in_default_domain(self) -> None:
        checks = evaluate(builtin_candidates()["square"], Limits())
        self.assertEqual(len(checks), 5)
        self.assertTrue(all(c.status == "no_counterexample_within_bounds" for c in checks))
        self.assertEqual([c.checked for c in checks], [1, 4, 729, 20, 20])

    def test_fourth_power_fails_computed_third_difference(self) -> None:
        checks = {c.id: c for c in evaluate(builtin_candidates()["fourth"], Limits())}
        failed = checks["coefficient_third_difference"]
        self.assertEqual(failed.status, "counterexample")
        self.assertEqual(failed.checked, 1)
        self.assertIsNotNone(failed.witness)
        if failed.witness is not None:
            self.assertEqual(failed.witness["actual"], "36")
        self.assertEqual(checks["self_composition"].status, "unsupported")

    def test_non_psd_passes_local_grade_and_self_copies_but_not_reference(self) -> None:
        checks = evaluate(builtin_candidates()["non_psd"], Limits())
        self.assertTrue(all(c.status == "no_counterexample_within_bounds" for c in checks[:4]))
        failed = checks[-1]
        self.assertEqual(failed.status, "counterexample")
        self.assertEqual(failed.witness, {
            "actual": "-1/2", "required": ">=0", "inputs": {
                "reference_vector": ["-2", "1"],
                "reference_matrix": [["4", "-2"], ["-2", "1"]],
                "composite_event": [[0, 0], [1, 1]],
            },
        })

    def test_tiny_reference_domain_can_miss_known_counterexample(self) -> None:
        checks = evaluate(builtin_candidates()["non_psd"], Limits(reference_radius=1))
        self.assertEqual(checks[-1].status, "no_counterexample_within_bounds")
        self.assertEqual(checks[-1].checked, 6)

    def test_tensor_witness_recomputed_independently(self) -> None:
        q = Fraction
        matrix = ((q(1, 6), q(1, 3)), (q(1, 3), q(1, 6)))
        reference = ((q(4), q(-2)), (q(-2), q(1)))
        joint = tensor(matrix, reference)
        self.assertEqual(joint[0][3], matrix[0][1] * reference[0][1])
        self.assertEqual(sum(sum(row) for row in reference), 1)
        self.assertEqual(joint[0][0] + joint[0][3] + joint[3][0] + joint[3][3], q(-1, 2))
        self.assertEqual(quadratic(joint, (q(1), q(0), q(0), q(1))), q(-1, 2))

    def test_budget_exhaustion_is_not_success(self) -> None:
        checks = evaluate(builtin_candidates()["square"], Limits(max_cases=1))
        self.assertEqual(aggregate_status(checks), "inconclusive")
        self.assertEqual(checks[2].checked, 1)
        self.assertEqual(checks[2].planned, 729)
        self.assertEqual(checks[2].status, "inconclusive")

    def test_missing_composition_does_not_pass(self) -> None:
        checks = evaluate(PowerSum("power_two", 2, 2), Limits())
        self.assertEqual(aggregate_status(checks), "unsupported")
        self.assertEqual(checks[-1].checked, 0)

    def test_controls_do_not_depend_on_candidate_names(self) -> None:
        original = builtin_candidates()["non_psd"]
        self.assertIsInstance(original, PairKernel)
        if isinstance(original, PairKernel):
            self.assertEqual(evaluate(PairKernel("arbitrary_name", original.matrix), Limits()),
                             evaluate(original, Limits()))

    def test_non_unit_kernel_is_not_silently_normalized(self) -> None:
        candidate = PairKernel("nonunit", ((Fraction(2),),))
        checks = evaluate(candidate, Limits())
        self.assertEqual(checks[0].status, "counterexample")
        self.assertEqual(candidate.matrix[0][0], 2)

    def test_negative_event_is_found(self) -> None:
        candidate = PairKernel("negative", ((Fraction(-1), Fraction(0)),
                                            (Fraction(0), Fraction(2))))
        checks = evaluate(candidate, Limits())
        self.assertEqual(checks[0].status, "no_counterexample_within_bounds")
        self.assertEqual(checks[1].status, "counterexample")

    def test_aggregate_retains_blockers_and_failures(self) -> None:
        def check(status: str) -> Check:
            for item in evaluate(PowerSum("power_two", 2, 2), Limits(max_cases=1)):
                if item.status == status:
                    return item
            raise AssertionError(status)

        unsupported = check("unsupported")
        incomplete = check("inconclusive")
        failed = evaluate(builtin_candidates()["fourth"], Limits(max_cases=1))[2]
        self.assertEqual(aggregate_status(()), "inconclusive")
        self.assertEqual(aggregate_status((unsupported, incomplete)), "inconclusive")
        self.assertEqual(aggregate_status((failed, unsupported, incomplete)), "counterexample")

    def test_json_candidates_are_editable_not_prefilled_outputs(self) -> None:
        for candidate in builtin_candidates().values():
            self.assertEqual(parse_candidate(candidate.specification()), candidate)
        changed = builtin_candidates()["fourth"].specification()
        changed["exponent"] = 2
        self.assertEqual(evaluate(parse_candidate(changed), Limits())[2].status,
                         "no_counterexample_within_bounds")
        changed["expected_result"] = "pass"
        with self.assertRaises(ValueError):
            parse_candidate(changed)

    def test_malformed_candidates_fail_closed(self) -> None:
        with self.assertRaises(TypeError):
            parse_candidate(None)
        invalid: list[object] = [{}, {"family": "python", "code": "print(1)"}]
        for matrix in ([["1", "0"]], [["1", "2"], ["0", "1"]],
                       [[0.1]], [["1/0"]], [["NaN"]], [["1" * 40]]):
            invalid.append({"family": "pair_kernel", "id": "bad", "matrix": matrix})
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ValueError):
                parse_candidate(value)

    def test_bounds_are_strict(self) -> None:
        for number in (0, -1, 5001, True, 1.5):
            row = Limits().specification()
            row["max_cases"] = number
            with self.subTest(number=number), self.assertRaises(ValueError):
                parse_limits(row)

    def test_reports_are_deterministic_replayable_and_explicitly_unproved(self) -> None:
        report = screen(builtin_candidates()["non_psd"], Limits(max_cases=20))
        self.assertEqual(replay(report), report)
        self.assertEqual(report["empirical_status"], "not_tested")
        self.assertEqual(report["proof_status"], "not_attempted")
        untested = report["untested"]
        self.assertIsInstance(untested, list)
        if isinstance(untested, list):
            self.assertIn("standard_model", untested)
        for field, replacement in (("status", "proved"), ("source_sha256", {}),
                                   ("candidate_sha256", "000")):
            changed = dict(report)
            changed[field] = replacement
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "replay mismatch"):
                replay(changed)

    def test_json_reader_rejects_ambiguous_or_oversized_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            for content in ('{"a":1,"a":2}', '{"a":NaN}', '{"a":0.1}', ' ' * 131073):
                path.write_text(content, encoding="utf-8")
                with self.subTest(size=len(content)), self.assertRaises(ValueError):
                    load_json(path)

    def test_cli_save_replay_and_refuse_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            output = Path(directory) / "report.json"
            self.assertEqual(main(["--builtin", "non_psd", "--output", str(output)]), 1)
            original = output.read_bytes()
            self.assertEqual(main(["--replay", str(output)]), 1)
            self.assertEqual(main(["--builtin", "square", "--output", str(output)]), 2)
            self.assertEqual(output.read_bytes(), original)
            self.assertEqual(main(["--replay", str(output), "--max-cases", "1"]), 2)

    def test_cli_custom_candidate_and_incomplete_exit(self) -> None:
        with tempfile.TemporaryDirectory() as directory, contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            path = Path(directory) / "candidate.json"
            path.write_text(json.dumps(PowerSum("new_hypothesis", 2, 2).specification()), encoding="utf-8")
            self.assertEqual(main(["--candidate-file", str(path)]), 3)
            self.assertEqual(main(["--builtin", "square", "--max-cases", "1"]), 3)
            self.assertEqual(main(["--max-cases", "0"]), 2)
            self.assertEqual(main(["--builtin", "fourth", "--show-candidate"]), 0)


if __name__ == "__main__":
    unittest.main()
