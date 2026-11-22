"""Exact rank witnesses, conditional-resource boundaries, and interval controls."""

from __future__ import annotations

import copy
import hashlib
import unittest
from dataclasses import replace
from fractions import Fraction as F
from itertools import permutations, product
from math import prod
from pathlib import Path
from unittest.mock import patch

from theory_experiments import prepare_measure_cut as adapter
from theory_experiments.primitive_screen import Limits, aggregate_status


def spec(table, *, dimension=2, model="classical", seed=False, basis="unconditional"):
    return {"id": "finite_cut", "family": "prepare_measure_cut", "event": "joint_ref",
            "event_basis": basis, "memory": {"model": model, "dimension": dimension,
                                             "shared_classical_seed": seed},
            "intervals": [[[str(x) for x in v] if isinstance(v, tuple) else [str(v), str(v)]
                           for v in row] for row in table]}


def ident(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def evaluate(raw, max_cases=2, **kwargs):
    checks, scope = adapter.evaluate_prepare_measure_cut(
        adapter.parse_prepare_measure_cut(raw), Limits(max_cases=max_cases), **kwargs)
    return checks, scope


def exact_report_number(value):
    if "0x" in value:
        a, b = value.split("/")
        return F(int(a, 16), int(b, 16))
    return F(value)


def determinant(matrix):
    """Independent Leibniz oracle for the small minors under test."""
    n = len(matrix)
    return sum(((-1)**sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
                * prod(matrix[i][p[i]] for i in range(n))
                for p in permutations(range(n))), F(0))


class PrepareMeasureCutTests(unittest.TestCase):
    def verify_minor(self, matrix, check):
        self.assertEqual(check.status, "counterexample")
        inputs = check.witness["inputs"]
        self.assertEqual(inputs["method"], "fraction_free_exact_rank")
        rows, cols = inputs["rows"], inputs["columns"]
        n = inputs["rank_bound"] + 1
        self.assertEqual(len(set(rows)), n)
        self.assertEqual(len(set(cols)), n)
        self.assertEqual(len(rows), n)
        self.assertEqual(len(cols), n)
        exact = determinant([[F(matrix[i][j]) for j in cols] for i in rows])
        self.assertNotEqual(exact, 0)
        self.assertEqual(exact_report_number(inputs["determinant_in_listed_order"]), exact)
        self.assertEqual(check.witness["actual"], "-1")

    def test_classical_factorization_generated_table_is_never_confirmed(self):
        states = [(F(1, 3), F(2, 3)), (1, 0), (F(5, 8), F(3, 8))]
        effects = [(0, 1), (F(2, 3), F(3, 4)), (0, F(2, 5))]
        table = [[sum(p*e for p, e in zip(s, f)) for f in effects] for s in states]
        checks, result = evaluate(spec(table))
        self.assertEqual([c.status for c in checks], ["inconclusive", "inconclusive"])
        self.assertEqual(result["rank"]["exact_rank"], 2)
        self.assertIsNone(checks[0].witness)
        self.assertTrue(result["necessary_conditions_only"])
        self.assertEqual(result["stop_reason"], "necessary_conditions_only_no_contradiction")
        self.assertEqual((result["scientific_status"], result["proof_status"], result["empirical_status"]),
                         ("unassessed", "not_attempted", "not_tested"))
        self.assertEqual(result["interval_coverage_status"], "declared_outer_bounds_not_verified")
        self.assertEqual(result["cut_sufficiency_status"], "declared_model_premise_not_verified")
        self.assertEqual(result["rejection_scope"], adapter.SCOPE)
        small, _ = evaluate(spec(table, dimension=1))
        self.verify_minor(table, small[0])

    def test_exact_qubit_bloch_factorization_uses_hermitian_rank_four(self):
        states = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1, 0, 0)]
        effects = states[:]
        table = [[F(1 + sum(x*y for x, y in zip(s, e)), 2) for e in effects] for s in states]
        checks, scope = evaluate(spec(table, model="quantum"))
        self.assertEqual(aggregate_status(checks), "inconclusive")
        self.assertEqual(scope["rank"]["rank_bound"], 4)
        self.assertEqual(scope["rank"]["exact_rank"], 4)
        checks, result = evaluate(spec(table, dimension=3))
        self.assertEqual(result["rank"]["rank_bound"], 3)
        self.verify_minor(table, checks[0])

    def test_nonprincipal_minor_and_signed_fraction_free_index_order(self):
        table = [[0, 0, 0, 0], [0, 0, F(1, 3), 0], [0, 0, 0, F(2, 5)], [0, 0, 0, 0]]
        checks, scope = evaluate(spec(table, dimension=1))
        self.verify_minor(table, checks[0])
        inputs = checks[0].witness["inputs"]
        self.assertEqual(inputs["rows"], [1, 2])
        self.assertEqual(inputs["columns"], [2, 3])
        self.assertEqual(inputs["determinant_in_listed_order"], "2/15")
        self.assertIsNone(scope["rank"]["exact_rank"])

    def test_exhaustive_three_square_binary_elimination_against_minor_oracle(self):
        n = 3
        indices = range(n)
        for entries in product((0, 1), repeat=n*n):
            table = tuple(tuple(F(entries[n*i+j]) for j in indices) for i in indices)
            full = determinant(table)
            minor2 = any(determinant([[table[i][j] for j in (a, b)] for i in (r, s)])
                         for r in indices for s in range(r+1, n)
                         for a in indices for b in range(a+1, n)) if not full else True
            rank = 3 if full else 2 if minor2 else 1 if any(entries) else 0
            for bound in (1, 2, 3):
                lower, certificate = adapter._rank_or_minor(table, bound, lambda: None)
                self.assertEqual(lower, min(rank, bound+1))
                self.assertEqual(certificate is not None, rank > bound)
                if certificate:
                    exact = determinant([[table[i][j] for j in certificate["columns"]]
                                         for i in certificate["rows"]])
                    self.assertEqual(exact_report_number(certificate["determinant_in_listed_order"]), exact)
                    self.assertNotEqual(exact, 0)

    def test_interval_robust_dominance_and_overlap_at_the_exact_boundary(self):
        robust = [[(F(4, 5), F(9, 10)) if i == j else (0, F(1, 10))
                   for j in range(3)] for i in range(3)]
        checks, scope = evaluate(spec(robust))
        rank, trace = checks
        self.assertEqual(rank.status, "counterexample")
        self.assertEqual(trace.status, "inconclusive")
        self.assertFalse(scope["saturated_diagonal"]["eligible"])
        inputs = rank.witness["inputs"]
        margins = [row[i][0] - sum(hi for j, (_, hi) in enumerate(row) if j != i)
                   for i, row in enumerate(robust)]
        self.assertEqual(inputs["certified_rank_lower_bound"], 3)
        self.assertEqual(inputs["diagonal_lower_minus_off_diagonal_upper_sums"], list(map(str, margins)))
        touching = [[(F(1, 2), 1) if i == j else (0, F(1, 2)) for j in range(2)] for i in range(2)]
        checks, details = evaluate(spec(touching, dimension=1))
        self.assertEqual(aggregate_status(checks), "inconclusive")
        self.assertIsNone(checks[0].witness)  # All cells can simultaneously be 1/2.
        self.assertIsNone(details["rank"]["rank_lower_bound"])

    def test_saturated_trace_uses_upper_box_only_and_strict_exact_inequality(self):
        tie = [[(1, 1) if i == j else (0, F(1, 4)) for j in range(3)] for i in range(3)]
        for model, seed in product(("classical", "quantum"), (False, True)):
            with self.subTest(model=model, seed=seed):
                checks, scope = evaluate(spec(tie, model=model, seed=seed))
                self.assertEqual(checks[1].status, "inconclusive")
                self.assertIsNone(checks[1].witness)
                self.assertEqual(scope["saturated_diagonal"]["scaled_upper_gap"], "0")
                strict = copy.deepcopy(tie)
                strict[0][1] = (0, F(249999999999, 10**12-1))
                checks, scope = evaluate(spec(strict, model=model, seed=seed))
                trace = checks[1]
                self.assertEqual(trace.status, "counterexample")
                upper = sum(F(hi) for row in strict for _, hi in row)
                self.assertLess(2*upper-9, 0)
                self.assertEqual(exact_report_number(trace.witness["actual"]), 2*upper-9)
                self.assertEqual(exact_report_number(trace.witness["inputs"]["entry_upper_sum"]), upper)
                widened = copy.deepcopy(strict)
                widened[0][0] = (F(999, 1000), 1)
                checks, scope = evaluate(spec(widened, model=model, seed=seed))
                self.assertFalse(scope["saturated_diagonal"]["eligible"])
                self.assertIsNone(checks[1].witness)

    def test_accepted_only_loss_control_and_joint_probability_are_not_synonyms(self):
        # Exact lossy qubit control: for |psi_i>=(2i,1)/sqrt(1+4i²)
        # with successful Kraus [[1,-2j],[0,1]]/5, the raw second-output
        # probability is independent of j. Success-only divides by the
        # sum of raw outcome probabilities and can make a rank-three table.
        joint = [[F(1, 25*(1 + 4*i*i)) for _ in range(3)] for i in range(3)]
        conditioned = [[F(1, 1 + 4*(i-j)**2) for j in range(3)] for i in range(3)]
        for model in ("classical", "quantum"):
            checks, details = evaluate(spec(conditioned, model=model, basis="accepted_only"))
            self.assertEqual(aggregate_status(checks), "unsupported")
            self.assertEqual([c.checked for c in checks], [0, 0])
            self.assertTrue(all(c.witness is None for c in checks))
            self.assertIsNone(details["rank"]["rank_bound"])
            self.assertFalse(details["saturated_diagonal"]["eligible"])
            checks, scope = evaluate(spec(joint, model=model, basis="joint_accepted_event"))
            self.assertEqual(aggregate_status(checks), "inconclusive")
            self.assertEqual(scope["event_basis"], "joint_accepted_event")
            self.assertEqual(scope["rank"]["exact_rank"], 1 if model == "classical" else None)
            # Treating the ratio as an unconditional number is a different
            # submitted premise; it would spuriously exclude the example.
            checks, _ = evaluate(spec(conditioned, model=model))
            self.assertEqual(aggregate_status(checks), "counterexample")
        checks, _ = evaluate(spec(ident(3), basis="joint_accepted_event"))
        self.assertEqual(aggregate_status(checks), "counterexample")

    def test_setting_independent_shared_hash_seed_raises_rank_but_not_saturation_bound(self):
        d = 5
        seeds = list(product((0, 1), repeat=d))
        table = [[F(sum(bits[i] == bits[j] for bits in seeds), len(seeds))
                  for j in range(d)] for i in range(d)]
        for model in ("classical", "quantum"):
            with self.subTest(model=model):
                checks, scope = evaluate(spec(table, model=model))
                self.verify_minor(table, checks[0])
                checks, scope = evaluate(spec(table, model=model, seed=True))
                self.assertEqual([c.status for c in checks], ["unsupported", "inconclusive"])
                self.assertEqual(scope["rank"]["stop_reason"], "rank_not_applicable_with_shared_classical_seed")
                self.assertIsNone(scope["rank"]["rank_bound"])
                self.assertEqual(scope["saturated_diagonal"]["entry_upper_sum"], "15")
                checks, scope = evaluate(spec(table, dimension=1, model=model, seed=True))
                self.assertEqual([c.status for c in checks], ["unsupported", "counterexample"])
                self.assertTrue(checks[1].witness["inputs"]["shared_classical_seed"])
                self.assertEqual(checks[1].witness["actual"], "-10")

    def test_shared_case_budget_and_deadline_do_not_invent_a_test(self):
        raw = spec(ident(5), model="quantum")
        checks, scope = evaluate(raw, max_cases=1)
        self.assertEqual([(c.status, c.checked, c.planned) for c in checks],
                         [("counterexample", 1, 1), ("inconclusive", 0, 1)])
        self.assertEqual(scope["saturated_diagonal"]["stop_reason"], "max_cases")
        checks, scope = evaluate(raw)
        self.assertEqual([(c.status, c.checked) for c in checks],
                         [("counterexample", 1), ("counterexample", 1)])
        for permitted in (0, 10):
            with patch.object(adapter, "monotonic", side_effect=[0]*permitted + [20]*100):
                checks, scope = evaluate(raw, deadline=10)
                self.assertEqual(aggregate_status(checks), "inconclusive")
                self.assertEqual(scope["checked_necessary_tests"], 0)
                self.assertEqual(scope["stop_reason"], "deadline")
                self.assertTrue(all(c.witness is None for c in checks))
        for invalid in (True, "soon", float("nan"), float("-inf")):
            with self.subTest(deadline=invalid), self.assertRaises(ValueError):
                evaluate(raw, deadline=invalid)

    def test_maximum_supported_square_and_large_exact_output_encoding(self):
        n = adapter.MAX_SETTINGS
        table = [[F(1, 1) if i == j else F(1, 11 + n*i + j) for j in range(n)] for i in range(n)]
        checks, scope = evaluate(spec(table, dimension=n-1))
        self.assertEqual(checks[0].status, "counterexample")
        self.assertEqual(scope["rank"]["exact_rank"], n)
        self.assertEqual(checks[0].witness["inputs"]["rows"], list(range(n)))
        total = sum(x for row in table for x in row)
        self.assertEqual(exact_report_number(scope["saturated_diagonal"]["entry_upper_sum"]), total)
        big = F(1, 2**2300-1)
        self.assertEqual(exact_report_number(adapter._exact_text(big)), big)
        self.assertEqual(exact_report_number(adapter._exact_text(-big)), -big)

    def test_strict_schema_normalizes_rational_atoms_and_locks_event_convention(self):
        raw = spec(ident(2), dimension=1)
        raw["intervals"][0][0] = ["2/2", "01"]
        candidate = adapter.parse_prepare_measure_cut(raw)
        self.assertEqual(candidate.specification(), spec(ident(2), dimension=1))
        raw["intervals"][0][0][0] = "0"
        self.assertEqual(candidate.intervals[0][0], (F(1), F(1)))
        self.assertEqual(adapter.LOADED_SOURCE_SHA256,
                         hashlib.sha256(Path(adapter.__file__).read_bytes()).hexdigest())

        def reject(path, value):
            invalid = spec(ident(2))
            parent = invalid
            for key in path[:-1]:
                parent = parent[key]
            parent[path[-1]] = value
            with self.subTest(path=path, value=str(value)[:50]), self.assertRaises((TypeError, ValueError)):
                adapter.parse_prepare_measure_cut(invalid)

        for path, values in (
            (("id",), (True, "invalid label")), (("family",), ("other", False)),
            (("event",), (True, "", "rank selected", ["ref", "other"])),
            (("event_basis",), (True, "conditional", ["unconditional", "accepted_only"])),
            (("memory",), ([], {"model": "quantum", "dimension": 2})),
            (("memory", "model"), ("mixed", True)),
            (("memory", "dimension"), (True, 0, 2.0, adapter.MAX_DIMENSION+1)),
            (("memory", "shared_classical_seed"), (1, 0, "true", None)),
            (("intervals",), ([], [[], []], [[], [], []], [None]*(adapter.MAX_SETTINGS+1))),
            (("intervals", 0, 0), ([0, 1], [False, True], ["0"], ["0", "1", False], ("0", "1"),
                                     ["1/3", "1/4"], ["-1/2", "1"], ["0", "2"], ["0", "1/0"],
                                     ["0.0", "1"], ["0", "1/1000000000000"],
                                     {"basis": "accepted_only", "interval": ["0", "1"]})),
        ):
            for value in values:
                reject(path, value)
        for kwargs in ({"dimension": True}, {"shared_classical_seed": "no"},
                       {"intervals": ([[F(0), F(1)]],)}, {"event_basis": "other"}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                replace(candidate, **kwargs)


if __name__ == "__main__":
    unittest.main()
