"""Controls for the conditional rank-only screen (the research probe is an oracle here only)."""

from __future__ import annotations

import json
import unittest
from dataclasses import FrozenInstanceError
from fractions import Fraction as F
from math import lcm, prod
from typing import cast
from unittest.mock import patch

from scripts import probe_weighted_chiral_pencil as oracle
from scripts.probe_chiral_pencil_signs import EVEN, rank_q
from theory_experiments import chiral_pencil as adapter
from theory_experiments.primitive_screen import Check, Limits, object_fields


def spec(weights: list[object]) -> dict[str, object]:
    return {"family": "chiral_pencil", "id": "sample", "weights": weights}


def result(weights: tuple[F, ...], budget: int = 20) -> Check:
    checks, _ = adapter.evaluate_chiral_pencil(
        adapter.ChiralPencil("sample", weights), Limits(max_cases=budget)
    )
    (check,) = checks
    return check


def synthetic_signs() -> tuple[F, ...]:
    # Synthesize raw signs by inverting the 20 odd-parity equations over
    # GF(2), with every nonpivot edge positive. No target CAR signs as input.
    weights = [F(1)] * 40
    cert = oracle.certificate()
    for j, powers in zip(oracle.J, cert.undo_cycles, strict=True):
        weights[j] = F((-1) ** (sum(powers) % 2))
    return tuple(weights)


def cubic_residuals(weights: tuple[F, ...]) -> list[F]:
    rows, _ = oracle.lattices()
    return [
        sum(
            (
                prod(
                    (w for w, c in zip(weights, row, strict=True) if c == sign),
                    start=F(1),
                )
                for sign in (-1, 1)
            ),
            F(),
        )
        for row in rows
    ]


class ChiralPencilAdapterTests(unittest.TestCase):
    def test_exact_domain_canonicalization_and_immutable_internal_weights(self) -> None:
        raw: list[object] = ["2/4", "-0", "-999999999999/999999999998", *(["1"] * 37)]
        model = adapter.parse_chiral_pencil(spec(raw))
        self.assertEqual(
            model.weights[:3], (F(1, 2), F(), F(-999999999999, 999999999998))
        )
        self.assertEqual(model.specification()["weights"], ["1/2", "0", *raw[2:]])
        self.assertEqual(adapter.parse_chiral_pencil(model.specification()), model)
        raw[0] = "5"
        self.assertEqual(model.weights[0], F(1, 2))
        with self.assertRaises(FrozenInstanceError):
            model.weights = ()  # type: ignore[misc]  # intentionally exercise runtime guard

        invalid: list[object] = [
            True,
            1,
            1.0,
            float("inf"),
            float("nan"),
            1j,
            "i",
            "NaN",
            "",
            "-1/0",
            "1/-3",
            "1.0",
            "+1",
            "1e0",
            "1/1000000000000",
            # Bound the source before cancellation, not just the reduced ratio.
            "1000000000000/1000000000000",
            "0" * 5000,
            "1/" + "9" * 5000,
        ]
        for value in invalid:
            with (
                self.subTest(value_type=type(value)),
                self.assertRaises((TypeError, ValueError)),
            ):
                adapter.parse_chiral_pencil(spec([value] + ["1"] * 39))
        good = spec(["1"] * 40)
        malformed: list[object] = [
            False,
            None,
            {},
            spec([]),
            spec(["1"] * 39),
            spec(["1"] * 41),
            {**good, "weights": ("1",) * 40},
            {**good, "id": True},
            {**good, "family": "other"},
            {**good, "signs": 0},
        ]
        malformed.extend({k: v for k, v in good.items() if k != drop} for drop in good)
        for bad in malformed:
            with self.assertRaises((TypeError, ValueError)):
                adapter.parse_chiral_pencil(bad)
        for bad in [True, 1, 1.5, F(10**12), F(1, 10**12), F(-(1 << 50000))]:
            with self.assertRaises((TypeError, ValueError)):
                adapter.ChiralPencil("sample", (cast(F, bad),) + (F(1),) * 39)
        with self.assertRaises((TypeError, ValueError)):
            adapter.ChiralPencil("sample", cast(tuple[F, ...], [F(1)] * 40))

    def test_incidence_and_signed_integer_certificate(self) -> None:
        self.assertEqual(adapter.EDGES, tuple((a, b) for a, b, _ in oracle.WE))
        self.assertEqual(
            adapter.CHANNELS,
            tuple(2 * i + int(not create) for _, _, (i, create) in oracle.WE),
        )
        rows, _ = oracle.lattices()
        self.assertEqual(
            [h.row() for h in adapter._basis()], [rows[j] for j in oracle.C_ROWS]
        )
        adapter._certify(rows)
        # Multiplying the last row by two leaves it in the integral span but
        # makes its -1 target incompatible. An unsigned rank check would pass.
        bad_sign = [*rows[:-1], [2 * x for x in rows[-1]]]
        with self.assertRaisesRegex(ArithmeticError, "signed conditions"):
            adapter._certify(bad_sign)
        # Doubling a basis row leaves its Q-span alone, but loses unimodularity.
        not_unimodular = [[2 * x for x in rows[0]], *rows[1:]]
        with self.assertRaisesRegex(ArithmeticError, "nonunit pivot"):
            adapter._certify(not_unimodular)

    def test_positive_rational_scalings_and_mixed_sign_gauges(self) -> None:
        signs = synthetic_signs()
        self.assertEqual(cubic_residuals(signs), [F()] * 80)
        scaled = tuple(
            w
            * F(a + 2, a + 3)
            * F(b + 2, b + 3)
            * F(i + 3, i + 5)
            * (-1 if 0 in (a, b) else 1)
            * (-1 if create else 1)
            for w, (a, b, (i, create)) in zip(signs, oracle.WE, strict=True)
        )
        self.assertGreater(len(set(map(abs, scaled))), 10)
        self.assertEqual(cubic_residuals(scaled), [F()] * 80)
        for weights in (signs, scaled):
            check = result(weights)
            self.assertEqual(
                (check.status, check.checked, check.planned, check.witness),
                ("no_counterexample_within_bounds", 20, 20, None),
            )
        # All forty individual sign changes and unequal-amplitude defects must
        # each return a rank-10 witness, not merely a nonzero numerical error.
        for j in range(40):
            for factor in (F(-1), F(5, 3)):
                changed = list(scaled)
                changed[j] *= factor
                failed = result(tuple(changed))
                self.assertEqual(failed.status, "counterexample")
                inputs = object_fields(object_fields(failed.witness)["inputs"])
                self.assertEqual(inputs["direct_symmetric_rational_rank"], 10)

    def test_replay_full_weighted_symmetric_witness(self) -> None:
        weights = tuple(F(j + 1, j + 2) for j in range(40))
        failed = result(weights)
        self.assertEqual(
            (failed.id, failed.status, failed.checked),
            ("chiral_pencil_rank10_holdout", "counterexample", 1),
        )
        witness = object_fields(json.loads(json.dumps(failed.witness)))
        inputs = object_fields(witness["inputs"])
        axes = cast(list[list[int]], inputs["channels_slot_common_bit"])
        coeffs = cast(list[int], inputs["channel_coefficients"])
        self.assertEqual(len(coeffs), 10)
        self.assertEqual(
            {j for j, bit in enumerate(coeffs) if bit}, {2 * i + b for i, b in axes}
        )
        self.assertEqual(sum(coeffs), 3)
        edges = cast(list[dict[str, object]], inputs["active_edges"])
        expected = [
            {"masks": [a, b], "weight": str(w)}
            for w, (a, b, (i, create)) in zip(weights, oracle.WE, strict=True)
            if coeffs[2 * i + int(not create)]
        ]
        self.assertEqual(edges, expected)
        self.assertEqual(len(edges), 12)
        m = [[0] * 16 for _ in range(16)]
        denominator = lcm(*(w.denominator for w in weights))
        for edge in edges:
            a, b = cast(list[int], edge["masks"])
            r, c = EVEN.index(a), EVEN.index(b)
            m[r][c] = m[c][r] = int(F(str(edge["weight"])) * denominator)
        self.assertEqual(rank_q(m), 10)
        left, right = (
            F(s) for s in cast(list[str], inputs["alternating_matching_products"])
        )
        self.assertEqual(str(left + right), witness["actual"])
        self.assertEqual(cubic_residuals(weights)[0], left + right)
        with (
            patch.object(adapter, "_unit_sum_rank", return_value=8),
            self.assertRaisesRegex(ArithmeticError, "disagrees"),
        ):
            result(weights)

    def test_budget_never_visits_the_twentieth_case_early(self) -> None:
        weights = list(synthetic_signs())
        # Place a multiplicative defect EXCLUSIVELY on the final selected
        # basis condition; other dependent triples need not remain intact.
        for j, powers in zip(oracle.J, oracle.certificate().undo_cycles, strict=True):
            weights[j] *= F(2) ** powers[-1]
        residuals = cubic_residuals(tuple(weights))
        self.assertEqual(
            [j for j in oracle.C_ROWS if residuals[j]], [oracle.C_ROWS[-1]]
        )
        with patch.object(
            adapter, "_unit_sum_rank", side_effect=AssertionError("over budget")
        ):
            limited = result(tuple(weights), 19)
        self.assertEqual(
            (limited.status, limited.checked, limited.planned, limited.witness),
            ("inconclusive", 19, 20, None),
        )
        complete = result(tuple(weights), 20)
        self.assertEqual((complete.status, complete.checked), ("counterexample", 20))

    def test_zero_has_no_counterexample_even_with_another_early_defect(self) -> None:
        weights = ["1"] * 40
        weights[-1] = "0"
        candidate = adapter.parse_chiral_pencil(spec(list(weights)))
        with patch.object(
            adapter, "_basis", side_effect=AssertionError("zero reached trials")
        ):
            checks, scope = adapter.evaluate_chiral_pencil(
                candidate, Limits(max_cases=1)
            )
        (check,) = checks
        self.assertEqual(
            (check.status, check.checked, check.planned, check.witness),
            ("unsupported", 0, 0, None),
        )
        self.assertEqual(scope["zero_edge_indices"], [39])

    def test_nonreal_gauge_is_outside_parser_even_when_ratios_cancel(self) -> None:
        # Exact exponents mod four for multiplying only the zero-mask vertex
        # by i. Every alternating ratio is unchanged, yet affected entries
        # are not in this adapter's real rational input domain.
        exponents = [int(0 in (a, b)) for a, b, _ in oracle.WE]
        self.assertIn(1, exponents)
        rows, _ = oracle.lattices()
        self.assertTrue(
            all(
                sum(e * c for e, c in zip(exponents, row, strict=True)) % 4 == 0
                for row in rows
            )
        )
        raw: list[object] = [
            1j * int(w) if e else str(w)
            for w, e in zip(synthetic_signs(), exponents, strict=True)
        ]
        with self.assertRaises(ValueError):
            adapter.parse_chiral_pencil(spec(raw))
