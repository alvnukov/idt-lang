from __future__ import annotations

import io
import json
import unittest
from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction as F
from itertools import pairwise, product
from unittest.mock import patch

from scripts import probe_adic_event_reservoir as adic
from scripts import probe_alternative_setting_gaps as gaps
from scripts import probe_hensen_order_controls as hensen
from scripts.probe_coset_address_transport import ONE, I, add, mul, reduce, reps
from scripts.probe_routed_pair_bell import (
    A_FIRST,
    B_FIRST,
    prepare,
    raw_counts,
    run_setting,
)


class AlternativeSettingControls(unittest.TestCase):
    def test_hidden_router_history_saturates_bound_with_zero_pair_gaps(self) -> None:
        prep = prepare(True)
        with redirect_stdout(io.StringIO()):
            tables = (gaps.routed_journal(prep, 0), gaps.routed_journal(prep, 1))
        box = gaps.sequential_box(tables)
        for setting, pair_table in zip(gaps.SETTINGS, box, strict=True):
            for order in (A_FIRST, B_FIRST):
                with self.subTest(setting=setting, order=order):
                    counts = raw_counts(run_setting(prep, setting, order))
                    self.assertEqual(
                        tuple(F(count, 20) for count in counts), pair_table
                    )
        self.assertEqual(gaps.chsh(box), F(14, 5))
        self.assertEqual(tuple(map(gaps.history_equal, tables)), (F(7, 10), F(3, 10)))
        self.assertEqual(gaps.triple_bound(box, tables), (F(0), F(0), F(2, 5)))
        self.assertEqual(gaps.tv(*map(gaps.history_table, tables)), F(2, 5))

    def test_common_joint_spends_same_budget_on_pair_gaps(self) -> None:
        target = gaps.unbiased_box((F(3, 5), F(3, 5), F(4, 5), F(-4, 5)))
        joint = gaps.local_joint((F(1, 5), F(1, 5), F(3, 10), F(3, 10)))
        self.assertEqual(gaps.chsh(gaps.joint_box(joint)), F(2))
        self.assertEqual(gaps.full_joint_bound(target, joint), (0, 0, F(1, 5), F(1, 5)))
        self.assertEqual(
            gaps.triple_bound(target, gaps.triples_from_joint(joint)),
            (F(1, 5), F(1, 5), 0),
        )

    def test_two_triple_bound_rejects_mismatched_causal_prefix(self) -> None:
        joint = gaps.local_joint((F(1, 4), F(1, 4), F(1, 4), F(1, 4)))
        tables = gaps.triples_from_joint(joint)
        target = gaps.unbiased_box((F(0), F(1, 2), F(1, 2), F(-1, 2)))
        with self.assertRaisesRegex(ValueError, "causal prefix"):
            gaps.triple_bound(target, tables)


class AdicReservoirControls(unittest.TestCase):
    def test_finite_address_law_bijection_and_exhaustion(self) -> None:
        for level in (0, 1, 2, 5):
            with self.subTest(level=level):
                stock = reps(adic.pi_power(level))
                self.assertEqual(
                    Counter(adic.digits(address, level) for address in stock),
                    Counter(product((0, 1), repeat=level)),
                )
        with self.assertRaisesRegex(ValueError, "finite reservoir exhausted"):
            adic.split((0, 0), 0)

    def test_same_uniform_initial_law_does_not_choose_the_update(self) -> None:
        level = 3
        modulus = adic.pi_power(level)
        stock = reps(modulus)
        translated = [reduce(add(address, ONE), modulus) for address in stock]
        rotated = [reduce(mul(I, address), modulus) for address in stock]
        self.assertCountEqual(stock, translated)
        self.assertCountEqual(stock, rotated)

        def first_bits(addresses: list[tuple[int, int]]) -> list[int]:
            return [adic.split(address, level)[0] for address in addresses]

        bits = [adic.split(address, level)[0] for address in stock]
        self.assertEqual(first_bits(translated), [1 - digit for digit in bits])
        self.assertEqual(first_bits(rotated), bits)
        self.assertEqual(
            Counter(adic.digits(address, level)[:2] for address in stock),
            Counter({(0, 0): 2, (0, 1): 2, (1, 0): 2, (1, 1): 2}),
        )

    def test_predictable_prefix_and_peek_selected_digit_differ(self) -> None:
        level = 3
        words = tuple(adic.digits(a, level) for a in reps(adic.pi_power(level)))
        seeds: Counter[tuple[int, tuple[int, ...]]] = Counter()
        for word in words:
            width = 1 + word[0]
            seeds[word[0], word[1 : 1 + width]] += 1
        self.assertEqual(seeds[0, (0,)], 2)
        self.assertEqual(seeds[0, (1,)], 2)
        self.assertEqual(
            tuple(seeds[1, seed] for seed in product((0, 1), repeat=2)), (1,) * 4
        )
        selected_zeroes = sum(word[0 if word[0] == 0 else 1] == 0 for word in words)
        self.assertEqual(F(selected_zeroes, len(words)), F(3, 4))


class ConditionalRunsControls(unittest.TestCase):
    def test_raw_free_fixed_margin_counts_and_resolution_floor(self) -> None:
        words = tuple(word for word in product((-1, 1), repeat=4) if sum(word) == 0)
        brute = Counter(sum(a != b for a, b in pairwise(word)) for word in words)
        self.assertEqual(dict(hensen.transition_counts(2, 2)), brute)
        result = hensen.party_test(((1, 1, -1), (1, 1, 1, -1)))
        self.assertEqual(result["two_sided_p_exact"], "2/3")
        self.assertEqual(result["two_party_bonferroni_p_exact"], "1")
        self.assertEqual(result["smallest_attainable_bonferroni_p_exact"], "2/3")
        self.assertFalse(result["rejection_possible_at_family_alpha"])

    def test_accepted_subsequence_can_skip_other_contexts_and_rejected_rows(
        self,
    ) -> None:
        def row(day: int, run: int, a: int, b: int, sign: int) -> dict[str, object]:
            return {
                "accepted": True,
                "source_fields": ["time", str(day), str(run)],
                "a": a,
                "b": b,
                "x": sign,
                "y": 1,
            }

        rows = [
            row(1, 1, 0, 0, 1),
            {"accepted": False},
            row(1, 1, 0, 1, 1),
            row(2, 1, 0, 0, 1),
            row(1, 1, 0, 0, -1),
            row(1, 2, 0, 0, 1),
        ]
        strata = hensen.accepted_strata({"records": rows})
        self.assertEqual(strata[(1, 1, 0, 0)], [(1, 1), (-1, 1)])
        result = hensen.party_test(
            tuple(tuple(a for a, _ in values) for values in strata.values())
        )
        self.assertEqual(result["observations"], 5)
        self.assertEqual(result["same_stratum_subsequence_neighbors"], 1)
        self.assertEqual(result["observed_transitions"], 1)

    def test_default_cli_does_not_read_raw_or_report_empirical_completion(self) -> None:
        output = io.StringIO()
        with (
            patch("sys.argv", ["probe_hensen_order_controls", "--json"]),
            patch.object(hensen, "read_pinned_raw") as read_raw,
            patch.object(hensen, "analyze_pinned_bytes") as analyze,
            redirect_stdout(output),
        ):
            self.assertEqual(hensen.main(), 0)
        read_raw.assert_not_called()
        analyze.assert_not_called()
        result = json.loads(output.getvalue())
        self.assertEqual(result["exact_controls"], "passed")
        self.assertEqual(
            result["empirical_status"], "not_tested_without_optional_pinned_raw_file"
        )
        self.assertNotIn("empirical", result)
