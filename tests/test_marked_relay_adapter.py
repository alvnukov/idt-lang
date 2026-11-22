"""Independent path and quantifier checks for the pure marked-relay adapter."""

from __future__ import annotations

import json
import unittest
from collections import Counter
from collections.abc import Iterator, Sequence
from dataclasses import replace
from functools import reduce
from itertools import product
from typing import cast

from scripts.probe_minimal_signal_relay import quotient_4
from theory_experiments.marked_relay import (
    MarkedRelay,
    evaluate_marked_relay,
    parse_marked_relay,
)
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    object_fields,
    parse_limits,
)

PORTS = range(4)
Table = Sequence[Sequence[int]]
Word = tuple[int, ...]


def raw_spec(
    table: Table,
    markers: Sequence[int] | None = None,
    contract: str = "fixed",
    program: str = "named_six",
    origin: int = 0,
) -> dict[str, object]:
    result: dict[str, object] = {
        "id": "marked_relay_test",
        "family": "marked_relay",
        "transitions": [list(row) for row in table],
        "marker_classes": list(range(len(table))) if markers is None else list(markers),
        "origin_contract": contract,
        "program": program,
    }
    if contract == "fixed":
        result["origin"] = origin
    return result


def run(spec: dict[str, object], budget: int = 5000) -> tuple[Check, dict[str, object]]:
    (check,), scope = evaluate_marked_relay(
        parse_marked_relay(spec), Limits(max_cases=budget)
    )
    return check, scope


def origin_classes(scope: dict[str, object]) -> list[dict[str, object]]:
    rows = scope["origin_classes"]
    if not isinstance(rows, list):
        raise TypeError("expected an origin class list")
    return [object_fields(row) for row in rows]


def reduced_words(length: int) -> Iterator[Word]:
    if length == 0:
        yield ()
    else:
        for prefix in reduced_words(length - 1):
            for port in PORTS:
                if not prefix or port != prefix[-1]:
                    yield (*prefix, port)


def expected_cases(program: str) -> tuple[tuple[Word, bool], ...]:
    if program == "named_six":
        returns = [
            ((a, b, c, a, b, c), True)
            for a, b, c in product(PORTS, repeat=3)
            if len({a, b, c}) == 3
        ]
        nonreturns = [
            ((a, b, a, b, a, b), False) for a, b in product(PORTS, repeat=2) if a != b
        ]
        return tuple(returns + nonreturns)
    return tuple(
        (word, Counter(word[::2]) == Counter(word[1::2]))
        for length in range(1, 7)
        for word in reduced_words(length)
    )


NAMED = expected_cases("named_six")
THROUGH = expected_cases("through_six")


def oracle_return(
    table: Table, markers: Sequence[int], origin: int, word: Word
) -> bool:
    end = reduce(lambda state, port: table[state][port], word, origin)
    return markers[origin] == markers[end]


def first_unequal(
    table: Table,
    markers: Sequence[int],
    origin: int,
    cases: Sequence[tuple[Word, bool]],
) -> tuple[int, Word] | None:
    return next(
        (
            (i, word)
            for i, (word, expected) in enumerate(cases, 1)
            if oracle_return(table, markers, origin, word) != expected
        ),
        None,
    )


def disjoint(*components: Table) -> tuple[tuple[int, ...], ...]:
    table: list[tuple[int, ...]] = []
    for component in components:
        start = len(table)
        table.extend(tuple(start + target for target in row) for row in component)
    return tuple(table)


def abelian_duplicate_ports(offsets: Sequence[int]) -> tuple[tuple[int, ...], ...]:
    """Offsets in (Z/2)^2 force failure exactly for duplicated port pairs."""
    return tuple(
        tuple(4 * (1 - role) + (position ^ offset) for offset in offsets)
        for role, position in product(range(2), range(4))
    )


class MarkedRelayTests(unittest.TestCase):
    def assert_replayable(
        self,
        failure: object,
        table: Table,
        markers: Sequence[int],
        origin: int,
        word: Word,
    ) -> None:
        row = object_fields(failure)
        self.assertEqual(row["origin"], origin)
        self.assertEqual(row["word"], list(word))
        path = [origin]
        for p in word:
            path.append(table[path[-1]][p])
        self.assertEqual(row["path"], path)
        self.assertEqual(row["endpoint"], path[-1])
        self.assertEqual(row["origin_marker_class"], markers[origin])
        self.assertEqual(row["endpoint_marker_class"], markers[path[-1]])
        observed = markers[origin] == markers[path[-1]]
        self.assertIs(row["observed_return"], observed)
        self.assertIs(row["expected_return"], not observed)
        positive, negative = Counter(word[::2]), Counter(word[1::2])
        self.assertEqual(
            row["alternating_signed_port_counts"],
            [positive[p] - negative[p] for p in PORTS],
        )

    def test_strict_input_and_dataclass_roundtrip(self) -> None:
        table = ((1, 0, 1, 0), (0, 1, 0, 1))
        fixed = raw_spec(table, (127, 127), origin=1)
        for spec in (
            fixed,
            raw_spec(table, contract="exists"),
            raw_spec(table, contract="all"),
        ):
            model = parse_marked_relay(spec)
            self.assertEqual(model.specification(), spec)
            self.assertEqual(parse_marked_relay(json.loads(json.dumps(spec))), model)
        invalid: list[object] = [[], None, True, {**fixed, "expected_verdict": "pass"}]
        invalid.extend({k: v for k, v in fixed.items() if k != key} for key in fixed)
        invalid_fields: dict[str, list[object]] = {
            "id": [True, "", "Invalid"],
            "family": ["other", True],
            "origin_contract": [True, [], "fixed_calibration", "exists", "all"],
            "origin": [None, True, 1.0, -1, 2],
            "program": [True, [], "six", "program_is_correct"],
            "marker_classes": [
                [],
                (127, 127),
                [0],
                [False, 0],
                [0, 1.0],
                [0, 128],
                [0, -1],
            ],
            "transitions": [
                [],
                table,
                [[0, 0, 0, 0]] * 129,
                [[0, 0, 0]],
                [(0, 0, 0, 0)],
                [[False, 0, 0, 0]],
                [[0, 0.0, 0, 0]],
                [[0, 0, -1, 0]],
                [[0, 0, 1, 0]],
                [[1, 0, 0, 0], [1, 1, 1, 1]],
            ],
        }
        invalid.extend(
            {**fixed, key: value}
            for key, values in invalid_fields.items()
            for value in values
        )
        for item in invalid:
            with self.subTest(item=item), self.assertRaises((TypeError, ValueError)):
                parse_marked_relay(item)
        model = parse_marked_relay(fixed)
        for params in (
            {"origin": True},
            {"origin_contract": "exists"},
            {"marker_classes": (127, False)},
            {"marker_classes": [127, 127]},
            {"transitions": ((1, 0, 1, 0), (1, 1, 0, 1))},
        ):
            with self.subTest(params=params), self.assertRaises(ValueError):
                replace(model, **params)
        with self.assertRaises(ValueError):
            MarkedRelay("id", ((0, 0, 0, 0),), (0,), "fixed", "named_six")
        for limit_fields in (
            {"max_cases": True},
            {"max_cases": 0},
            {"max_cases": 5001},
            {"unknown": 1},
            {"coefficient_radius": True},
        ):
            with self.subTest(limits=limit_fields), self.assertRaises(ValueError):
                parse_limits({**Limits().specification(), **limit_fields})
        with self.assertRaises(TypeError):
            evaluate_marked_relay(model, cast(Limits, {"max_cases": 1}))
        renamed = {**fixed, "id": "name_cannot_set_verdict"}
        self.assertEqual(run(fixed), run(renamed))

    def test_all_three_state_transitions_against_independent_oracle(self) -> None:
        involutions = ((0, 1, 2), (1, 0, 2), (2, 1, 0), (0, 2, 1))
        for columns in product(involutions, repeat=4):
            table = tuple(zip(*columns, strict=True))
            for markers in ((0, 1, 2), (0, 0, 1), (0, 1, 0), (0, 0, 0)):
                for program, cases in (("named_six", NAMED), ("through_six", THROUGH)):
                    outcomes = [
                        first_unequal(table, markers, origin, cases)
                        for origin in range(3)
                    ]
                    for origin, outcome in enumerate(outcomes):
                        check, scope = run(
                            raw_spec(table, markers, "fixed", program, origin)
                        )
                        self.assertEqual(check.planned, len(cases))
                        if outcome is None:
                            self.assertEqual(
                                check.status, "no_counterexample_within_bounds"
                            )
                            self.assertEqual(check.checked, len(cases))
                        else:
                            index, word = outcome
                            self.assertEqual(
                                (check.status, check.checked), ("counterexample", index)
                            )
                            self.assert_replayable(
                                origin_classes(scope)[0]["first_failure"],
                                table,
                                markers,
                                origin,
                                word,
                            )
                    for contract in ("all", "exists"):
                        check, scope = run(raw_spec(table, markers, contract, program))
                        accepted = (all if contract == "all" else any)(
                            outcome is None for outcome in outcomes
                        )
                        self.assertEqual(
                            check.status,
                            "no_counterexample_within_bounds"
                            if accepted
                            else "counterexample",
                        )
                        rows = origin_classes(scope)
                        self.assertEqual(check.planned, len(cases) * len(rows))
                        self.assertEqual(
                            check.checked,
                            sum(cast(int, row["checked"]) for row in rows),
                        )
                        self.assertEqual(
                            sorted(
                                origin
                                for row in rows
                                for origin in cast(list[int], row["origins"])
                            ),
                            [0, 1, 2],
                        )
                        for row in rows:
                            members = cast(list[int], row["origins"])
                            self.assertEqual(row["representative"], members[0])
                            self.assertTrue(
                                all(
                                    outcomes[origin] == outcomes[members[0]]
                                    for origin in members
                                )
                            )

    def test_detector_equality_neither_state_equality_nor_a_congruence(self) -> None:
        # Same marks at 0 and 2; following port 0 reveals different return bits.
        table = ((1, 0, 0, 0), (0, 2, 1, 1), (2, 1, 2, 2))
        markers = (7, 9, 7)
        self.assertFalse(oracle_return(table, markers, 0, (0,)))
        self.assertTrue(oracle_return(table, markers, 2, (0,)))
        check, scope = run(raw_spec(table, markers, "exists", "through_six"))
        rows = origin_classes(scope)
        self.assertEqual([row["origins"] for row in rows], [[0], [1], [2]])
        self.assertEqual([row["reachable_states"] for row in rows], [3, 3, 3])
        self.assertEqual((check.status, check.checked), ("counterexample", 6))
        self.assert_replayable(rows[0]["first_failure"], table, markers, 0, (1,))
        self.assert_replayable(rows[1]["first_failure"], table, markers, 1, (2,))
        self.assert_replayable(rows[2]["first_failure"], table, markers, 2, (0,))

        # A different state does count as a return if it carries this origin's mark.
        crossing = ((1, 0, 0, 0), (0, 1, 1, 1))
        check, scope = run(raw_spec(crossing, (7, 7), program="through_six"))
        self.assertEqual((check.status, check.checked), ("counterexample", 1))
        self.assert_replayable(
            origin_classes(scope)[0]["first_failure"], crossing, (7, 7), 0, (0,)
        )

    def test_disconnected_root_sharing_ignores_irrelevant_marker_names(self) -> None:
        component = ((1, 0, 0, 0), (0, 2, 1, 1), (2, 1, 2, 2))
        table = disjoint(component, component)
        # In the second component the OTHER vertices share a marker; for roots
        # 0 and 3 only their own marker predicate is observable.
        check, scope = run(raw_spec(table, (0, 1, 2, 7, 8, 8), "exists", "through_six"))
        rows = origin_classes(scope)
        self.assertEqual(rows[0]["origins"], [0, 3])
        self.assertEqual(rows[0]["reachable_states"], 3)
        self.assertEqual(rows[0]["checked"], 2)
        self.assertEqual(check.planned, len(rows) * len(THROUGH))
        self.assertEqual(check.status, "counterexample")

        isolated = tuple((state,) * 4 for state in range(128))
        check, scope = run(
            raw_spec(isolated, contract="exists", program="through_six"), 1
        )
        self.assertEqual(
            (check.status, check.checked, check.planned), ("counterexample", 1, 1456)
        )
        self.assertEqual(origin_classes(scope)[0]["origins"], list(range(128)))
        self.assertEqual(origin_classes(scope)[0]["reachable_states"], 1)

    def test_mixed_viable_and_eliminated_origins_under_edge_budgets(self) -> None:
        good = quotient_4((0, 1, 2, 3)).neighbors
        bad = ((0, 0, 0, 0),)
        table = disjoint(bad, good)
        ex = raw_spec(table, contract="exists")
        al = raw_spec(table, contract="all")
        fixed_bad = raw_spec(table)
        fixed_good = raw_spec(table, origin=1)
        for budget, status, checked, classes in (
            (24, "inconclusive", 24, ["partial", "not_tested"]),
            (25, "inconclusive", 25, ["eliminated", "not_tested"]),
            (26, "inconclusive", 26, ["eliminated", "partial"]),
            (60, "inconclusive", 60, ["eliminated", "partial"]),
            (61, "no_counterexample_within_bounds", 61, ["eliminated", "viable"]),
        ):
            with self.subTest(budget=budget):
                check, scope = run(ex, budget)
                self.assertEqual(
                    (check.status, check.checked, check.planned), (status, checked, 72)
                )
                self.assertIsNone(check.witness)
                rows = origin_classes(scope)
                self.assertEqual([row["status"] for row in rows], classes)
                self.assertEqual(
                    [row["origins"] for row in rows], [[0], list(range(1, 33))]
                )
                self.assertEqual(scope["viable_origin"], 1 if budget == 61 else None)
        for spec in (al, fixed_bad):
            self.assertEqual(run(spec, 24)[0].status, "inconclusive")
            self.assertEqual(run(spec, 25)[0].status, "counterexample")
        self.assertEqual(run(fixed_good, 35)[0].status, "inconclusive")
        self.assertEqual(
            run(fixed_good, 36)[0].status, "no_counterexample_within_bounds"
        )

        # When a viable class comes first, exists need not sample the bad class.
        reversed_table = disjoint(good, bad)
        check, scope = run(raw_spec(reversed_table, contract="exists"), 36)
        self.assertEqual(
            (check.status, check.checked, check.planned),
            ("no_counterexample_within_bounds", 36, 72),
        )
        self.assertIs(scope["trajectory_plan_exhausted"], False)
        self.assertEqual(
            [row["status"] for row in origin_classes(scope)], ["viable", "not_tested"]
        )

    def test_exists_requires_one_origin_for_all_words_even_if_each_word_can_pass(
        self,
    ) -> None:
        table = disjoint(
            abelian_duplicate_ports((0, 0, 1, 2)), abelian_duplicate_ports((0, 1, 2, 2))
        )
        markers = tuple(range(len(table)))
        for word, expected in NAMED:
            self.assertTrue(
                any(
                    oracle_return(table, markers, x, word) == expected
                    for x in range(len(table))
                )
            )
        self.assertTrue(
            all(
                first_unequal(table, markers, x, NAMED) is not None
                for x in range(len(table))
            )
        )
        spec = raw_spec(table, markers, "exists")
        check, scope = run(spec)
        self.assertEqual(
            (check.status, check.checked, check.planned), ("counterexample", 58, 72)
        )
        self.assertEqual(scope["stop_reason"], "all_origin_classes_eliminated")
        rows = origin_classes(scope)
        self.assertEqual([row["status"] for row in rows], ["eliminated", "eliminated"])
        self.assert_replayable(rows[0]["first_failure"], table, markers, 0, (0, 1) * 3)
        self.assert_replayable(rows[1]["first_failure"], table, markers, 8, (2, 3) * 3)
        self.assertIsNotNone(check.witness)
        incomplete, scope = run(spec, 57)
        self.assertEqual(incomplete.status, "inconclusive")
        self.assertIsNone(incomplete.witness)
        self.assertEqual(
            [row["status"] for row in origin_classes(scope)], ["eliminated", "partial"]
        )
        self.assertEqual(run(spec, 58)[0], check)

    def test_published_32_and_64_state_relays(self) -> None:
        small = quotient_4((0, 1, 2, 3)).neighbors
        large = quotient_4((0, 2)).neighbors
        self.assertEqual((len(small), len(large)), (32, 64))
        self.assertEqual((len(NAMED), len(THROUGH)), (36, 1456))
        for table in (small, large):
            check, scope = run(raw_spec(table, contract="all"))
            self.assertEqual(
                (check.status, check.checked, check.planned),
                ("no_counterexample_within_bounds", 36, 36),
            )
            self.assertEqual(
                origin_classes(scope)[0]["origins"], list(range(len(table)))
            )
        check, scope = run(raw_spec(small, contract="all", program="through_six"))
        self.assertEqual(check.status, "counterexample")
        first = first_unequal(small, range(32), 0, THROUGH)
        if first is None:
            self.fail("32-state relay must return on some extra six-letter word")
        index, word = first
        self.assertEqual(len(word), 6)
        self.assertEqual((check.checked, check.planned), (index, 1456))
        self.assert_replayable(
            origin_classes(scope)[0]["first_failure"], small, range(32), 0, word
        )
        self.assertTrue(oracle_return(small, range(32), 0, (0, 1, 0, 2, 0, 3)))
        self.assertFalse(oracle_return(large, range(64), 0, (0, 1, 0, 2, 0, 3)))
        self.assertTrue(
            all(
                first_unequal(large, range(64), origin, THROUGH) is None
                for origin in range(64)
            )
        )
        spec = raw_spec(large, contract="all", program="through_six")
        self.assertEqual(run(spec, 1455)[0].status, "inconclusive")
        check, scope = run(spec, 1456)
        self.assertEqual(
            (check.status, check.checked, check.planned),
            ("no_counterexample_within_bounds", 1456, 1456),
        )
        self.assertIs(scope["trajectory_plan_exhausted"], True)
        self.assertIs(scope["all_origin_classes_decided"], True)

    def test_state_port_and_detector_relabeling_does_not_prescribe_the_verdict(
        self,
    ) -> None:
        table = quotient_4((0, 1, 2, 3)).neighbors
        reorder_ports = (2, 0, 3, 1)
        new_state = tuple((11 * i + 7) % 32 for i in range(32))
        renamed_table: list[tuple[int, ...]] = [()] * 32
        renamed_marker = [0] * 32
        for old, new in enumerate(new_state):
            renamed_table[new] = tuple(new_state[table[old][p]] for p in reorder_ports)
            renamed_marker[new] = 127 - old
        for program, cases in (("named_six", NAMED), ("through_six", THROUGH)):
            fixed, _ = run(raw_spec(table, program=program, origin=8))
            renamed, _ = run(
                raw_spec(
                    renamed_table, renamed_marker, program=program, origin=new_state[8]
                )
            )
            original_all, _ = run(raw_spec(table, contract="all", program=program))
            renamed_all, _ = run(
                raw_spec(renamed_table, renamed_marker, "all", program)
            )
            self.assertEqual(
                (fixed.status, fixed.planned), (renamed.status, renamed.planned)
            )
            self.assertEqual(
                (original_all.status, original_all.planned),
                (renamed_all.status, renamed_all.planned),
            )
            comparator = dict(cases)
            for word, expected in cases:
                rewired_word = tuple(reorder_ports[p] for p in word)
                self.assertEqual(comparator[rewired_word], expected)
                self.assertEqual(
                    oracle_return(renamed_table, renamed_marker, new_state[8], word),
                    oracle_return(table, range(32), 8, rewired_word),
                )
