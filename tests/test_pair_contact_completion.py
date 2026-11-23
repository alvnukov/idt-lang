import unittest
from itertools import combinations, permutations, product
from math import isqrt

from scripts.probe_pair_contact_completion import (
    BASIC_MAP,
    CONTACTS,
    FRESH_START,
    MARKER_MAP,
    Histogram,
    Pair,
    PairMap,
    State,
    basic_protocol,
    census,
    enumerate_pair_maps,
    marker_protocol,
    pair_event,
    replay,
)


def direct_small_run(
    mapping: dict[Pair, Pair], zeros: int, ones: int, occupied: Pair
) -> tuple[int, bool, bool]:
    width = zeros + ones
    start = tuple(zeros if i in occupied else 0 for i in range(4))

    def target(state: State) -> bool:
        return all((x >= zeros) != (i in occupied) for i, x in enumerate(state))

    def histogram(state: State) -> Histogram:
        return tuple(state.count(x) for x in range(width))

    def explore(positives: set[Histogram]) -> tuple[dict[State, int], tuple[bool, ...]]:
        distances = {start: 0}
        queue = [start]
        hits = []
        for state in queue:
            if histogram(state) in positives:
                hits.append(target(state))
                continue
            for a, b in CONTACTS:
                left, right = mapping[state[a], state[b]]
                after = tuple(
                    left if i == a else right if i == b else x
                    for i, x in enumerate(state)
                )
                if after not in distances:
                    distances[after] = distances[state] + 1
                    queue.append(after)
        return distances, tuple(hits)

    full_states, _ = explore(set())
    minimum = min((n for state, n in full_states.items() if target(state)), default=-1)
    observations = sorted(
        {histogram(state) for state in full_states} - {histogram(start)}
    )
    first, globally = False, False
    for keep in product((False, True), repeat=len(observations)):
        positives = {hist for hist, use in zip(observations, keep, strict=True) if use}
        _, hits = explore(positives)
        first |= bool(hits) and all(hits)
        global_hits = [
            target(state) for state in full_states if histogram(state) in positives
        ]
        globally |= bool(global_hits) and all(global_hits)
    return minimum, globally, first


def direct_small_inventory(
    zeros: int, ones: int
) -> tuple[set[PairMap], dict[int, int], int, int]:
    """Ordered state graph and literal observation subsets, independent of the quotient."""
    width = zeros + ones
    pairs = tuple((a, b) for a in range(width) for b in range(width))
    blocks = [
        tuple(pair for pair in pairs if sum(x >= zeros for x in pair) == w)
        for w in range(3)
    ]
    rules: set[PairMap] = set()
    lengths: dict[int, int] = {}
    global_total = first_total = 0
    for images in product(*(permutations(block) for block in blocks)):
        mapping = {
            pair: image
            for block, block_images in zip(blocks, images, strict=True)
            for pair, image in zip(block, block_images, strict=True)
        }
        if any(mapping[b, a] != (d, c) for (a, b), (c, d) in mapping.items()):
            continue
        rule = tuple(mapping[pair] for pair in pairs)
        rules.add(rule)
        results = [
            direct_small_run(mapping, zeros, ones, occupied)
            for occupied in combinations(range(4), 2)
        ]
        if len(set(results)) != 1:
            raise ArithmeticError(f"direct results vary by fresh start: {results}")
        minimum, globally, first = results[0]
        if minimum >= 0:
            lengths[minimum] = lengths.get(minimum, 0) + 1
        global_total += globally
        first_total += first
    return rules, lengths, global_total, first_total


class PairContactCompletionTests(unittest.TestCase):
    def test_basic_rule_is_one_shared_reversible_pair_permutation(self) -> None:
        for rule in (BASIC_MAP, MARKER_MAP):
            for lhs in product(range(isqrt(len(rule))), repeat=2):
                rhs = pair_event(rule, lhs, (0, 1))
                self.assertEqual(rhs, pair_event(rule, lhs, (1, 0)))
                self.assertEqual(pair_event(rule, rhs, (0, 1)), lhs)
                self.assertEqual(
                    sum(x in (2, 3) for x in lhs), sum(x in (2, 3) for x in rhs)
                )
        self.assertEqual(pair_event(BASIC_MAP, (0, 2), (0, 1)), (3, 1))
        self.assertEqual(
            replay(BASIC_MAP, FRESH_START, ((0, 2), (1, 3))),
            ((2, 2, 0, 0), (1, 2, 3, 0), (1, 1, 3, 3)),
        )

    def test_basic_protocol_checks_all_six_starts_and_fair_lasso(self) -> None:
        report = basic_protocol()
        self.assertEqual(report["valid_starts"], 6)
        self.assertEqual(report["component_sizes"], [6] * 6)
        self.assertEqual(report["input_dependent_matching_completions"], 6)
        self.assertEqual(report["fixed_word"], ((0, 1), (0, 2), (1, 3), (2, 3)))
        self.assertEqual(report["fixed_word_completions"], 6)
        self.assertEqual(
            report["fair_loop_word"], tuple(edge for edge in CONTACTS for _ in range(2))
        )
        self.assertEqual(report["fair_loop_noncompletions"], 6)

    def test_map_census_distinguishes_reach_global_and_first_hit(self) -> None:
        for split, maps, reachable, lengths, globally_sound, first_hit_sound in (
            ((1, 1), 2, 1, {2: 1}, 0, 0),
            ((2, 1), 32, 22, {2: 16, 3: 4, 4: 2}, 0, 0),
            (
                (2, 2),
                6144,
                5448,
                {2: 3072, 3: 1392, 4: 584, 5: 264, 6: 120, 7: 8, 8: 8},
                8,
                12,
            ),
        ):
            with self.subTest(split=split):
                report = census(*split)
                self.assertEqual(report["candidate_maps"], maps)
                self.assertEqual(report["reaching_complement"], reachable)
                self.assertEqual(report["minimum_contact_histogram"], lengths)
                self.assertEqual(report["globally_sound_maps"], globally_sound)
                self.assertEqual(report["first_hit_sound_maps"], first_hit_sound)
                self.assertEqual(report["globally_sound_single_symbol_maps"], 0)
                self.assertEqual(report["first_hit_sound_single_symbol_maps"], 0)
                self.assertEqual(
                    report["globally_sound_identical_spent_pair_maps"], globally_sound
                )
                self.assertEqual(
                    report["first_hit_sound_identical_spent_pair_maps"], first_hit_sound
                )

    def test_small_enum_directly_checks_all_ordered_pairs(self) -> None:
        for zero_symbols, one_symbols in ((1, 1), (2, 1), (2, 2)):
            with self.subTest(split=(zero_symbols, one_symbols)):
                width = zero_symbols + one_symbols
                pairs = tuple(product(range(width), repeat=2))
                maps = tuple(enumerate_pair_maps(zero_symbols, one_symbols))
                self.assertEqual(len(set(maps)), len(maps))
                for rule in maps:
                    self.assertEqual(set(rule), set(pairs))
                    for (a, b), (c, d) in zip(pairs, rule, strict=True):
                        self.assertEqual(
                            sum(x >= zero_symbols for x in (a, b)),
                            sum(x >= zero_symbols for x in (c, d)),
                        )
                        self.assertEqual(rule[width * b + a], (d, c))

    def test_small_splits_against_direct_full_permutations_and_schedules(self) -> None:
        for split in ((1, 1), (2, 1), (1, 2)):
            with self.subTest(split=split):
                rules, lengths, global_total, first_total = direct_small_inventory(
                    *split
                )
                self.assertEqual(rules, set(enumerate_pair_maps(*split)))
                report = census(*split)
                self.assertEqual(report["minimum_contact_histogram"], lengths)
                self.assertEqual(report["globally_sound_maps"], global_total)
                self.assertEqual(report["first_hit_sound_maps"], first_total)

    def test_first_hit_only_rule_replays_a_later_false_positive(self) -> None:
        sample = census(2, 2)["first_hit_only_example"]
        if sample is None:
            self.fail("the census found no first-hit-only witness")
        good, bad = sample["correct_first_hit"], sample["later_wrong_hit"]
        self.assertEqual(
            good["states"],
            replay(sample["pair_map"], good["states"][0], good["contacts"]),
        )
        self.assertEqual(
            bad["states"], replay(sample["pair_map"], bad["states"][0], bad["contacts"])
        )
        self.assertTrue(good["is_charge_complement"])
        self.assertFalse(bad["is_charge_complement"])
        histogram = sample["positive_histogram"]
        self.assertEqual(
            tuple(good["states"][-1].count(x) for x in range(4)), histogram
        )
        self.assertEqual(tuple(bad["states"][-1].count(x) for x in range(4)), histogram)
        self.assertFalse(
            any(
                tuple(state.count(x) for x in range(4)) == histogram
                for state in good["states"][:-1]
            )
        )
        self.assertTrue(
            any(
                tuple(state.count(x) for x in range(4)) == histogram
                for state in bad["states"][:-1]
            )
        )

    def test_marker_is_locally_reversible_but_not_a_six_slot_certificate(self) -> None:
        self.assertEqual(pair_event(MARKER_MAP, (1, 1), (0, 1)), (4, 4))
        self.assertEqual(pair_event(MARKER_MAP, (4, 4), (0, 1)), (1, 1))
        report = marker_protocol()
        self.assertEqual(report["valid_starts"], 6)
        self.assertEqual(report["valid_component_sizes"], [7] * 6)
        self.assertEqual(report["valid_unique_two_marker_completions"], 6)
        self.assertEqual(report["other_fresh_starts"], 10)
        self.assertEqual(report["other_fresh_starts_with_marker"], 0)
        path = report["six_slot_counterexample"]
        self.assertEqual(path["states"][0], (2, 2, 2, 0, 0, 0))
        self.assertEqual(path["states"][-1], (4, 4, 2, 3, 3, 0))
        self.assertEqual(len(path["contacts"]), 3)
        self.assertEqual(
            path["states"], replay(MARKER_MAP, path["states"][0], path["contacts"])
        )
        self.assertFalse(path["is_charge_complement"])


if __name__ == "__main__":
    unittest.main()
