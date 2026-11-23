"""Finite completion and readout census for a shared reversible pair rule.

The scheduler supplies unordered contacts on four slots. The goal is the current
binary-charge complement of the particular fresh input, not just balanced
charge. The observer sees only the current symbol histogram. Global soundness
checks every positive in the uncut reachable graph. First-hit soundness checks
the first positive on each schedule from a fresh start, where the monitor is
initially armed. Nonvacuity requires some positive on a schedule from every fresh
half-filled start; neither notion requires one on every schedule.

The explicit 0,1 / 2,3 example adds a fifth symbol as a mark. Its successful
four-slot control and its six-slot false positive are finite statements only.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, deque
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import isqrt
from typing import Final, TypedDict

Pair = tuple[int, int]
PairMap = tuple[Pair, ...]
State = tuple[int, ...]
Histogram = tuple[int, ...]
Word = tuple[Pair, ...]

CONTACTS: Final[Word] = tuple(combinations(range(4), 2))
FRESH_START: Final[State] = (2, 2, 0, 0)
FIXED_WORD: Final[Word] = ((0, 1), (0, 2), (1, 3), (2, 3))
BASE_CHARGES: Final = (0, 0, 1, 1)
MARKED_CHARGES: Final = (*BASE_CHARGES, 0)


class Census(TypedDict):
    charge_split: Pair
    candidate_maps: int
    reaching_complement: int
    minimum_contact_histogram: dict[int, int]
    globally_sound_maps: int
    first_hit_sound_maps: int
    globally_sound_single_symbol_maps: int
    first_hit_sound_single_symbol_maps: int
    globally_sound_identical_spent_pair_maps: int
    first_hit_sound_identical_spent_pair_maps: int
    first_hit_only_example: FirstHitExample | None


class Trace(TypedDict):
    contacts: Word
    states: tuple[State, ...]
    is_charge_complement: bool


class FirstHitExample(TypedDict):
    pair_map: PairMap
    positive_histogram: Histogram
    correct_first_hit: Trace
    later_wrong_hit: Trace


class BasicProtocol(TypedDict):
    valid_starts: int
    component_sizes: list[int]
    input_dependent_matching_completions: int
    example: Trace
    fixed_word: Word
    fixed_word_completions: int
    fair_loop_word: Word
    fair_loop_noncompletions: int


class MarkerProtocol(TypedDict):
    valid_starts: int
    valid_component_sizes: list[int]
    valid_unique_two_marker_completions: int
    other_fresh_starts: int
    other_fresh_starts_with_marker: int
    six_slot_counterexample: Trace


def involution(width: int, swaps: tuple[tuple[Pair, Pair], ...]) -> PairMap:
    mapped = {pair: image for a, b in swaps for pair, image in ((a, b), (b, a))}
    return tuple(mapped.get((a, b), (a, b)) for a in range(width) for b in range(width))


BASIC_MAP: Final = involution(4, (((0, 2), (3, 1)), ((2, 0), (1, 3))))
MARKER_MAP: Final = involution(
    5, (((0, 2), (3, 1)), ((2, 0), (1, 3)), ((1, 1), (4, 4)))
)


def pair_event(rule: PairMap, state: State, contact: Pair) -> State:
    a, b = contact
    left, right = rule[isqrt(len(rule)) * state[a] + state[b]]
    after = list(state)
    after[a], after[b] = left, right
    return tuple(after)


def replay(rule: PairMap, start: State, word: Word) -> tuple[State, ...]:
    trace = [start]
    for contact in word:
        trace.append(pair_event(rule, trace[-1], contact))
    return tuple(trace)


def contact_paths(rule: PairMap, start: State) -> dict[State, Word]:
    paths: dict[State, Word] = {start: ()}
    queue = deque([start])
    contacts = tuple(combinations(range(len(start)), 2))
    while queue:
        before = queue.popleft()
        for contact in contacts:
            after = pair_event(rule, before, contact)
            if after not in paths:
                paths[after] = (*paths[before], contact)
                queue.append(after)
    return paths


def is_complement(start: State, current: State, charges: tuple[int, ...]) -> bool:
    return all(charges[a] != charges[b] for a, b in zip(start, current, strict=True))


def fresh_starts() -> tuple[State, ...]:
    return tuple(product((0, 2), repeat=4))


def trace(rule: PairMap, start: State, word: Word, charges: tuple[int, ...]) -> Trace:
    states = replay(rule, start, word)
    return {
        "contacts": word,
        "states": states,
        "is_charge_complement": is_complement(start, states[-1], charges),
    }


def basic_protocol() -> BasicProtocol:
    starts = [state for state in fresh_starts() if state.count(0) == 2]
    component_sizes = []
    matching_completions = fixed_completions = fair_noncompletions = 0
    fair_word = tuple(edge for edge in CONTACTS for _ in range(2))
    for start in starts:
        component_sizes.append(len(contact_paths(BASIC_MAP, start)))
        zeros = (i for i, symbol in enumerate(start) if symbol == 0)
        ones = (i for i, symbol in enumerate(start) if symbol == 2)
        matching = tuple(zip(zeros, ones, strict=True))
        matching_completions += trace(BASIC_MAP, start, matching, BASE_CHARGES)[
            "is_charge_complement"
        ]
        fixed_completions += trace(BASIC_MAP, start, FIXED_WORD, BASE_CHARGES)[
            "is_charge_complement"
        ]
        loop = replay(BASIC_MAP, start, fair_word)
        fair_noncompletions += loop[-1] == start and not any(
            is_complement(start, state, BASE_CHARGES) for state in loop
        )
    return {
        "valid_starts": len(starts),
        "component_sizes": component_sizes,
        "input_dependent_matching_completions": matching_completions,
        "example": trace(BASIC_MAP, FRESH_START, ((0, 2), (1, 3)), BASE_CHARGES),
        "fixed_word": FIXED_WORD,
        "fixed_word_completions": fixed_completions,
        "fair_loop_word": fair_word,
        "fair_loop_noncompletions": fair_noncompletions,
    }


def marker_protocol() -> MarkerProtocol:
    sizes = []
    unique_completions = invalid_count = invalid_marks = 0
    for start in fresh_starts():
        paths = contact_paths(MARKER_MAP, start)
        marked = [state for state in paths if 4 in state]
        if start.count(0) != 2:
            invalid_count += 1
            invalid_marks += bool(marked)
            continue
        sizes.append(len(paths))
        if len(marked) != 1 or marked[0].count(4) != 2:
            continue
        terminal = marked[0]
        inverse = [
            after
            for contact in CONTACTS
            if (after := pair_event(MARKER_MAP, terminal, contact)) != terminal
        ]
        unique_completions += (
            len(inverse) == 1
            and inverse[0] in paths
            and sorted(inverse[0]) == [1, 1, 3, 3]
            and is_complement(start, terminal, MARKED_CHARGES)
        )
    six_start = (2, 2, 2, 0, 0, 0)
    six_marked = (4, 4, 2, 3, 3, 0)
    six_word = contact_paths(MARKER_MAP, six_start)[six_marked]
    return {
        "valid_starts": len(sizes),
        "valid_component_sizes": sizes,
        "valid_unique_two_marker_completions": unique_completions,
        "other_fresh_starts": invalid_count,
        "other_fresh_starts_with_marker": invalid_marks,
        "six_slot_counterexample": trace(
            MARKER_MAP, six_start, six_word, MARKED_CHARGES
        ),
    }


def orbit_blocks(width: int, zeros: int) -> tuple[tuple[Pair, ...], ...]:
    # Reversal has two kinds of orbits: fixed diagonals and two-port orientations.
    # Orbit size and pair charge are the complete invariants for matching orbits.
    groups: dict[tuple[bool, int], list[Pair]] = {}
    for a, b in combinations_with_replacement(range(width), 2):
        groups.setdefault((a == b, int(a >= zeros) + int(b >= zeros)), []).append(
            (a, b)
        )
    return tuple(tuple(group) for group in groups.values())


def orbit_block_maps(
    block: tuple[Pair, ...],
) -> tuple[tuple[tuple[Pair, Pair], ...], ...]:
    maps: list[tuple[tuple[Pair, Pair], ...]] = []
    for image in permutations(block):
        if block[0][0] == block[0][1]:
            maps.append(tuple(zip(block, image, strict=True)))
            continue
        for orientations in product((0, 1), repeat=len(block)):
            rows: list[tuple[Pair, Pair]] = []
            for (a, b), (c, d), flip in zip(block, image, orientations, strict=True):
                if flip:
                    c, d = d, c
                rows.extend((((a, b), (c, d)), ((b, a), (d, c))))
            maps.append(tuple(rows))
    return tuple(maps)


def enumerate_pair_maps(zeros: int, ones: int) -> tuple[PairMap, ...]:
    """Exhaust permutations of port-reflection orbits and their orientations."""
    width = zeros + ones
    maps = []
    for blocks in product(
        *(orbit_block_maps(block) for block in orbit_blocks(width, zeros))
    ):
        rule: list[Pair] = [(0, 0)] * (width * width)
        for block in blocks:
            for (a, b), image in block:
                rule[width * a + b] = image
        maps.append(tuple(rule))
    return tuple(maps)


def representative(state: State) -> State:
    # S2 × S2 fixes the fresh input: quotient only within its original charge
    # groups. The true sitewise target and the anonymous observation descend.
    return (*sorted(state[:2]), *sorted(state[2:]))


class Quotient(TypedDict):
    targets: frozenset[int]
    observations: tuple[Histogram, ...]
    transitions: tuple[tuple[tuple[int, dict[Pair, int]], ...], ...]
    start: int


def quotient(zeros: int, ones: int) -> Quotient:
    width = zeros + ones
    charges = (0,) * zeros + (1,) * ones
    states = tuple(
        sorted(
            {
                representative(state)
                for state in product(range(width), repeat=4)
                if sum(charges[x] for x in state) == 2
            }
        )
    )
    indices = {state: index for index, state in enumerate(states)}
    start = (0, 0, zeros, zeros)
    # The full contact graph and equivariant uniform rule transport this search
    # to each of the six fresh masks, with goals and observations preserved.
    targets = frozenset(
        i for i, state in enumerate(states) if is_complement(start, state, charges)
    )
    observations = tuple(
        tuple(state.count(x) for x in range(width)) for state in states
    )
    # Cache all possible successors of each edge before considering individual
    # rules. The contact set is invariant under the start stabilizer.
    rows = []
    for state in states:
        edge_rows = []
        for a, b in CONTACTS:
            pair = state[a], state[b]
            successors: dict[Pair, int] = {}
            for c, d in product(range(width), repeat=2):
                output = c, d
                if sum(charges[x] for x in pair) == sum(charges[x] for x in output):
                    updated = list(state)
                    updated[a], updated[b] = output
                    successors[output] = indices[representative(tuple(updated))]
            edge_rows.append((width * pair[0] + pair[1], successors))
        rows.append(tuple(edge_rows))
    return {
        "targets": targets,
        "observations": observations,
        "transitions": tuple(rows),
        "start": indices[start],
    }


def quotient_paths(
    rule: PairMap, frame: Quotient
) -> tuple[dict[int, int], dict[int, tuple[int, ...]]]:
    start = frame["start"]
    edges: dict[int, tuple[int, ...]] = {}
    distances = {start: 0}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        successors = tuple(
            dict.fromkeys(
                choices[rule[pair]] for pair, choices in frame["transitions"][state]
            )
        )
        edges[state] = successors
        for after in successors:
            if after not in distances:
                distances[after] = distances[state] + 1
                queue.append(after)
    return distances, edges


def first_hits(
    positives: set[Histogram],
    frame: Quotient,
    edges: dict[int, tuple[int, ...]],
) -> tuple[set[Histogram], set[Histogram]]:
    start = frame["start"]
    seen = {start}
    pending = [start]
    good: set[Histogram] = set()
    bad: set[Histogram] = set()
    while pending:
        state = pending.pop()
        observation = frame["observations"][state]
        if observation in positives:
            (good if state in frame["targets"] else bad).add(observation)
        else:
            for after in edges[state]:
                if after not in seen:
                    seen.add(after)
                    pending.append(after)
    return good, bad


def maximal_first_hit_positives(
    candidates: set[Histogram],
    frame: Quotient,
    edges: dict[int, tuple[int, ...]],
) -> set[Histogram]:
    # A wrong first hit for a candidate also survives in every subset keeping
    # that candidate. Iteratively remove it; this cannot discard a sound subset.
    pending = candidates.copy()
    while pending:
        good, bad = first_hits(pending, frame, edges)
        if not bad:
            return good
        pending -= bad
    return set()


def first_hit_example(
    rule: PairMap, positive: Histogram, zeros: int, ones: int
) -> FirstHitExample:
    start = (0, 0, zeros, zeros)
    charges = (0,) * zeros + (1,) * ones
    paths = contact_paths(rule, start)
    good, wrong = None, None
    for state, path in paths.items():
        if tuple(state.count(x) for x in range(zeros + ones)) != positive:
            continue
        if good is None and is_complement(start, state, charges):
            good = trace(rule, start, path, charges)
        if wrong is None and not is_complement(start, state, charges):
            wrong = trace(rule, start, path, charges)
    if good is None or wrong is None:
        raise ArithmeticError(
            "first-hit-only histogram lacks a direct good or wrong occurrence"
        )
    return {
        "pair_map": rule,
        "positive_histogram": positive,
        "correct_first_hit": good,
        "later_wrong_hit": wrong,
    }


@cache
def census(zeros: int, ones: int) -> Census:
    frame = quotient(zeros, ones)
    start_hist = frame["observations"][frame["start"]]
    minimum: Counter[int] = Counter()
    globally_sound = first_hit_sound = 0
    global_single = first_hit_single = global_pair = first_hit_pair = 0
    witness = None
    spent = tuple(i for i in range(zeros + ones) if i not in (0, zeros))
    rules = enumerate_pair_maps(zeros, ones)
    for rule in rules:
        distances, edges = quotient_paths(rule, frame)
        reachable_targets = distances.keys() & frame["targets"]
        if not reachable_targets:
            continue
        minimum[min(distances[i] for i in reachable_targets)] += 1
        bad_hist = {
            frame["observations"][i] for i in distances if i not in frame["targets"]
        }
        # Unreachable labels cannot change a hit. A label occurring only on
        # wrong states can never be a sound first hit and need not be included
        # in any useful first-hit predicate.
        candidate = {frame["observations"][i] for i in reachable_targets} - {start_hist}
        global_positives = candidate - bad_hist
        first_positives = maximal_first_hit_positives(candidate, frame, edges)
        globally_sound += bool(global_positives)
        first_hit_sound += bool(first_positives)
        if witness is None and not global_positives:
            for observation in sorted(first_positives):
                good, bad = first_hits({observation}, frame, edges)
                if good and not bad:
                    witness = first_hit_example(rule, observation, zeros, ones)
                    break
        all_observations = {frame["observations"][i] for i in distances} - {start_hist}
        # For a specified spent letter, test whether seeing at least one copy
        # or an identical pair anywhere in the configuration suffices.
        global_symbol_tests = first_symbol_tests = global_pair_tests = (
            first_pair_tests
        ) = False
        for x in spent:
            for threshold in (1, 2):
                positives = {obs for obs in all_observations if obs[x] >= threshold}
                good, bad = first_hits(positives, frame, edges)
                globally_valid = bool(positives) and positives <= global_positives
                first_hit_valid = bool(good) and not bad
                if threshold == 1:
                    global_symbol_tests |= globally_valid
                    first_symbol_tests |= first_hit_valid
                else:
                    global_pair_tests |= globally_valid
                    first_pair_tests |= first_hit_valid
        global_single += global_symbol_tests
        first_hit_single += first_symbol_tests
        global_pair += global_pair_tests
        first_hit_pair += first_pair_tests
    return {
        "charge_split": (zeros, ones),
        "candidate_maps": len(rules),
        "reaching_complement": minimum.total(),
        "minimum_contact_histogram": dict(sorted(minimum.items())),
        "globally_sound_maps": globally_sound,
        "first_hit_sound_maps": first_hit_sound,
        "globally_sound_single_symbol_maps": global_single,
        "first_hit_sound_single_symbol_maps": first_hit_single,
        "globally_sound_identical_spent_pair_maps": global_pair,
        "first_hit_sound_identical_spent_pair_maps": first_hit_pair,
        "first_hit_only_example": witness,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--bundle", action="store_true", help="include the exhaustive pair-map census"
    )
    args = parser.parse_args()
    report: dict[str, object] = {
        "basic_protocol": basic_protocol(),
        "marker_protocol": marker_protocol(),
    }
    if args.bundle:
        report["census"] = [census(*split) for split in ((1, 1), (2, 1), (2, 2))]
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
