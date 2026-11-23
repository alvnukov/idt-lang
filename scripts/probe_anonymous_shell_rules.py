"""Finite census of reversible rules on four ports with two marks.

Only equality of the four other-edge population scores is supplied. Score
names and port order carry no information. Non-half-filled centers idle by
convention, not as a consequence of reversibility. Each move chooses one
center; no scheduler or probability measure is supplied. Triangle parity is
a constructed diagnostic, not an input to a rule or a free particle.

Run: python3 -m scripts.probe_anonymous_shell_rules
"""

import json
import sys
from collections import Counter, deque
from dataclasses import asdict, dataclass
from functools import cache
from itertools import permutations
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_neighbor_twins_flux import (
    K5,
    OCTAHEDRON,
    Incidence,
    Offers,
    components,
)

MARKS = (3, 5, 6, 9, 10, 12)
REPRESENTATIVES = ((0, 0, 0, 0), (0, 0, 0, 1), (0, 1, 2, 3), (0, 0, 1, 1), (0, 0, 1, 2))


def partition(scores: tuple[int, ...]) -> tuple[int, ...]:
    """Unordered classes of equal scores, as four-bit port masks."""
    if len(scores) != 4:
        raise ValueError(
            "exactly four ports required; larger shells are outside this class"
        )
    return tuple(
        sorted(sum(1 << i for i, s in enumerate(scores) if s == v) for v in set(scores))
    )


def _permute(mask: int, perm: tuple[int, ...]) -> int:
    return sum(1 << j for i, j in enumerate(perm) if mask & (1 << i))


def centralizer(classes: tuple[int, ...]) -> set[tuple[int, ...]]:
    """Brute force all 6! bijections, independently of the named flags."""
    actions = [
        {m: _permute(m, perm) for m in MARKS}
        for perm in permutations(range(4))
        if {_permute(c, perm) for c in classes} == set(classes)
    ]
    result = set()
    for values in permutations(MARKS):
        f = dict(zip(MARKS, values, strict=True))
        if all(f[g[m]] == g[f[m]] for g in actions for m in MARKS):
            result.add(values)
    return result


@cache
def _moves(classes: tuple[int, ...], marks: int) -> tuple[tuple[int, int], ...]:
    """Independent (selector bit, xor mask) moves; zero, one or two apply."""
    if marks not in MARKS:
        return ()
    if len(classes) == 1:
        return ((1, 15),)
    if len(classes) == 4:
        return ((4, 15),)
    doubles = tuple(c for c in classes if c.bit_count() == 2)
    if not doubles:
        return ((2, 15),)
    if len(doubles) == 2:
        return ((8 if marks in doubles else 16, 15),)
    d = doubles[0]
    if marks in (d, 15 ^ d):
        return ((32, 15),)
    return ((64, d), (128, 15 ^ d))


def local_image(rule: int, scores: tuple[int, ...], marks: int) -> int:
    if not 0 <= rule < 256 or not 0 <= marks < 16:
        raise ValueError("expected an eight-bit rule and a four-bit port state")
    out = marks
    for flag, delta in _moves(partition(scores), marks):
        if rule & flag:
            out ^= delta
    return out


def tagged_control(scores: tuple[int, ...], marks: int) -> int:
    """Reversible but outside the class: complement at the absolute all-zero tag."""
    return marks ^ 15 if scores == (0, 0, 0, 0) and marks in MARKS else marks


def check_local_class() -> tuple[int, ...]:
    sizes = []
    for scores in REPRESENTATIVES:
        commuting = centralizer(partition(scores))
        encoded = {tuple(local_image(r, scores, m) for m in MARKS) for r in range(256)}
        if encoded != commuting:
            raise ValueError(
                "named flags do not match the independently enumerated centralizer"
            )
        for row in commuting:
            f = dict(zip(MARKS, row, strict=True))
            if any(f[f[m]] != m or f[15 ^ m] != 15 ^ f[m] for m in MARKS):
                raise ValueError("not involutive or not complement-equivariant")
        sizes.append(len(commuting))
    return tuple(sizes)


@dataclass(frozen=True)
class EventTemplate:
    center: int
    first: int
    delta: int
    second: int
    other: int


def _templates(
    graph: Incidence, states: tuple[int, ...]
) -> dict[int, list[EventTemplate]]:
    result: dict[int, list[EventTemplate]] = {}
    for state in states:
        row = []
        for center, star in enumerate(graph.stars):
            marks = sum(((state >> e) & 1) << j for j, e in enumerate(star))
            deltas = _moves(partition(graph.scores(state, center)), marks)
            if deltas:
                lifted = [
                    (flag, sum(1 << e for j, e in enumerate(star) if mask & (1 << j)))
                    for flag, mask in deltas
                ]
                first, delta = lifted[0]
                second, other = lifted[1] if len(lifted) == 2 else (0, 0)
                row.append(EventTemplate(center, first, delta, second, other))
        result[state] = row
    return result


def _offers(templates: dict[int, list[EventTemplate]], rule: int) -> Offers:
    moves: Offers = {}
    for state, row in templates.items():
        edges = {}
        for event in row:
            delta = event.delta if rule & event.first else 0
            if rule & event.second:
                delta ^= event.other
            if delta:
                edges[event.center] = state ^ delta
        moves[state] = edges
    if any(
        moves[target].get(c) != s
        for s, row2 in moves.items()
        for c, target in row2.items()
    ):
        raise ValueError("nonreversible microscopic edge")
    return moves


@dataclass(frozen=True)
class PathExample:
    distances: dict[int, int]  # across all starts, excluding unreachable starts
    unreachable: int
    centers: tuple[int, ...]
    states: tuple[int, ...]
    parities: tuple[int, ...]


def _shortest(offers: Offers, parity: dict[int, int]) -> PathExample:
    distances: Counter[int] = Counter()
    unreachable = 0
    best: tuple[tuple[int, ...], tuple[int, ...]] | None = None
    for start, initial in parity.items():
        if initial.bit_count() != 2:
            continue
        queue = deque([start])
        via: dict[int, tuple[int, int]] = {}
        seen = {start}
        while queue:
            cur = queue.popleft()
            if parity[cur] != initial and parity[cur].bit_count() == 2:
                states = [cur]
                centers = []
                while cur != start:
                    cur, center = via[cur]
                    centers.append(center)
                    states.append(cur)
                distances[len(centers)] += 1
                if best is None or len(centers) < len(best[0]):
                    best = tuple(reversed(centers)), tuple(reversed(states))
                break
            for center, target in offers[cur].items():
                if target not in seen:
                    seen.add(target)
                    via[target] = cur, center
                    queue.append(target)
        else:
            unreachable += 1
    if best is None:
        raise ValueError("no relocation witness")
    return PathExample(
        dict(distances), unreachable, *best, tuple(parity[s] for s in best[1])
    )


@dataclass(frozen=True)
class Census:
    states: int
    two_odd_starts: int
    parity_preserving: int
    transfer_counts: dict[int, int]  # relocatable starts -> number of rules
    cheapest: tuple[int, ...]
    examples: dict[int, PathExample]
    # Indexed by eight-bit rule; counts refer to microscopic starts, not syndromes.
    by_rule: tuple[tuple[bool, int], ...]  # (some parity change, relocatable starts)


def census(graph: Incidence) -> Census:
    states = graph.half_filled()
    templates = _templates(graph, states)
    parity = {s: graph.triangle_parities(s) for s in states}
    rows = []
    for rule in range(256):
        moves = _offers(templates, rule)
        changed = False
        relocated = 0
        for group in components(moves):
            syndromes = {parity[s] for s in group}
            changed |= len(syndromes) > 1
            if sum(mask.bit_count() == 2 for mask in syndromes) > 1:
                relocated += sum(parity[s].bit_count() == 2 for s in group)
        rows.append((changed, relocated))
    hits = [r for r, (_, n) in enumerate(rows) if n]
    cost = min((r.bit_count() for r in hits), default=None)
    cheapest = tuple(r for r in hits if r.bit_count() == cost)
    return Census(
        len(states),
        sum(m.bit_count() == 2 for m in parity.values()),
        sum(not change for change, _ in rows),
        dict(Counter(n for _, n in rows)),
        cheapest,
        {r: _shortest(_offers(templates, r), parity) for r in cheapest},
        tuple(rows),
    )


def main() -> None:
    print(
        json.dumps(
            {
                "local_class_sizes_in_order_4_31_1111_22_211": check_local_class(),
                "simplicity": "number of active orbit flags in this encoding only",
                "scope": "fixed four ports, equality-only shells; no closure on larger neighborhoods",
                "readout": "triangle parity on supplied incidence; paths need not preserve odd count",
                "absolute_tag_control_all_zero_vs_all_one_on_mask_3": [
                    tagged_control((s,) * 4, 3) for s in (0, 1)
                ],
                "K5": asdict(census(K5)),
                "octahedron": asdict(census(OCTAHEDRON)),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
