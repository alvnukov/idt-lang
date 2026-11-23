"""Finite localization test for a fixed anonymous shell rule.

Supply a simple cubic H, its doubled graph H □ K2, a rung matching M and
an externally flipped first-layer star. Only the simulator's *preparation*
and the independent oracle know these data. The event kernel sees just an
edge word, a center and the four unordered pairs (bit, other-edge count).
No time law or preference among offered centers is supplied.

Test the entire one-root move graph, not a chosen history. Compare it to
the incidence subdivision of H and recover the matching from each reached
word without giving the decoder either layer. Scan all 256 existing anonymous
shell rules, including their possible partial-star events. Distinguish raw
contact from completed relocation, one-root from multiroot preparations,
and observational aliases from an identified law. Finite graph evidence
only; neither space, an observer, motion direction nor Born weights follow.

Run: python3 -m scripts.probe_localized_shell_packets
"""

from __future__ import annotations

import json
from collections import deque
from dataclasses import asdict, dataclass
from functools import cache
from itertools import combinations

from scripts.probe_anonymous_shell_rules import local_image
from scripts.probe_facilitated_forest_signal import (
    Incidence,
    Moves,
    carriers,
    distances,
    edge,
    indices,
    lift,
    need,
    raw_orbits,
)

Subset = frozenset[int]
View = tuple[tuple[int, ...], int]


def fixtures() -> dict[str, Incidence]:
    named = carriers()
    result = {k: named[k] for k in ("cube", "prism_c5", "k4", "k33", "triangle_prism")}
    # Generalized Petersen G(5,2); Heawood is the 14-cycle with LCF [5,-5]^7.
    result["petersen"] = Incidence.from_edges(
        10,
        [(v, (v + 1) % 5) for v in range(5)]
        + [(v, v + 5) for v in range(5)]
        + [(v + 5, (v + 2) % 5 + 5) for v in range(5)],
        3,
    )
    result["heawood"] = Incidence.from_edges(
        14,
        [(v, (v + 1) % 14) for v in range(14)]
        + [(v, (v + 5) % 14) for v in range(0, 14, 2)],
        3,
    )
    return result


@cache
def delta(rule: int, view: View) -> int:
    scores, marks = view
    return marks ^ local_image(rule, scores, marks)


class RawShell:
    """Local port slots are only a storage convention for the anonymous rule."""

    def __init__(self, graph: Incidence):
        self.graph = graph
        self.ports = tuple(
            tuple(
                (
                    graph.edge_bits[edge(v, w)],
                    graph.stars[w] ^ graph.edge_bits[edge(v, w)],
                )
                for w in sorted(row)
            )
            for v, row in enumerate(graph.neighbors)
        )

    def view(self, state: int, v: int) -> View:
        ports = self.ports[v]
        return (
            tuple((state & rest).bit_count() for _, rest in ports),
            sum(1 << i for i, (bit, _) in enumerate(ports) if state & bit),
        )

    def offers(self, state: int, rule: int) -> dict[int, int]:
        offers = {}
        for v, star in enumerate(self.graph.stars):
            if (state & star).bit_count() != 2:
                continue
            change = delta(rule, self.view(state, v))
            if change:
                offers[v] = state ^ sum(self.ports[v][i][0] for i in indices(change))
        return offers

    def orbit(self, start: int, rule: int) -> Moves:
        rows: Moves = {}
        todo = deque([start])
        while todo:
            state = todo.popleft()
            if state in rows:
                continue
            rows[state] = self.offers(state, rule)
            todo.extend(t for t in rows[state].values() if t not in rows)
        need(
            all(rows[t].get(v) == s for s, row in rows.items() for v, t in row.items()),
            "nonreciprocal raw shell event",
        )
        return rows


def packet_oracle(base: Incidence) -> dict[Subset, frozenset[int]]:
    """Only pure H incidence: center labels on singleton↔edge transitions."""
    return {
        **{frozenset([v]): ns for v, ns in enumerate(base.neighbors)},
        **{frozenset([u, v]): frozenset([u, v]) for u, v in base.edge_bits},
    }


def decode(raw: Incidence, state: int) -> tuple[Subset, int]:
    """Read raw degrees, recover the unique marked-degree≥2 mate of each zero."""
    degree = [(state & star).bit_count() for star in raw.stars]
    mates = set()
    for v, d in enumerate(degree):
        if d == 0:
            candidates = [w for w in raw.neighbors[v] if degree[w] >= 2]
            need(len(candidates) == 1, "no unique high-degree neighbor of a zero")
            mates.add(candidates[0])
    return frozenset(mates), raw.prepare(state, mates)


@dataclass(frozen=True)
class RuleScan:
    rules: tuple[int, ...]
    # (subset, center, oracle delta, flag32 delta), local deltas are port masks.
    flag32_mismatch: tuple[tuple[int, ...], int, int, int] | None


def rule_scan(base: Incidence) -> RuleScan:
    raw, rungs = lift(base)
    shell = RawShell(raw)
    constraints: set[tuple[View, int]] = set()
    mismatch = None
    for subset, expected in packet_oracle(base).items():
        state = raw.prepare(sum(rungs), subset)
        for v in range(len(raw.stars)):
            view = shell.view(state, v)
            wanted = 15 if v in expected else 0
            constraints.add((view, wanted))
            if mismatch is None and delta(32, view) != wanted:
                mismatch = tuple(sorted(subset)), v, wanted, delta(32, view)
    rules = tuple(
        r for r in range(256) if all(delta(r, v) == d for v, d in constraints)
    )
    return RuleScan(rules, mismatch)


@dataclass(frozen=True)
class OrbitResult:
    rule: int
    states: int
    undirected_events: int
    recovered_matchings: int
    ordered_distances: int
    # (d_H, first absent rung under selected rule, first under 255, singleton distance under both)
    metrics: tuple[tuple[int, int, int, int], ...]


def check_orbit(base: Incidence, rule: int) -> OrbitResult:
    raw, rungs = lift(base)
    background = sum(rungs)
    shell = RawShell(raw)
    need(not shell.offers(background, rule), "matching itself should idle")
    start = raw.prepare(background, [0])
    n = len(base.stars)
    rows = shell.orbit(start, rule)
    oracle = packet_oracle(base)
    words = {s: raw.prepare(background, s) for s in oracle}
    need(set(words.values()) == rows.keys(), "raw orbit differs from incidence states")
    for s, word in words.items():
        need(
            {v for v, star in enumerate(raw.stars) if not word & star}
            == {v + n for v in s},
            "degree-zero centers are not exactly the opposite copy of the support",
        )
        need(decode(raw, word) == (s, background), "raw-only decoder mismatch")
        expected = {v: words[s ^ {v}] for v in oracle[s]}
        need(rows[word] == expected, "raw labeled event differs from incidence oracle")
    # The previous probe's score-independent half-star kernel is rule 255:
    # applying both complementary partial deltas also flips the entire star.
    free = raw_orbits(raw, [start])
    graphs = [
        {s: tuple(row.values()) for s, row in table.items()} for table in (rows, free)
    ]
    metrics = set()
    for x in range(n):
        d_h = distances(dict(enumerate(base.neighbors)), x)
        root = words[frozenset([x])]
        near, broad = (distances(graph, root) for graph in graphs)
        for y, rung in enumerate(rungs):
            d = d_h[y]
            target = words[frozenset([y])]
            first = min(k for w, k in near.items() if not w & rung)
            first_free = min(k for w, k in broad.items() if not w & rung)
            need(first == max(0, 2 * d - 1) and first_free == d, "wrong first contact")
            need(near[target] == broad[target] == 2 * d, "wrong singleton relocation")
            metrics.add((d, first, first_free, near[target]))
    return OrbitResult(
        rule,
        len(rows),
        sum(map(len, rows.values())) // 2,
        len(words),
        n * n,
        tuple(sorted(metrics)),
    )


@cache
def active_flags(view: View) -> int:
    return sum(1 << i for i in range(8) if delta(1 << i, view))


@dataclass(frozen=True)
class UpperCuts:
    states: int
    visible_flags: int


def upper_cuts(base: Incidence) -> UpperCuts:
    raw, rungs = lift(base)
    shell = RawShell(raw)
    count = 1 << len(base.stars)
    seen = 0
    for mask in range(count):
        word = raw.prepare(sum(rungs), indices(mask))
        for v, star in enumerate(raw.stars):
            if (word & star).bit_count() == 2:
                seen |= active_flags(shell.view(word, v))
    return UpperCuts(count, seen)


@dataclass(frozen=True)
class Intervention:
    extra: int
    center: int
    view: View
    firing_rules: tuple[int, ...]


def split_aliases(
    cube: Incidence, aliases: tuple[int, ...]
) -> tuple[Intervention, ...]:
    raw, rungs = lift(cube)
    shell = RawShell(raw)
    rows = []
    for extra in (8, 10):
        word = raw.prepare(sum(rungs), (0, 1, extra))
        rows.append(
            Intervention(
                extra,
                3,
                shell.view(word, 3),
                tuple(r for r in aliases if 3 in shell.offers(word, r)),
            )
        )
    return tuple(rows)


def component_sizes(base: Incidence, subset: Subset) -> tuple[int, ...]:
    graph = {v: subset & base.neighbors[v] for v in subset}
    remaining = set(subset)
    sizes = []
    while remaining:
        component = distances(graph, next(iter(remaining)))
        remaining.difference_update(component)
        sizes.append(len(component))
    return tuple(sorted(sizes))


@dataclass(frozen=True)
class ThreeRoots:
    subsets: tuple[tuple[int, ...], ...]
    centers: tuple[int, int]
    component_sizes: tuple[tuple[int, ...], ...]


def three_root_counterexample(base: Incidence) -> ThreeRoots:
    """Short direct raw plays; report an independent-three-root start that branches."""
    raw, rungs = lift(base)
    bg = sum(rungs)
    shell = RawShell(raw)
    n = len(base.stars)
    for roots in combinations(range(n), 3):
        s = frozenset(roots)
        if component_sizes(base, s) != (1, 1, 1):
            continue
        for v, first in shell.offers(raw.prepare(bg, s), 32).items():
            if v >= n or v in s:
                continue
            t = s | {v}
            for w, second in shell.offers(first, 32).items():
                if w >= n or w in t:
                    continue
                u = t | {w}
                if component_sizes(base, u) == (1, 1, 3):
                    need(
                        first == raw.prepare(bg, t) and second == raw.prepare(bg, u),
                        "raw multiroot event is not the reported cut",
                    )
                    sets = (s, t, u)
                    return ThreeRoots(
                        tuple(tuple(sorted(x)) for x in sets),
                        (v, w),
                        tuple(component_sizes(base, x) for x in sets),
                    )
    raise ArithmeticError("no three-root enlargement witness on this carrier")


@dataclass(frozen=True)
class TwoRoots:
    roots: tuple[int, int]
    distance: int
    initial_offers: tuple[int, ...]
    union_solo_offers: tuple[int, ...]
    raw_component: int
    component_profiles: tuple[tuple[int, ...], ...]
    shortest_enlargement: tuple[int, ...] | None


def two_root_control(base: Incidence, roots: tuple[int, int]) -> TwoRoots:
    """Initial superposition check and actual orbit, with no independence filter."""
    raw, rungs = lift(base)
    shell = RawShell(raw)
    bg = sum(rungs)
    start = raw.prepare(bg, roots)
    rows = shell.orbit(start, 32)
    solo = set().union(*(shell.offers(raw.prepare(bg, [v]), 32) for v in roots))
    steps = distances({s: row.values() for s, row in rows.items()}, start)
    profiles = {}
    for word in rows:
        s = frozenset(v for v, r in enumerate(rungs) if not r & word)
        need(raw.prepare(bg, s) == word, "pair row escaped upper cuts")
        profiles[word] = component_sizes(base, s)
        need(len(profiles[word]) == 2, "pair's induced component count changed")
    enlarged = [word for word, parts in profiles.items() if max(parts) > 2]
    witness = None
    if enlarged:
        at = min(enlarged, key=lambda w: (steps[w], w))
        back = []
        while at != start:
            v, at = next(
                (v, w) for v, w in rows[at].items() if steps[w] == steps[at] - 1
            )
            back.append(v)
        witness = tuple(reversed(back))
        at = start
        for v in witness:
            at = rows[at][v]
        need(max(profiles[at]) > 2, "shortest enlargement trace did not replay")
    return TwoRoots(
        roots,
        distances(dict(enumerate(base.neighbors)), roots[0])[roots[1]],
        tuple(sorted(rows[start])),
        tuple(sorted(solo)),
        len(rows),
        tuple(sorted(set(profiles.values()))),
        witness,
    )


@dataclass(frozen=True)
class Report:
    scope: str
    scans: dict[str, RuleScan]
    orbits: dict[str, OrbitResult]
    upper_cuts: dict[str, UpperCuts]
    common_cut_aliases: tuple[int, ...]
    cube_interventions: tuple[Intervention, ...]
    three_roots: ThreeRoots
    two_roots: dict[str, TwoRoots]


def localized_shell_packets() -> Report:
    cases = fixtures()
    scans = {name: rule_scan(g) for name, g in cases.items()}
    selected = {"cube": 32, "prism_c5": 32, "petersen": 32, "heawood": 32, "k4": 2}
    orbits = {name: check_orbit(cases[name], rule) for name, rule in selected.items()}
    cuts = {name: upper_cuts(cases[name]) for name in ("cube", "prism_c5", "petersen")}
    visible = 0
    for row in cuts.values():
        visible |= row.visible_flags
    # Selector deltas at a view are disjoint; equality on all visible bits is
    # necessary as well as sufficient for equality of every raw transition.
    aliases = tuple(r for r in range(256) if (r ^ 32) & visible == 0)
    pairs = {
        "cube_near": (cases["cube"], (0, 2)),
        "cube_antipodes": (cases["cube"], (0, 6)),
        "k33_twins": (cases["k33"], (0, 1)),
        "prism_c6_far": (carriers()["prism_c6"], (0, 9)),
    }
    return Report(
        "Finite conditional event counts on a supplied graph, matching and external "
        "preparations; not an intrinsic spatial dimension, observer, directed motion "
        "or probability law.",
        scans,
        orbits,
        cuts,
        aliases,
        split_aliases(cases["cube"], aliases),
        three_root_counterexample(cases["heawood"]),
        {name: two_root_control(g, pair) for name, (g, pair) in pairs.items()},
    )


if __name__ == "__main__":
    print(json.dumps(asdict(localized_shell_packets()), sort_keys=True))
