"""Conditional graph-metric readout from actual half-filled star moves.

Supply a connected simple cubic graph H and two copies joined by rungs G =
H □ K2. Mark just the rungs (M), then externally complement the star at a
chosen root on the first side. M itself is stationary. The only allowed
move, frozen shell rule 255, complements a four-edge star with two marks.
There is no probability, scheduler, or external tick in the move count.

In a raw word M XOR cut(S), S on the first side, each rung is 1−s_v and
each first-side horizontal bit is s_u XOR s_v. If k first-side neighbors
belong to S, the star has 1+k marks outside S and 3−k inside S. Thus a move
adds or removes a leaf exactly when k=1, and the opposite side never
fires. Independently enumerate raw edges and compare against this oracle.
Every induced tree shrinks to a singleton; every induced two-component
forest shrinks to an independent pair. Loop parities are unchanged by a
cut. The graph of independent-pair token slides is a separate distance
oracle checked on these finite carriers, not a restriction imposed on the
raw BFS. From singleton x, the union of all occupied vertices visited by
any event word is connected. To touch y it must contain at least d_H(x,y)
added vertices; to finish at singleton y every distinct intermediate
vertex must be both added and removed. Growing a shortest path, and then
pruning it from x, attains the two lower bounds.

For the pair comparison, track one representative in each component. An
addition needs no representative move. When its current vertex is removed,
move the representative to that vertex's unique remaining neighbor. The
representatives stay nonadjacent, and take at most one slide per deletion
(half the events on pair-to-pair words). Conversely, a nonadjacent slide
can be expanded into a leaf addition followed by a leaf removal. Thus
this comparison does not assume a separate two-particle update law.

Contrast probe_relational_signal_metric: that probe supplies a common tick
and measures dispatch moments; this one counts possible one-center events.
The matching, layer and preparation are supplied resources. No carrier
dimension, autonomous source, observer clock or physical space is derived.

Run: python3 -m scripts.probe_facilitated_forest_signal
"""

from __future__ import annotations

import json
from collections import Counter, deque
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import asdict, dataclass
from itertools import combinations, product
from typing import TypeVar

Edge = tuple[int, int]
Moves = dict[int, dict[int, int]]  # raw state -> center -> raw state
Node = TypeVar("Node")


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ArithmeticError(message)


def edge(u: int, v: int) -> Edge:
    return (u, v) if u < v else (v, u)


def indices(mask: int) -> Iterator[int]:
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def distances(graph: Mapping[Node, Iterable[Node]], root: Node) -> dict[Node, int]:
    distance = {root: 0}
    todo = deque([root])
    while todo:
        u = todo.popleft()
        for v in graph[u]:
            if v not in distance:
                distance[v] = distance[u] + 1
                todo.append(v)
    return distance


@dataclass(frozen=True)
class Incidence:
    neighbors: tuple[frozenset[int], ...]
    edge_bits: dict[Edge, int]
    stars: tuple[int, ...]

    @classmethod
    def from_edges(cls, order: int, edges: Iterable[Edge], degree: int) -> Incidence:
        sorted_edges = sorted(edge(u, v) for u, v in edges)
        need(len(set(sorted_edges)) == len(sorted_edges), "repeated edge")
        neighbors: list[set[int]] = [set() for _ in range(order)]
        stars = [0] * order
        bits = {}
        for i, (u, v) in enumerate(sorted_edges):
            need(0 <= u < v < order, "bad simple incidence")
            bits[u, v] = 1 << i
            stars[u] |= bits[u, v]
            stars[v] |= bits[u, v]
            neighbors[u].add(v)
            neighbors[v].add(u)
        need(all(len(row) == degree for row in neighbors), "wrong vertex degree")
        need(
            len(distances(dict(enumerate(neighbors)), 0)) == order, "disconnected graph"
        )
        return cls(tuple(map(frozenset, neighbors)), bits, tuple(stars))

    def prepare(self, background: int, vertices: Iterable[int]) -> int:
        """External intervention, not a native event from the matching."""
        for v in vertices:
            background ^= self.stars[v]
        return background

    def offers(self, state: int) -> dict[int, int]:
        offers = {}
        for center, star in enumerate(self.stars):
            target = half_filled_star_step(state, star)
            if target != state:
                offers[center] = target
        return offers

    def cycle_basis(self) -> tuple[int, ...]:
        """Each non-tree edge plus the two tree paths to its endpoints."""
        paths = {0: 0}
        todo = deque([0])
        while todo:
            u = todo.popleft()
            for v in sorted(self.neighbors[u]):
                if v not in paths:
                    paths[v] = paths[u] ^ self.edge_bits[edge(u, v)]
                    todo.append(v)
        cycles = tuple(
            paths[u] ^ paths[v] ^ mark
            for (u, v), mark in self.edge_bits.items()
            if paths[u] ^ paths[v] != mark
        )
        need(
            len(cycles) == len(self.edge_bits) - len(self.stars) + 1, "wrong cycle rank"
        )
        return cycles


def half_filled_star_step(state: int, star: int) -> int:
    """The score-independent, four-port specialization of frozen rule 255."""
    return state ^ star if (state & star).bit_count() == 2 else state


def raw_orbits(incidence: Incidence, starts: Iterable[int]) -> Moves:
    """No knowledge of rung bits, forests, pair slides or target labels."""
    rows: Moves = {}
    todo = deque(dict.fromkeys(starts))
    while todo:
        before = todo.popleft()
        if before not in rows:
            rows[before] = incidence.offers(before)
            todo.extend(after for after in rows[before].values() if after not in rows)
    need(
        all(
            rows[after].get(v) == before
            for before, row in rows.items()
            for v, after in row.items()
        ),
        "raw offer not reversible at its own center",
    )
    return rows


def prism_edges(n: int) -> tuple[Edge, ...]:
    return tuple(
        [edge(i, (i + 1) % n) for i in range(n)]
        + [edge(i + n, (i + 1) % n + n) for i in range(n)]
        + [(i, i + n) for i in range(n)]
    )


def carriers() -> dict[str, Incidence]:
    fixtures = {
        "k4": (4, tuple(combinations(range(4), 2))),
        "k33": (6, tuple(product(range(3), range(3, 6)))),
        "triangle_prism": (6, prism_edges(3)),
        "cube": (8, prism_edges(4)),
        "prism_c5": (10, prism_edges(5)),
        "prism_c6": (12, prism_edges(6)),
    }
    return {
        name: Incidence.from_edges(n, edges, 3) for name, (n, edges) in fixtures.items()
    }


def lift(base: Incidence) -> tuple[Incidence, tuple[int, ...]]:
    n = len(base.neighbors)
    edges = tuple(base.edge_bits)
    rungs = tuple((v, v + n) for v in range(n))
    raw = Incidence.from_edges(
        2 * n, (*edges, *((u + n, v + n) for u, v in edges), *rungs), 4
    )
    return raw, tuple(raw.edge_bits[e] for e in rungs)


def forest_counts(base: Incidence, subset: int) -> tuple[int, int]:
    """Independent induced subgraph census, not a closure under leaf moves."""
    vertices = set(indices(subset))
    remaining = set(vertices)
    components = 0
    while remaining:
        components += 1
        todo = [remaining.pop()]
        while todo:
            discovered = remaining & base.neighbors[todo.pop()]
            remaining.difference_update(discovered)
            todo.extend(discovered)
    return components, sum(u in vertices and v in vertices for u, v in base.edge_bits)


def compare_forest_oracle(
    base: Incidence, raw: Incidence, rungs: tuple[int, ...], sectors: dict[int, Moves]
) -> int:
    n = len(base.neighbors)
    background = sum(rungs)
    neighbor_masks = tuple(sum(1 << w for w in row) for row in base.neighbors)
    expected: dict[int, set[int]] = {k: set() for k in sectors}
    for subset in range(1, 1 << n):
        parts, internal_edges = forest_counts(base, subset)
        if parts in expected and internal_edges == subset.bit_count() - parts:
            expected[parts].add(subset)

    cycles = raw.cycle_basis()
    for k, rows in sectors.items():
        projections = {}
        for state, row in rows.items():
            subset = sum(1 << v for v, rung in enumerate(rungs) if not state & rung)
            projections[state] = subset
            need(
                state == raw.prepare(background, indices(subset)),
                "raw word is not the cut encoded by its rung projection",
            )
            need(
                state.bit_count() == background.bit_count() + 2 * k,
                "raw moves did not preserve the preparation mark budget",
            )
            need(
                all(
                    ((state ^ background) & cycle).bit_count() % 2 == 0
                    for cycle in cycles
                ),
                "a background loop parity changed",
            )
            need(
                row.keys()
                == {
                    v
                    for v, ns in enumerate(neighbor_masks)
                    if (subset & ns).bit_count() == 1
                },
                "raw offers disagree with a first-side leaf move",
            )
            need(
                all(
                    after == raw.prepare(background, indices(subset ^ (1 << v)))
                    for v, after in row.items()
                ),
                "raw step disagrees with projected leaf toggle",
            )
        need(
            set(projections.values()) == expected[k],
            "raw orbit is not the full induced forest census",
        )
    return len(cycles)


def check_relabel(raw: Incidence, rows: Moves, n: int) -> int:
    """Permute both layers into one interleaved labeling; replay every offer."""
    image = tuple(2 * v + 1 for v in reversed(range(n))) + tuple(
        2 * v for v in range(n)
    )
    relabelled_edges = tuple(edge(image[u], image[v]) for u, v in raw.edge_bits)
    relabelled = Incidence.from_edges(2 * n, relabelled_edges, 4)
    transport = tuple(relabelled.edge_bits[e] for e in relabelled_edges)

    def encode(state: int) -> int:
        return sum(transport[i] for i in indices(state))

    images = {state: encode(state) for state in rows}
    for before, row in rows.items():
        need(
            relabelled.offers(images[before])
            == {image[v]: images[after] for v, after in row.items()},
            "raw move graph changed under vertex/port relabeling",
        )
    return len(images)


def singleton_comparisons(
    base: Incidence, raw_rows: Moves, singleton: tuple[int, ...], rungs: tuple[int, ...]
) -> tuple[tuple[int, int], ...]:
    abstract = dict(enumerate(base.neighbors))
    measured = {state: tuple(row.values()) for state, row in raw_rows.items()}
    histogram: Counter[int] = Counter()
    for x, source in enumerate(singleton):
        raw_distance = distances(measured, source)
        carrier_distance = distances(abstract, x)
        for y, (target, rung) in enumerate(zip(singleton, rungs, strict=True)):
            arrival = min(k for state, k in raw_distance.items() if not state & rung)
            need(
                raw_distance[target] == 2 * carrier_distance[y],
                "wrong singleton distance",
            )
            need(arrival == carrier_distance[y], "wrong target rung first-arrival")
            if x < y:
                histogram[raw_distance[target]] += 1
    return tuple(sorted(histogram.items()))


def pair_comparisons(
    base: Incidence, raw_rows: Moves, seeds: dict[Edge, int]
) -> tuple[tuple[int, ...], int]:
    slides = {
        (x, y): tuple(
            edge(moving, still)
            for old, still in ((x, y), (y, x))
            for moving in base.neighbors[old]
            if moving != still and moving not in base.neighbors[still]
        )
        for x, y in seeds
    }
    measured = {state: tuple(row.values()) for state, row in raw_rows.items()}
    missing = 0
    unseen = set(raw_rows)
    sector_sizes = []
    for source, raw_source in seeds.items():
        raw_distance = distances(measured, raw_source)
        slide_distance = distances(slides, source)
        if raw_source in unseen:
            sector_sizes.append(len(raw_distance))
            unseen.difference_update(raw_distance)
        for pair, raw_target in seeds.items():
            count = slide_distance.get(pair)
            missing += count is None
            need(
                raw_distance.get(raw_target) == (None if count is None else 2 * count),
                "raw pair distance (including infinity) differs from twice the slide distance",
            )
    need(not unseen, "raw sector lacks an independent-pair preparation")
    return tuple(sorted(sector_sizes)), missing


@dataclass(frozen=True)
class CarrierResult:
    carrier_vertices: int
    singleton_raw_states: int
    singleton_raw_edges: int
    singleton_event_histogram: tuple[tuple[int, int], ...]
    ordered_singleton_and_arrival_comparisons: int
    independent_pairs: int
    pair_raw_states: int
    pair_raw_edges: int
    pair_sector_raw_sizes: tuple[int, ...]
    ordered_pair_comparisons: int
    unreachable_ordered_pair_comparisons: int
    checked_fundamental_cycles: int
    relabelled_raw_states: int
    preparation_added_marks: int
    enabled_background_centers: int


def analyze_carrier(base: Incidence) -> CarrierResult:
    raw, rungs = lift(base)
    n = len(base.neighbors)
    background = sum(rungs)
    starts = tuple(raw.prepare(background, (v,)) for v in range(n))
    pairs = {
        (x, y): raw.prepare(background, (x, y))
        for x, y in combinations(range(n), 2)
        if y not in base.neighbors[x]
    }
    enabled = len(raw.offers(background))
    need(enabled == 0, "matching background should be stationary")
    added = starts[0].bit_count() - background.bit_count()
    need(
        all(s.bit_count() - background.bit_count() == added == 2 for s in starts),
        "wrong singleton preparation budget",
    )
    need(
        all(s.bit_count() - background.bit_count() == 4 for s in pairs.values()),
        "wrong independent pair preparation budget",
    )
    single_rows = raw_orbits(raw, starts[:1])
    pair_rows = raw_orbits(raw, pairs.values())
    need(single_rows.keys().isdisjoint(pair_rows), "singleton and pair sectors mixed")
    cycles = compare_forest_oracle(base, raw, rungs, {1: single_rows, 2: pair_rows})
    histogram = singleton_comparisons(base, single_rows, starts, rungs)
    sizes, missing = pair_comparisons(base, pair_rows, pairs)
    relabelled = check_relabel(raw, single_rows | pair_rows, n)
    return CarrierResult(
        n,
        len(single_rows),
        sum(map(len, single_rows.values())) // 2,
        histogram,
        n**2,
        len(pairs),
        len(pair_rows),
        sum(map(len, pair_rows.values())) // 2,
        sizes,
        len(pairs) ** 2,
        missing,
        cycles,
        relabelled,
        added,
        enabled,
    )


def matching_words(raw: Incidence, available: int) -> Iterator[int]:
    if not available:
        yield 0
        return
    x = next(indices(available))
    for y in sorted(raw.neighbors[x]):
        if available >> y & 1:
            for rest in matching_words(raw, available ^ (1 << x) ^ (1 << y)):
                yield raw.edge_bits[edge(x, y)] | rest


def matching_two_step(raw: Incidence, matching: int) -> tuple[int, int, int]:
    # In a connected graph the XOR-cut of two vertex sets agrees only when
    # the sets coincide or are complements. Here there are more than four
    # vertices, so the only net two-center toggle for x -> y is {x, y}.
    # Initially x has three marks; y can go first exactly over a nonmatching
    # edge xy, after which x has two marks and can complete the transfer.
    prepared = tuple(raw.prepare(matching, (x,)) for x in range(len(raw.stars)))
    need(not raw.offers(matching), "a perfect matching is not stationary")
    comparisons = 0
    for x, state in enumerate(prepared):
        one = set(raw.offers(state).values())
        two = {end for first in one for end in raw.offers(first).values()}
        for y, target in enumerate(prepared):
            if x == y:
                continue
            e = raw.edge_bits.get(edge(x, y), 0)
            need(
                target not in one and (target in two) == bool(e and not matching & e),
                "two-event singleton adjacency is not G minus its perfect matching",
            )
            comparisons += 1
    orbit = raw_orbits(raw, prepared[:1])
    return len(orbit), sum(s in orbit for s in prepared), comparisons


@dataclass(frozen=True)
class MatchingControl:
    all_matchings: int
    vertical_matching_root_component: tuple[int, int]
    root_component_histogram: tuple[tuple[int, int, int], ...]
    ordered_two_event_comparisons: int
    additional_4regular_graph_matchings: tuple[tuple[str, int, int], ...]


def matching_control(k4: Incidence) -> MatchingControl:
    raw, rungs = lift(k4)
    rows = {
        mask: matching_two_step(raw, mask)
        for mask in matching_words(raw, (1 << len(raw.stars)) - 1)
    }
    vertical = rows[sum(rungs)][:2]
    histogram = Counter(row[:2] for row in rows.values())
    need(
        histogram[vertical] == 1,
        "vertical matching is not unique by this rooted census",
    )

    other_graphs = {
        "k44": Incidence.from_edges(8, product(range(4), range(4, 8)), 4),
        "octahedron": Incidence.from_edges(
            6, ((x, y) for x, y in combinations(range(6), 2) if y != x + 3), 4
        ),
    }
    extra = []
    for name, graph in other_graphs.items():
        checked = tuple(
            matching_two_step(graph, mask)[2]
            for mask in matching_words(graph, (1 << len(graph.stars)) - 1)
        )
        extra.append((name, len(checked), sum(checked)))
    return MatchingControl(
        len(rows),
        vertical,
        tuple((n, k, count) for (n, k), count in sorted(histogram.items())),
        sum(row[2] for row in rows.values()),
        tuple(extra),
    )


@dataclass(frozen=True)
class SignalMetricReport:
    scope: str
    preparation: str
    singleton_readout: str
    pair_readout: str
    loop_readout: str
    carriers: dict[str, CarrierResult]
    same_graph_matching_control: MatchingControl


def facilitated_signal_metric() -> SignalMetricReport:
    fixtures = carriers()
    return SignalMetricReport(
        "Supplied cubic incidence, rungs and external preparation give a conditional event-count metric, not emergent dimension, a physical space, or an observer clock.",
        "Stationary rung matching; external first-side root star flip adds two marks. Nonadjacent pair preparation adds four. Events preserve the prepared mark count.",
        "Shortest singleton-to-singleton count = twice carrier graph distance; first absent target rung count = carrier graph distance (zero for the input root).",
        "An independent-pair start has two induced forest components throughout. On the six fixtures, exact raw distance is twice the nonadjacent token-slide distance, including disconnected pairs.",
        "Every reached raw word has unchanged mod-2 parity on a fundamental cycle basis, hence on all closed walks.",
        {name: analyze_carrier(base) for name, base in fixtures.items()},
        matching_control(fixtures["k4"]),
    )


if __name__ == "__main__":
    print(
        json.dumps(
            asdict(facilitated_signal_metric()), sort_keys=True, separators=(",", ":")
        )
    )
