"""Replay three-mark tracks and offered two-seam preparations on fixed graphs.

Only asynchronous choices of a single center are considered. Vertices in a
cycle square are construction labels, not recovered spatial coordinates.

Run: python3 -m scripts.probe_three_mark_tracks
"""

from __future__ import annotations

import json
import sys
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_anonymous_shell_rules as shell
from scripts.probe_neighbor_twins_flux import (
    K5,
    OCTAHEDRON,
    Edge,
    Incidence,
    Offers,
    components,
    mask_of,
)

CYCLE_SIZES = (7, 8, 9, 10, 12, 16)
PAIR_SIZES = (14, 16, 20)
BULK_RULES = (16, 80, 208)
BOUND_RULES = (66, 130)
PAIR_RULES = BULK_RULES + BOUND_RULES


def edge(a: int, b: int) -> Edge:
    return min(a, b), max(a, b)


def cycle_square(n: int) -> Incidence:
    if n < 5:
        raise ValueError("cycle square needs at least five vertices")
    return Incidence.build(
        n, tuple(edge(i, (i + d) % n) for i in range(n) for d in (1, 2))
    )


def fixtures() -> dict[str, Incidence]:
    return {
        "K5": K5,
        "octahedron": OCTAHEDRON,
        "K4,4": Incidence.build(
            8, tuple((a, b) for a in range(4) for b in range(4, 8))
        ),
        "3x3-rook": Incidence.build(
            9,
            tuple(
                (a, b)
                for a, b in combinations(range(9), 2)
                if a // 3 == b // 3 or a % 3 == b % 3
            ),
        ),
        **{f"C{n}^2": cycle_square(n) for n in CYCLE_SIZES},
    }


def weight_states(graph: Incidence, weight: int) -> tuple[int, ...]:
    return tuple(
        mask_of(ports) for ports in combinations(range(len(graph.edges)), weight)
    )


def raw_row(graph: Incidence, state: int, rule: int) -> dict[int, int]:
    """Lift local_image back to incidence edges; do not assume target closure."""
    row = {}
    for center, star in enumerate(graph.stars):
        before = mask_of(tuple(j for j, port in enumerate(star) if state & (1 << port)))
        if before.bit_count() != 2:
            continue
        after = shell.local_image(rule, graph.scores(state, center), before)
        if before != after:
            delta = mask_of(
                tuple(
                    port for j, port in enumerate(star) if (before ^ after) & (1 << j)
                )
            )
            row[center] = state ^ delta
    return row


def chord_offers(graph: Incidence, states: tuple[int, ...]) -> Offers:
    """Predict flag 16 from occupied paths, without shell scores or local_image.

    At a two-mark center b, the single remaining edge must raise one marked
    port's score and one unmarked port's score. Thus the occupied shape is
    a-b-c-d and b-d must be a chord. The other unmarked neighbor x is unique
    by four-regularity; the new occupied path is x-b-d-c.
    """
    index = {ends: j for j, ends in enumerate(graph.edges)}
    neighbors = [
        {sum(graph.edges[j]) - v for j in star} for v, star in enumerate(graph.stars)
    ]
    offers: Offers = {}
    for state in states:
        if state.bit_count() != 3 or state >> len(graph.edges):
            raise ValueError("expected three occupied incidence edges")
        marked: dict[int, set[int]] = {}
        for a, b in graph.occupied_edges(state):
            marked.setdefault(a, set()).add(b)
            marked.setdefault(b, set()).add(a)
        row: dict[int, int] = {}
        if sorted(map(len, marked.values())) == [1, 1, 2, 2]:
            for b, ports in marked.items():
                if len(ports) != 2:
                    continue
                c = next(v for v in ports if len(marked[v]) == 2)
                a = next(iter(ports - {c}))
                d = next(iter(marked[c] - {b}))
                if d in neighbors[b]:
                    x = next(iter(neighbors[b] - {a, c, d}))
                    row[b] = mask_of(
                        tuple(
                            index[ends] for ends in (edge(x, b), edge(b, d), edge(d, c))
                        )
                    )
        offers[state] = row
    return offers


def check_chord_offers(graph: Incidence, observed: Offers) -> None:
    prediction = chord_offers(graph, weight_states(graph, 3))
    if prediction != observed:
        state = next(
            s
            for s in prediction.keys() | observed.keys()
            if prediction.get(s) != observed.get(s)
        )
        raise ValueError(f"flag-16 path/chord mismatch at state {state}")


@dataclass(frozen=True)
class WeightThreeCensus:
    states: int
    directed_offers: int
    max_degree: int
    isolates: int
    walks: dict[int, int]
    cycles: dict[int, int]
    edge_disjoint_triangles: bool


def weight_three_census(graph: Incidence) -> WeightThreeCensus:
    states = weight_states(graph, 3)
    observed = {state: raw_row(graph, state, 16) for state in states}
    check_chord_offers(graph, observed)
    if any(
        observed.get(target, {}).get(center) != state
        for state, row in observed.items()
        for center, target in row.items()
    ):
        raise ValueError("weight-three raw transition is not involutive")
    degrees = {state: len(row) for state, row in observed.items()}
    max_degree = max(degrees.values())
    if max_degree > 2:
        raise ValueError("weight-three track branches")
    walks: Counter[int] = Counter()
    cycles: Counter[int] = Counter()
    isolates = 0
    for group in components(observed):
        if len(group) == 1:
            isolates += 1
        elif all(degrees[state] == 2 for state in group):
            cycles[len(group)] += 1
        else:
            walks[len(group)] += 1
    triangle_edges = [
        j
        for mask in graph.triangle_masks
        for j in range(len(graph.edges))
        if mask & (1 << j)
    ]
    edge_disjoint = len(set(triangle_edges)) == len(triangle_edges)
    if edge_disjoint and max_degree > 1:
        raise ValueError("two flag-16 centers would require edge-sharing triangles")
    return WeightThreeCensus(
        len(states),
        sum(degrees.values()),
        max_degree,
        isolates,
        dict(walks),
        dict(cycles),
        edge_disjoint,
    )


@dataclass(frozen=True)
class SeamTrack:
    graph: Incidence
    seams: tuple[int, ...]


def seam_track(n: int) -> SeamTrack:
    graph = cycle_square(n)
    index = {ends: j for j, ends in enumerate(graph.edges)}

    def at(a: int, b: int) -> int:
        return index[edge(a % n, b % n)]

    return SeamTrack(
        graph,
        tuple(
            mask_of((at(i, i + 2), at(i + 1, i + 2), at(i + 1, i + 3)))
            for i in range(n)
        ),
    )


def cut_mask(graph: Incidence, vertices: set[int]) -> int:
    return mask_of(
        tuple(
            j
            for j, (a, b) in enumerate(graph.edges)
            if (a in vertices) != (b in vertices)
        )
    )


def fundamental_circuits(graph: Incidence) -> tuple[int, ...]:
    """One binary circuit per non-tree edge, in incidence edge order."""
    root_paths = {0: 0}
    tree = set()
    todo = deque([0])
    while todo:
        v = todo.popleft()
        for j in graph.stars[v]:
            w = sum(graph.edges[j]) - v
            if w not in root_paths:
                root_paths[w] = root_paths[v] ^ (1 << j)
                tree.add(j)
                todo.append(w)
    if len(root_paths) != len(graph.stars):
        raise ValueError("fundamental circuits require a connected graph")
    return tuple(
        root_paths[a] ^ root_paths[b] ^ (1 << j)
        for j, (a, b) in enumerate(graph.edges)
        if j not in tree
    )


def circuit_signature(state: int, circuits: tuple[int, ...]) -> int:
    return mask_of(
        tuple(j for j, loop in enumerate(circuits) if (state & loop).bit_count() % 2)
    )


def transport_row(
    graph: Incidence, row: dict[int, int], sign: int, offset: int
) -> dict[int, int]:
    """Transform center and occupied edges by v -> sign*v + offset (mod n)."""
    n = len(graph.stars)
    index = {ends: j for j, ends in enumerate(graph.edges)}

    def at(v: int) -> int:
        return (sign * v + offset) % n

    return {
        at(center): mask_of(
            tuple(index[edge(at(a), at(b))] for a, b in graph.occupied_edges(target))
        )
        for center, target in row.items()
    }


def check_seam_row(
    track: SeamTrack, i: int, rule: int, observed: dict[int, int]
) -> None:
    n = len(track.seams)
    expected = (
        {
            (i + 1) % n: track.seams[(i - 1) % n],
            (i + 2) % n: track.seams[(i + 1) % n],
        }
        if rule & 16
        else {}
    )
    if observed != expected:
        raise ValueError(f"single-seam mismatch on C{n}^2 at {i=}, {rule=}")


@dataclass(frozen=True)
class SeamCensus:
    n: int
    moving_rules: tuple[int, ...]
    frozen_rules: tuple[int, ...]
    triangle_parity: int
    winding_parity: int
    circuit_rank: int
    circuit_signature: int


def seam_census(track: SeamTrack) -> SeamCensus:
    graph, seams = track.graph, track.seams
    n = len(seams)
    basis = fundamental_circuits(graph)
    winding = mask_of(tuple(graph.edges.index(edge(v, (v + 1) % n)) for v in range(n)))
    signature = circuit_signature(seams[0], basis)
    if n < 7 or len(set(seams)) != n or len(graph.triangles) != n:
        raise ValueError("single-seam census requires the distinct n>=7 track")
    moving_rules: list[int] = []
    frozen_rules: list[int] = []
    for rule in range(256):
        for i, state in enumerate(seams):
            row = raw_row(graph, state, rule)
            check_seam_row(track, i, rule, row)
            if transport_row(graph, row, -1, 2 * i + 3) != row:
                raise ValueError("seam reflection must swap the two choices")
        (moving_rules if rule & 16 else frozen_rules).append(rule)
    for i, state in enumerate(seams):
        if (
            state.bit_count() != 3
            or graph.triangle_parities(state) != 0
            or (state & winding).bit_count() % 2 != 1
            or circuit_signature(state, basis) != signature
            or state ^ seams[(i + 1) % n] != cut_mask(graph, {(i + 2) % n})
        ):
            raise ValueError(f"single-seam parity/star mismatch on C{n}^2 at {i=}")
    return SeamCensus(
        n, tuple(moving_rules), tuple(frozen_rules), 0, 1, len(basis), signature
    )


def separation(i: int, j: int, n: int) -> int:
    return min((j - i) % n, (i - j) % n)


def check_pair_row(
    track: SeamTrack, i: int, j: int, rule: int, observed: dict[int, int]
) -> None:
    seams = track.seams
    n = len(seams)
    if rule not in PAIR_RULES or i == j:
        raise ValueError("expected an offered pair and a panel rule")
    gap = separation(i, j, n)
    expected = {}
    for a, b in ((i, j), (j, i)):
        for step, center in ((-1, a + 1), (1, a + 2)):
            shifted = (a + step) % n
            next_gap = separation(shifted, b, n)
            allowed = (
                min(gap, next_gap) >= 4
                if rule in BULK_RULES
                else {gap, next_gap} == {3, 4}
            )
            if allowed:
                expected[center % n] = seams[shifted] ^ seams[b]
    if observed != expected:
        raise ValueError(f"pair-seam mismatch on C{n}^2 at {i=}, {j=}, {rule=}")


@dataclass(frozen=True)
class PairExample:
    gap: int
    state: int
    weight: int
    cut_vertices: tuple[int, ...]
    complete_circuit_signature: int
    offers: dict[int, dict[int, int]]


@dataclass(frozen=True)
class PairPanel:
    n: int
    pairs: int
    rule_degrees: dict[int, dict[int, int]]
    nontrivial_component_sizes: dict[int, tuple[int, ...]]
    examples: tuple[PairExample, ...]


def pair_panel(track: SeamTrack) -> PairPanel:
    graph, seams = track.graph, track.seams
    n = len(seams)
    if n < 14:
        raise ValueError("two-seam panel requires n>=14")
    positions = {(i, j): seams[i] ^ seams[j] for i, j in combinations(range(n), 2)}
    if len(set(positions.values())) != len(positions) or 0 in positions.values():
        raise ValueError("pair states must be distinct and non-vacuum")
    basis = fundamental_circuits(graph)
    rows: dict[int, Offers] = {rule: {} for rule in PAIR_RULES}
    degrees: dict[int, dict[int, int]] = {rule: {} for rule in PAIR_RULES}
    for (i, j), state in positions.items():
        cut_vertices = {(v % n) for v in range(i + 2, j + 2)}
        gap = separation(i, j, n)
        if (
            state != cut_mask(graph, cut_vertices)
            or circuit_signature(state, basis) != 0
            or state.bit_count() != (4 if gap == 1 else 6)
        ):
            raise ValueError(f"pair cut or weight mismatch on C{n}^2 at {i=}, {j=}")
        for rule in PAIR_RULES:
            row = raw_row(graph, state, rule)
            check_pair_row(track, i, j, rule, row)
            rows[rule][state] = row
            if degrees[rule].setdefault(gap, len(row)) != len(row):
                raise ValueError("pair degree differs among equal separations")

    sizes = {}
    for rule, offers in rows.items():
        if raw_row(graph, 0, rule):
            raise ValueError("pair vacuum has an offer")
        if rule in BOUND_RULES and any(raw_row(graph, state, rule) for state in seams):
            raise ValueError("bound rule also moves an isolated seam")
        for (i, j), state in positions.items():
            row = offers[state]
            for sign, offset in ((1, 1), (-1, 0)):
                # Reflection reverses all three edges of S_i, sending its
                # index i to offset-i-3 (not to the image of vertex i).
                seam_offset = offset - (3 if sign == -1 else 0)
                moved = (
                    seams[(sign * i + seam_offset) % n]
                    ^ seams[(sign * j + seam_offset) % n]
                )
                if transport_row(graph, row, sign, offset) != offers[moved]:
                    raise ValueError("pair translation/reflection mismatch")
            if any(
                offers.get(target, {}).get(center) != state
                for center, target in row.items()
            ):
                raise ValueError("pair sector is not closed and involutive")
        sizes[rule] = tuple(
            sorted(len(group) for group in components(offers) if len(group) > 1)
        )
        if rule in BOUND_RULES and sizes[rule] != (2 * n,):
            raise ValueError("expected a single bound cycle with 2n states")

    examples = tuple(
        PairExample(
            gap,
            state,
            state.bit_count(),
            tuple(range(2, gap + 2)),
            circuit_signature(state, basis),
            {rule: rows[rule][state] for rule in PAIR_RULES},
        )
        for gap in range(1, n // 2 + 1)
        for state in (positions[0, gap],)
    )
    return PairPanel(n, len(positions), degrees, sizes, examples)


def report() -> dict[str, object]:
    single = [seam_census(seam_track(n)) for n in CYCLE_SIZES]
    pair = [pair_panel(seam_track(n)) for n in PAIR_SIZES]
    return {
        "schema": "idt-three-mark-tracks/1",
        "scope": "finite fixed-incidence raw replay and geometric characterizations; no physical claim",
        "choice": "each arrow is an offered asynchronous center choice, not a scheduler or direction",
        "cycle_labels": "construction labels only; no derived space, detector, or wave dynamics",
        "weight_three_geometric_rule": "a-b-c-d fires at b iff b-d is an edge, yielding x-b-d-c; likewise at c by reversal",
        "weight_three": {
            name: asdict(weight_three_census(graph))
            for name, graph in fixtures().items()
        },
        "single_seam_definition": "S_i={(i,i+2),(i+1,i+2),(i+1,i+3)} modulo n",
        "single_seam_rules": {
            "moving": single[0].moving_rules,
            "frozen": single[0].frozen_rules,
        },
        "single_seam": [
            {
                key: value
                for key, value in asdict(row).items()
                if key not in {"moving_rules", "frozen_rules"}
            }
            for row in single
        ],
        "single_seam_small_triangle_controls": {
            n: track.graph.odd_triangles(track.seams[0])
            for n in (5, 6)
            for track in (seam_track(n),)
        },
        "loop_readout": "binary circuit parities cannot localize a seam: adjacent positions differ by a vertex star",
        "pair_preparation": "externally offered S_i XOR S_j, equal to the incidence cut of {i+2,...,j+1} modulo n",
        "pair_vacuum_control": {
            "state": 0,
            "weight": 0,
            "complete_circuit_signature": 0,
            "offers": {},
        },
        "pair_bulk_rules": BULK_RULES,
        "pair_bound_rules": BOUND_RULES,
        "pair_panels": [asdict(row) for row in pair],
        "pair_example_state_bits": {n: cycle_square(n).edges for n in PAIR_SIZES},
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
