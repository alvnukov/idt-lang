"""Check raw two-seam exchange and its confounding by supplied cycle flux.

The host C_n², XOR preparations, addresses and timed center offers are supplied.
Labels in the ordered lift are bookkeeping, not detector outputs. Phase signs
and coherent-path reference models are compared, not derived by the raw rule.

Run: python3 -m scripts.probe_seam_exchange_flux
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations, pairwise
from math import prod
from pathlib import Path
from typing import NamedTuple

from scripts import probe_anonymous_shell_rules as shell
from scripts import probe_neighbor_twins_flux as incidence
from scripts import probe_three_mark_tracks as tracks

RULE = 16
SIZES = tuple(range(12, 25))
Pair = tuple[int, int]
PairEdge = tuple[Pair, Pair]
Square = tuple[PairEdge, ...]
LocalEvent = tuple[int, tuple[int, ...], tuple[int, ...]]


class Move(NamedTuple):
    origin: int
    destination: int
    target: Pair


@dataclass(frozen=True)
class PairGraph:
    track: tracks.SeamTrack
    rows: dict[Pair, dict[int, Move]]
    raw_orbit_sha256: str


def _ordered(a: int, b: int) -> Pair:
    return (a, b) if a < b else (b, a)


def _edge(source: Pair, target: Pair) -> PairEdge:
    return (source, target) if source < target else (target, source)


def _digest(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _raw_orbit(track: tracks.SeamTrack, start: int) -> dict[int, dict[int, int]]:
    """Unfiltered BFS in raw edge bits; do not assume pair-sector closure."""
    rows: dict[int, dict[int, int]] = {}
    seen = {start}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        row = tracks.raw_row(track.graph, state, RULE)
        rows[state] = row
        for target in row.values():
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return rows


def _predict_moves(pair: Pair, n: int) -> dict[int, Move]:
    moves: dict[int, Move] = {}
    for origin, other in (pair, pair[::-1]):
        for shift, center in ((-1, origin + 1), (1, origin + 2)):
            destination = (origin + shift) % n
            if tracks.separation(destination, other, n) >= 4:
                if center % n in moves:
                    raise ValueError(f"ambiguous center for separated seam pair {pair}")
                moves[center % n] = Move(
                    origin, destination, _ordered(destination, other)
                )
    return moves


def pair_graph(n: int) -> PairGraph:
    if n < 12:
        raise ValueError("the exchange probe requires n >= 12")
    track = tracks.seam_track(n)
    seams = track.seams
    raw = _raw_orbit(track, seams[0] ^ seams[n // 2])
    positions = [
        (a, b) for a, b in combinations(range(n), 2) if tracks.separation(a, b, n) >= 4
    ]
    states = {(a, b): seams[a] ^ seams[b] for a, b in positions}
    if len(set(states.values())) != len(states) or set(raw) != set(states.values()):
        raise ValueError(
            f"raw orbit and injective separated-pair encoding disagree on C{n}^2"
        )
    decode = {state: pair for pair, state in states.items()}
    rows = {}
    for pair, state in states.items():
        observed = raw[state]
        predicted = _predict_moves(pair, n)
        if observed != {
            center: states[move.target] for center, move in predicted.items()
        }:
            raise ValueError(f"center-by-center pair move mismatch on C{n}^2 at {pair}")
        row = {}
        for center, successor in observed.items():
            target = decode[successor]
            (origin,) = set(pair) - set(target)
            (destination,) = set(target) - set(pair)
            if raw[successor].get(center) != state:
                raise ValueError(f"raw offer not reversible at {pair}, {center=}")
            row[center] = Move(origin, destination, target)
        if len({move.target for move in row.values()}) != len(row):
            raise ValueError(f"parallel offers at separated pair {pair}")
        rows[pair] = row
    return PairGraph(track, rows, _digest((track.graph.edges, raw)))


def square_boundaries(pair_graph: PairGraph) -> tuple[Square, ...]:
    """Both center orders must fire, each moving the same distinct packet."""
    rows = pair_graph.rows
    squares: set[Square] = set()
    for source, row in rows.items():
        for (center_a, a), (center_b, b) in combinations(row.items(), 2):
            if a.origin == b.origin:
                continue
            ab = rows[a.target].get(center_b)
            ba = rows[b.target].get(center_a)
            if (
                ab is None
                or ba is None
                or ab.target != ba.target
                or (ab.origin, ab.destination) != (b.origin, b.destination)
                or (ba.origin, ba.destination) != (a.origin, a.destination)
                or len({source, a.target, b.target, ab.target}) != 4
            ):
                continue
            squares.add(
                tuple(
                    sorted(
                        (
                            _edge(source, a.target),
                            _edge(source, b.target),
                            _edge(a.target, ab.target),
                            _edge(b.target, ba.target),
                        )
                    )
                )
            )
    return tuple(sorted(squares))


def _gf2_rank(columns: tuple[int, ...]) -> int:
    pivots: dict[int, int] = {}
    for column in columns:
        while column:
            bit = column.bit_length()
            if bit not in pivots:
                pivots[bit] = column
                break
            column ^= pivots[bit]
    return len(pivots)


def _boundary_ranks(
    vertices: tuple[Pair, ...], edges: tuple[PairEdge, ...], squares: tuple[Square, ...]
) -> tuple[int, int]:
    vertex_ids = {v: j for j, v in enumerate(vertices)}
    edge_ids = {edge: j for j, edge in enumerate(edges)}
    d1 = tuple((1 << vertex_ids[a]) ^ (1 << vertex_ids[b]) for a, b in edges)
    d2 = tuple(sum(1 << edge_ids[e] for e in square) for square in squares)
    for square in squares:
        boundary = 0
        for edge in square:
            boundary ^= d1[edge_ids[edge]]
        if boundary:
            raise ValueError("square has nonzero boundary-of-boundary")
    return _gf2_rank(d1), _gf2_rank(d2)


def _lift(ordered: Pair, move: Move) -> Pair:
    a, b = ordered
    if a == move.origin:
        return move.destination, b
    if b == move.origin:
        return a, move.destination
    raise ValueError("offered packet is absent in ordered lift")


def _cover_distances(pair_graph: PairGraph, start: Pair) -> dict[Pair, int]:
    dist = {start: 0}
    queue = deque([start])
    while queue:
        source = queue.popleft()
        for move in pair_graph.rows[_ordered(*source)].values():
            target = _lift(source, move)
            if target not in dist:
                dist[target] = dist[source] + 1
                queue.append(target)
    return dist


def _edge_signs(pair_graph: PairGraph) -> dict[PairEdge, int]:
    """Check sorted-lift deck sign against the seam-position cut on every arrow."""
    cut = (0, len(pair_graph.track.seams) - 1)
    signs = {}
    for source, row in pair_graph.rows.items():
        for move in row.values():
            lifted = _lift(source, move)
            if _ordered(*lifted) != move.target:
                raise ValueError(f"ordered lift does not project to {move.target}")
            deck = 1 if lifted == move.target else -1
            flux = -1 if _ordered(move.origin, move.destination) == cut else 1
            if deck != flux:
                raise ValueError(f"deck/cut discrepancy at {source}, {move}")
            signs[_edge(source, move.target)] = flux
    return signs


def local_event(
    track: tracks.SeamTrack, center: int, before: int, after: int
) -> LocalEvent:
    """Absolute center and five full before/after bit restrictions, not scores."""
    graph = track.graph
    star = sum(1 << port for port in graph.stars[center])
    supports = (star, *graph.shells[center])
    return (
        center,
        tuple(before & mask for mask in supports),
        tuple(after & mask for mask in supports),
    )


def _monotone_exchange(n: int) -> tuple[Pair, ...]:
    a, b = 0, n // 2
    path = [(a, b)]
    for _ in range(n // 2):
        a = (a + 1) % n
        path.append((a, b))
        b = (b + 1) % n
        path.append((a, b))
    if n % 2:
        path.append((a, (b + 1) % n))
    return tuple(path)


def _pair_trace(
    pair_graph: PairGraph, path: tuple[Pair, ...]
) -> tuple[LocalEvent, ...]:
    track = pair_graph.track
    states = tuple(track.seams[a] ^ track.seams[b] for a, b in path)
    events = []
    for (source, target), (before, after) in zip(
        pairwise(path), pairwise(states), strict=True
    ):
        centers = [
            center
            for center, move in pair_graph.rows[_ordered(*source)].items()
            if _lift(source, move) == target
        ]
        if len(centers) != 1:
            raise ValueError(
                f"ordered witness step not uniquely offered: {source} to {target}"
            )
        events.append(local_event(track, centers[0], before, after))
    return tuple(events)


def _single_trace(track: tracks.SeamTrack) -> tuple[LocalEvent, ...]:
    n = len(track.seams)
    events = []
    for i, before in enumerate(track.seams):
        row = tracks.raw_row(track.graph, before, RULE)
        tracks.check_seam_row(track, i, RULE, row)
        center = (i + 2) % n
        events.append(local_event(track, center, before, row[center]))
    return tuple(events)


def _loop_sign(path: tuple[Pair, ...], signs: dict[PairEdge, int]) -> int:
    return prod(signs[_edge(_ordered(*a), _ordered(*b))] for a, b in pairwise(path))


@dataclass(frozen=True)
class SizeEvidence:
    n: int
    vertices: int
    edges: int
    squares: int
    rank_d1: int
    rank_d2: int
    b0: int
    b1: int
    b2: int
    ordered_cover_vertices: int
    shortest_exchange_length: int
    deck_cut_edges_checked: int
    negative_cut_edges: int
    flat_loop_signs: tuple[int, int]
    exchange_to_single_signs: tuple[int, int]
    exchange_ordered: tuple[Pair, ...]
    exchange_centers: tuple[int, ...]
    exchange_gap_trace: tuple[int, ...]
    retraced_ordered: tuple[Pair, ...] | None
    retraced_loop_sign: int | None
    local_events_matched: int
    single_event_multiset_sha256: str
    exchange_event_multiset_sha256: str
    raw_orbit_sha256: str
    cubical_target_sha256: str


def inspect_size(n: int) -> SizeEvidence:
    graph = pair_graph(n)
    vertices = tuple(sorted(graph.rows))
    signs = _edge_signs(graph)
    edges = tuple(sorted(signs))
    squares = square_boundaries(graph)
    v, e, f = len(vertices), len(edges), len(squares)
    d1, d2 = _boundary_ranks(vertices, edges, squares)
    b0, b1, b2 = v - d1, e - d1 - d2, f - d2
    if (v, e, f) != (n * (n - 7) // 2, n * (n - 8), n * (n - 9) // 2):
        raise ValueError(f"unexpected cell count on C{n}^2: {(v, e, f)}")
    if (b0, b1, b2) != (1, 1, 0):
        raise ValueError(f"unexpected GF(2) homology on C{n}^2: {(b0, b1, b2)}")
    if any(prod(signs[edge] for edge in square) != 1 for square in squares):
        raise ValueError("the cut signs are not flat on observed squares")

    path = _monotone_exchange(n)
    distances = _cover_distances(graph, path[0])
    exchange_length = distances.get(path[0][::-1])
    pair_events = _pair_trace(graph, path)
    if exchange_length != n or len(distances) != 2 * v or len(pair_events) != n:
        raise ValueError(
            "monotone path is not a shortest exchange in the connected ordered cover"
        )
    if path[-1] != path[0][::-1]:
        raise ValueError("monotone path did not exchange the ordered packets")
    exchange_deck_sign = (
        -1
    )  # The path closed downstairs and swapped the two lift labels.
    exchange_sign = _loop_sign(path, signs)
    single_path = (*range(n), 0)
    single_sign = prod(
        -1 if _ordered(a, b) == (0, n - 1) else 1 for a, b in pairwise(single_path)
    )
    if exchange_sign != exchange_deck_sign or single_sign != -1:
        raise ValueError("exchange and one-seam lap must cross the cut oddly")
    pure_flux_ratio = (
        exchange_sign * single_sign
    )  # Both supplied cut holonomies are signs.

    single_events = _single_trace(graph.track)
    single_counts, pair_counts = Counter(single_events), Counter(pair_events)
    if single_counts != pair_counts:
        raise ValueError(f"single and exchange local-event multisets differ on C{n}^2")
    gaps = tuple(tracks.separation(*pair, n) for pair in path)
    retraced, retraced_sign = None, None
    if n % 2 == 0:
        retraced = path[:2] * (n // 2) + path[:1]
        _pair_trace(graph, retraced)
        retraced_sign = _loop_sign(retraced, signs)
        if (
            retraced_sign != 1
            or tuple(tracks.separation(*pair, n) for pair in retraced) != gaps
        ):
            raise ValueError("gap-blind exchange/retrace control failed")

    return SizeEvidence(
        n,
        v,
        e,
        f,
        d1,
        d2,
        b0,
        b1,
        b2,
        len(distances),
        exchange_length,
        len(signs),
        sum(sign == -1 for sign in signs.values()),
        (1, exchange_sign),
        (pure_flux_ratio, pure_flux_ratio * exchange_deck_sign),
        path,
        tuple(event[0] for event in pair_events),
        gaps,
        retraced,
        retraced_sign,
        sum(pair_counts.values()),
        _digest(sorted(single_counts.items())),
        _digest(sorted(pair_counts.items())),
        graph.raw_orbit_sha256,
        _digest((vertices, edges, squares)),
    )


def report(sizes: tuple[int, ...] = SIZES) -> dict[str, object]:
    root = Path(__file__).resolve().parents[1]
    sources = (
        Path(__file__),
        Path(tracks.__file__),
        Path(shell.__file__),
        Path(incidence.__file__),
    )
    return {
        "schema": "idt-seam-exchange-flux/1",
        "claim_boundary": (
            "Finite check on supplied C_n^2 hosts and preparations. Addresses, schedules, "
            "reference paths and a phase-sensitive readout are supplied, not derived. "
            "Neither a sign choice nor Pauli exclusion, quantum statistics, or physical space follows; "
            "the probe does not alter inherited theory-closure statuses."
        ),
        "source_target_compatibility": {
            "track_rule": RULE,
            "raw_source": "frozen seam_track and raw_row; unfiltered closure from (0,floor(n/2))",
            "target": "injective XOR of unordered seam pairs at cyclic distance >=4; matches every raw center and target",
            "two_cells": "distinct packets actually move in either order to the same target, with the same centers",
            "source_sha256": {
                str(path.resolve().relative_to(root)): hashlib.sha256(
                    path.read_bytes()
                ).hexdigest()
                for path in sources
            },
        },
        "cut": "seam-coordinate edge {0,n-1}; its pullback equals the sorted ordered-cover deck sign on every edge",
        "flat_loop_sign_order": ("trivial", "cut/deck"),
        "exchange_to_single_sign_order": (
            "pure common spatial flux",
            "common spatial flux plus two-sector deck sign",
        ),
        "phase_model": (
            "Assumes common nonzero local scalar phase factors keyed by absolute center and "
            "full raw before/after restrictions on the star and all four neighbor other-edge supports; "
            "the event multisets agree exactly, so their commuting factors cancel in H2/H1. "
            "With a suitable supplied phase-sensitive reference this separates pure common spatial flux "
            "(+1) from an additional two-sector deck sign (-1). If spectator- or number-dependent "
            "phases are permitted, the separation is not identified: a negative cut factor used only "
            "in the two-seam sector mimics the additional deck sign."
        ),
        "gap_only_control": "even n only: the alternating exchange and repeated first-step retrace have equal gap traces and different deck changes",
        "sizes": [asdict(inspect_size(n)) for n in sizes],
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
