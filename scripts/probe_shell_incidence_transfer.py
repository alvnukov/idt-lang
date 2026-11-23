"""Transfer four fixed shell flags to two supplied, labeled incidences.

Exhaust fixed edge-weight sectors under arbitrary asynchronous center choices.
A hit is a different labeled pair of odd triangles, not autonomous motion:
the incidence, the triangle readout and the availability of center choices
are supplied. Paths may pass states with other numbers of odd triangles. No
geometry, scheduler, probabilities, or global incidence claim is inferred.

Run: python3 -m scripts.probe_shell_incidence_transfer
"""

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_anonymous_shell_rules as shell
from scripts import probe_neighbor_twins_flux as incidence
from scripts.probe_neighbor_twins_flux import Incidence, Offers, components, mask_of

RULES = (66, 130, 80, 208)
T, F = 80, 208
KERNEL_SHA256 = {
    "probe_anonymous_shell_rules.py": "ca6b46cb3ac75fe2762b5f7786c7814433fa48edd33ffb0af01941674e642843",
    "probe_neighbor_twins_flux.py": "e10b9e4967c72d98681933dca8ef6a4379514059ce43f5c9d709e948787cc01b",
}
C8_SQUARED = Incidence.build(
    8,
    tuple((a, b) for a, b in combinations(range(8), 2) if (b - a) in (1, 2, 6, 7)),
)
ROOK = Incidence.build(
    9,
    tuple(
        (a, b)
        for a, b in combinations(range(9), 2)
        if a // 3 == b // 3 or a % 3 == b % 3
    ),
)
SECTORS = (("C8^2", C8_SQUARED, 8), *(("L(K3,3)", ROOK, w) for w in (8, 9, 10)))


@dataclass(frozen=True)
class PathExample:
    centers: tuple[int, ...]
    states: tuple[int, ...]
    syndromes: tuple[int, ...]


@dataclass(frozen=True)
class BlockedExample:
    state: int
    syndrome: int
    component_size: int


@dataclass(frozen=True)
class RuleCensus:
    immediate: int
    reachable: int
    nontrivial_events: int
    triangle_changing_events: int
    immediate_example: PathExample | None
    delayed_example: PathExample | None
    blocked_example: BlockedExample | None


@dataclass(frozen=True)
class SectorCensus:
    graph: str
    weight: int
    states: int
    odd_count_histogram: dict[int, int]
    two_odd_starts: int
    triangle_edges_partition: bool
    odd_weight_excludes_two_odd: bool
    t_f_enabled_disagreements: int
    f_nonstar_events: int
    rules: dict[int, RuleCensus]


def kernel_digests() -> dict[str, str]:
    paths = (Path(shell.__file__), Path(incidence.__file__))
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _shortest_transfer(
    start: int, offers: Offers, parity: dict[int, int], two_odd: set[int]
) -> PathExample:
    """Find a path on full states, without filtering intermediate vertices."""
    via: dict[int, tuple[int, int] | None] = {start: None}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        if state in two_odd and parity[state] != parity[start]:
            states = [state]
            centers = []
            while (parent := via[state]) is not None:
                state, center = parent
                states.append(state)
                centers.append(center)
            return PathExample(
                tuple(reversed(centers)),
                tuple(reversed(states)),
                tuple(parity[s] for s in reversed(states)),
            )
        for center, target in offers[state].items():
            if target not in via:
                via[target] = state, center
                queue.append(target)
    raise ValueError("component census supplied an unreachable witness")


def _rule_census(
    offers: Offers, parity: dict[int, int], two_odd: set[int]
) -> RuleCensus:
    immediate: set[int] = set()
    first: PathExample | None = None
    nontrivial = changed = 0
    for state, row in offers.items():
        for center, target in row.items():
            nontrivial += 1
            if parity[state] != parity[target]:
                changed += 1
                if state in two_odd and target in two_odd:
                    immediate.add(state)
                    if first is None:
                        first = PathExample(
                            (center,), (state, target), (parity[state], parity[target])
                        )

    # The kernel checks every same-center inverse, hence unrestricted paths
    # reach exactly a component. Distinct two-odd masks, not just states, matter.
    reachable = 0
    delayed_start: int | None = None
    blocked: tuple[bool, int, int] | None = None
    for group in components(offers):
        starts = group & two_odd
        if len({parity[s] for s in starts}) > 1:
            reachable += len(starts)
            for state in starts - immediate:
                if delayed_start is None or state < delayed_start:
                    delayed_start = state
        else:
            for state in starts:
                key = (not offers[state], len(group), state)
                if blocked is None or key < blocked:
                    blocked = key
    if len(immediate) > reachable:
        raise ValueError("immediate starts must also be reachable")

    return RuleCensus(
        len(immediate),
        reachable,
        nontrivial,
        changed,
        first,
        _shortest_transfer(delayed_start, offers, parity, two_odd)
        if delayed_start is not None
        else None,
        BlockedExample(blocked[2], parity[blocked[2]], blocked[1]) if blocked else None,
    )


def _sector(name: str, graph: Incidence, weight: int) -> SectorCensus:
    states = tuple(
        sorted(
            mask_of(ports) for ports in combinations(range(len(graph.edges)), weight)
        )
    )
    parity = {s: graph.triangle_parities(s) for s in states}
    two_odd = {s for s, syndrome in parity.items() if syndrome.bit_count() == 2}
    histogram = dict(Counter(syndrome.bit_count() for syndrome in parity.values()))
    full = (1 << len(graph.edges)) - 1
    covered = 0
    disjoint = True
    for mask in graph.triangle_masks:
        disjoint &= not (mask & covered)
        covered |= mask
    partition = disjoint and covered == full
    if partition and any(count % 2 != weight % 2 for count in histogram):
        raise ValueError("partitioned triangle parity must equal total weight in GF(2)")

    templates = shell._templates(graph, states)
    rows = {}
    t_offers: Offers | None = None
    enabled_disagreements = f_nonstar = 0
    for flag in RULES:
        offers = shell._offers(templates, flag)
        rows[flag] = _rule_census(offers, parity, two_odd)
        if flag == T:
            t_offers = offers
        if flag == F:
            if t_offers is None:
                raise ValueError("the matched T control must be run before F")
            stars = tuple(map(mask_of, graph.stars))
            enabled_disagreements = sum(
                len(row.keys() ^ t_offers[s].keys()) for s, row in offers.items()
            )
            f_nonstar = sum(
                (s ^ target) != stars[center]
                for s, row in offers.items()
                for center, target in row.items()
            )
            if enabled_disagreements or f_nonstar or rows[F].triangle_changing_events:
                raise ValueError("matched-support full-star F control failed")
    return SectorCensus(
        name,
        weight,
        len(states),
        histogram,
        len(two_odd),
        partition,
        partition and weight % 2 == 1,
        enabled_disagreements,
        f_nonstar,
        rows,
    )


def fixed_census() -> tuple[SectorCensus, ...]:
    if kernel_digests() != KERNEL_SHA256:
        raise ValueError("frozen shell/incident event kernel SHA-256 mismatch")
    return tuple(_sector(name, graph, weight) for name, graph, weight in SECTORS)


def report() -> dict[str, object]:
    return {
        "schema": "idt-shell-incidence-transfer/1",
        "scope": "fixed labeled incidences; triangle-parity reachability, not autonomous motion",
        "path_semantics": "arbitrary asynchronous center choices; intermediate odd count unrestricted",
        "odd_weight_obstruction": "when triangles partition edges, XOR of triangle parities equals occupied edge count modulo two",
        "kernel_sha256": KERNEL_SHA256,
        "rule_order": RULES,
        "rule_labels": {66: "66", 130: "130", T: "T", F: "F"},
        "incidences": {
            name: {"edges_by_bit": graph.edges, "triangles_by_bit": graph.triangles}
            for name, graph, _ in SECTORS
        },
        "sectors": [asdict(row) for row in fixed_census()],
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
