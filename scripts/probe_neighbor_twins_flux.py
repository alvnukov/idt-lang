"""Finite control for equal local event offers and unequal triangle readouts.

Supply a simple 4-regular incidence and one bit per undirected edge. A
center action is admitted only at two marked ports. For each neighbor, count
its marked edges other than the common edge; use the equality partition of
these counts, not their names or order. T swaps both marks in every pair
class. F also swaps the two singleton ports if there are exactly two.

The center action does not change any of those neighbor-shell inputs. With
two marked ports, if there are two pair classes, either both pairs split
their marks or neither does. With one pair and two singletons, the singleton
marks split exactly when the pair's marks split. Thus the extra swap never
changes which events are non-null, and F only changes a whole star or
nothing. A cycle crosses a star evenly, so the star flip preserves its
mod-2 parity (not just the triangles counted below).

Triangles and their parity readout are supplied; triangle counts are not
particles. The model supplies incidences and conditional center actions, not
a 3D embedding, origin of an event selection, scheduler, or probabilities.
For K5, following a six-state ring without backtracking uses the previous
event as extra information; the instantaneous rule offers the reversal too.

Run: python3 -B scripts/probe_neighbor_twins_flux.py
"""

from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations, product
from json import dumps
from typing import Literal

Edge = tuple[int, int]
Triangle = tuple[int, int, int]
Rule = Literal["T", "F"]
Offers = dict[int, dict[int, int]]  # state -> center -> distinct state
RULES: tuple[Rule, Rule] = ("T", "F")


def bits_at(state: int, ports: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((state >> port) & 1 for port in ports)


def mask_of(ports: tuple[int, ...]) -> int:
    return sum(1 << port for port in ports)


def local_result(
    scores: tuple[int, ...],
    bits: tuple[int, ...],
    rule: Rule,
) -> tuple[int, ...]:
    """Return unchanged bits for ineligible or null events."""
    if sum(bits) != 2:
        return bits
    classes: dict[int, list[int]] = {}
    for port, score in enumerate(scores):
        classes.setdefault(score, []).append(port)
    result = list(bits)
    singletons = []
    for members in classes.values():
        if len(members) == 2:
            a, b = members
            result[a], result[b] = bits[b], bits[a]
        elif len(members) == 1:
            singletons.extend(members)
    if rule == "F" and len(singletons) == 2:
        a, b = singletons
        result[a], result[b] = bits[b], bits[a]
    return tuple(result)


@dataclass(frozen=True)
class Incidence:
    edges: tuple[Edge, ...]
    stars: tuple[tuple[int, ...], ...]
    shells: tuple[tuple[int, ...], ...]
    triangles: tuple[Triangle, ...]
    triangle_masks: tuple[int, ...]

    @classmethod
    def build(cls, vertex_count: int, edges: tuple[Edge, ...]) -> "Incidence":
        edges = tuple(sorted((min(a, b), max(a, b)) for a, b in edges))
        if len(edges) != len(set(edges)) or any(
            not 0 <= a < b < vertex_count for a, b in edges
        ):
            raise ValueError("a simple incidence with valid vertex indices is required")
        stars = tuple(
            tuple(i for i, edge in enumerate(edges) if v in edge)
            for v in range(vertex_count)
        )
        if not stars or any(len(star) != 4 for star in stars):
            raise ValueError("the four-port rule needs a nonempty 4-regular incidence")
        star_masks = tuple(mask_of(star) for star in stars)
        shells = tuple(
            tuple(star_masks[sum(edges[i]) - v] ^ (1 << i) for i in star)
            for v, star in enumerate(stars)
        )
        edge_indices = {edge: i for i, edge in enumerate(edges)}
        triangles = tuple(
            (a, b, c)
            for a, b, c in combinations(range(vertex_count), 3)
            if (a, b) in edge_indices
            and (a, c) in edge_indices
            and (b, c) in edge_indices
        )
        triangle_masks = tuple(
            mask_of((edge_indices[a, b], edge_indices[a, c], edge_indices[b, c]))
            for a, b, c in triangles
        )
        return cls(edges, stars, shells, triangles, triangle_masks)

    def half_filled(self) -> tuple[int, ...]:
        return tuple(
            sorted(
                mask_of(ports)
                for ports in combinations(range(len(self.edges)), len(self.edges) // 2)
            )
        )

    def scores(self, state: int, center: int) -> tuple[int, ...]:
        return tuple((state & shell).bit_count() for shell in self.shells[center])

    def event(self, state: int, center: int, rule: Rule) -> int | None:
        ports = self.stars[center]
        before = bits_at(state, ports)
        if sum(before) != 2:
            return None
        after = local_result(self.scores(state, center), before, rule)
        delta = mask_of(
            tuple(
                port for port, b, a in zip(ports, before, after, strict=True) if b != a
            )
        )
        return state ^ delta if delta else None

    def triangle_parities(self, state: int) -> int:
        return mask_of(
            tuple(
                i
                for i, triangle in enumerate(self.triangle_masks)
                if (state & triangle).bit_count() % 2
            )
        )

    def odd_triangles(self, state: int) -> tuple[Triangle, ...]:
        mask = self.triangle_parities(state)
        return tuple(
            triangle for i, triangle in enumerate(self.triangles) if mask & (1 << i)
        )

    def occupied_edges(self, state: int) -> tuple[Edge, ...]:
        return tuple(edge for i, edge in enumerate(self.edges) if state & (1 << i))


K5 = Incidence.build(5, tuple(combinations(range(5), 2)))
OCTAHEDRON = Incidence.build(
    6,
    tuple(
        edge
        for edge in combinations(range(6), 2)
        if edge not in {(0, 1), (2, 3), (4, 5)}
    ),
)


def local_control() -> dict[str, int]:
    inputs = disagreements = nonstar = irreversibilities = 0
    for scores in product(range(4), repeat=4):
        for bits in product(range(2), repeat=4):
            t_result = local_result(scores, bits, "T")
            f_result = local_result(scores, bits, "F")
            inputs += 1
            disagreements += (t_result != bits) != (f_result != bits)
            nonstar += f_result not in (bits, tuple(1 - b for b in bits))
            irreversibilities += local_result(scores, t_result, "T") != bits
            irreversibilities += local_result(scores, f_result, "F") != bits
    return {
        "score_bit_inputs": inputs,
        "enabled_disagreements": disagreements,
        "f_nonstar_events": nonstar,
        "irreversibilities": irreversibilities,
    }


def offers_for(graph: Incidence, states: tuple[int, ...], rule: Rule) -> Offers:
    return {
        state: {
            v: after
            for v in range(len(graph.stars))
            if (after := graph.event(state, v, rule)) is not None
        }
        for state in states
    }


def components(offers: Offers) -> list[set[int]]:
    """Exhaustive breadth-first components of a checked involutive event graph."""
    groups: list[set[int]] = []
    seen: set[int] = set()
    for start in offers:
        if start in seen:
            continue
        group = {start}
        queue = deque([start])
        while queue:
            for neighbor in offers[queue.popleft()].values():
                if neighbor not in group:
                    group.add(neighbor)
                    queue.append(neighbor)
        groups.append(group)
        seen.update(group)
    return groups


@dataclass(frozen=True)
class RuleReport:
    nontrivial_events: int
    triangle_changing_events: int
    triangle_change_histogram: dict[int, int]
    changed_odd_count_pairs: dict[str, int]
    component_histogram: dict[int, int]
    six_cycle_components: int
    two_odd_starts: int
    relocatable_two_odd_starts: int
    two_odd_starts_reaching_six_odd: int


def rule_report(
    graph: Incidence, offers: Offers, parities: dict[int, int]
) -> RuleReport:
    changed: Counter[int] = Counter()
    counts: Counter[str] = Counter()
    for state, moves in offers.items():
        for center, target in moves.items():
            if (
                target == state
                or target not in offers
                or offers[target].get(center) != state
            ):
                raise ValueError(
                    "an offer must be a nontrivial half-filling-preserving involution"
                )
            if graph.scores(state, center) != graph.scores(target, center):
                raise ValueError(
                    "the center action changed its own neighbor-shell inputs"
                )
            before, after = parities[state], parities[target]
            changed[(before ^ after).bit_count()] += 1
            if before != after:
                counts[f"{before.bit_count()}->{after.bit_count()}"] += 1

    six_cycles = two_odd_starts = relocatable = two_reaching_six = 0
    histogram: Counter[int] = Counter()
    for group in components(offers):
        histogram[len(group)] += 1
        six_cycles += len(group) == 6 and all(
            len(offers[state]) == len(set(offers[state].values())) == 2
            for state in group
        )
        two_odd = [
            parities[state] for state in group if parities[state].bit_count() == 2
        ]
        two_odd_starts += len(two_odd)
        if len(set(two_odd)) > 1:
            relocatable += len(two_odd)
        if any(parities[state].bit_count() == 6 for state in group):
            two_reaching_six += len(two_odd)
    nontrivial = sum(changed.values())
    return RuleReport(
        nontrivial,
        nontrivial - changed[0],
        dict(changed),
        dict(counts),
        dict(histogram),
        six_cycles,
        two_odd_starts,
        relocatable,
        two_reaching_six,
    )


def return_example(graph: Incidence, offers: Offers) -> dict[str, object]:
    """Compare taking an immediate inverse with choosing not to backtrack."""
    start = next(state for state, moves in offers.items() if len(moves) == 2)
    state = start
    previous: int | None = None
    centers: list[int] = []
    seen = {start}
    while True:
        allowed = [center for center in offers[state] if center != previous]
        if len(allowed) != (2 if previous is None else 1):
            raise ValueError("this return example needs a two-direction ring")
        previous = allowed[0]  # choose a first direction by reporting order only
        centers.append(previous)
        state = offers[state][previous]
        if state == start:
            break
        if state in seen:
            raise ValueError("the non-backtracking path did not return to its start")
        seen.add(state)
    return {
        "initial_occupied_edges": graph.occupied_edges(start),
        "backtrack_centers": (centers[0], centers[0]),
        "nonbacktracking_centers": centers,
        "direction_is_supplied_by_local_rule": False,
    }


def shortest_readout_word(
    start: int,
    target_mask: int,
    offers: Offers,
    parities: dict[int, int],
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """BFS over full states, not the coarse graph of observed parity counts."""
    paths: dict[int, tuple[tuple[int, ...], tuple[int, ...]]] = {start: ((start,), ())}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        states, centers = paths[state]
        if parities[state] == target_mask:
            return states, centers
        for center, target in offers[state].items():
            if target not in paths:
                paths[target] = ((*states, target), (*centers, center))
                queue.append(target)
    return None


def four_to_four_example(
    graph: Incidence,
    t_offers: Offers,
    f_offers: Offers,
    parities: dict[int, int],
) -> dict[str, object]:
    """An exact, report-only octahedron witness and its same-start F control."""
    initial: tuple[Edge, ...] = ((0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (2, 4))
    target: tuple[Triangle, ...] = ((0, 3, 5), (1, 2, 4), (1, 3, 4), (1, 3, 5))
    start = mask_of(tuple(graph.edges.index(edge) for edge in initial))
    target_mask = mask_of(tuple(graph.triangles.index(triangle) for triangle in target))
    t_result = shortest_readout_word(start, target_mask, t_offers, parities)
    f_result = shortest_readout_word(start, target_mask, f_offers, parities)
    if t_result is None:
        raise ValueError("the fixed T witness has no path to its target readout")
    states, centers = t_result
    f_state = start
    first_null = None
    for center in centers:
        f_target = f_offers[f_state].get(center)
        if f_target is None:
            first_null = center
            break
        f_state = f_target
    return {
        "initial_occupied_edges": initial,
        "T_shortest_centers": centers,
        "T_odd_triangles": [graph.odd_triangles(state) for state in states],
        "F_shortest_centers": f_result[1] if f_result is not None else None,
        "F_first_null_center_in_T_word": first_null,
    }


def graph_report(
    graph: Incidence, example: Literal["return", "triangle"]
) -> dict[str, object]:
    states = graph.half_filled()
    t_offers, f_offers = (offers_for(graph, states, rule) for rule in RULES)
    parities = {state: graph.triangle_parities(state) for state in states}
    report: dict[str, object] = {
        "state_count": len(states),
        "moving_states": sum(bool(moves) for moves in t_offers.values()),
        "triangle_count": len(graph.triangles),
        "enabled_disagreements": sum(
            t_offers[state].keys() != f_offers[state].keys() for state in states
        ),
        "output_disagreements": sum(
            t_offers[state] != f_offers[state] for state in states
        ),
        "T": asdict(rule_report(graph, t_offers, parities)),
        "F": asdict(rule_report(graph, f_offers, parities)),
    }
    if example == "return":
        report["return_example"] = return_example(graph, t_offers)
    else:
        report["four_to_four_example"] = four_to_four_example(
            graph, t_offers, f_offers, parities
        )
    return report


def main() -> None:
    report = {
        "scope": "supplied incidence, conditional actions and triangle readout; no event selector or physical claim",
        "local": local_control(),
        "K5": graph_report(K5, "return"),
        "octahedron": graph_report(OCTAHEDRON, "triangle"),
    }
    print(dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
