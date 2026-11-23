"""Finite addressed quartet gates using only links in one undirected graph.

The carrier has no loops, vertex marks, or spatial coordinates. The vertex
indices, the data/work layout, and the word of pair offers are supplied for
the probe; none is a rule for endogenous selection. Reachability counts test
each balanced input separately, not whether one word works on all inputs.

Run: python3 -m scripts.probe_loopless_link_quartet
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass
from itertools import combinations, permutations

Edge = tuple[int, int]
Word = tuple[int, ...]
Permutation = tuple[int, ...]


class LooplessGraph:
    """Graph masks have one bit per lexicographic unordered vertex pair."""

    def __init__(self, size: int) -> None:
        if size < 1:
            raise ValueError("at least one vertex is required")
        self.size = size
        self.edges = tuple(combinations(range(size), 2))
        self.edge_index = {edge: index for index, edge in enumerate(self.edges)}
        self.state_count = 1 << len(self.edges)
        self._incident = tuple(
            sum(1 << index for index, edge in enumerate(self.edges) if vertex in edge)
            for vertex in range(size)
        )

    def _expand(self, state: int, vertices: int) -> int:
        """Include each vertex at distance at most one from the current set."""
        reached = vertices
        while state:
            bit = state & -state
            state ^= bit
            a, b = self.edges[bit.bit_length() - 1]
            endpoints = (1 << a) | (1 << b)
            if vertices & endpoints:
                reached |= endpoints
        return reached

    def has_bypass(self, state: int, edge: int, radius: int) -> bool:
        """An existing path of bounded length after excluding the offer edge."""
        a, b = self.edges[edge]
        reached = 1 << a
        other = state & ~(1 << edge)
        for _ in range(radius):
            expanded = self._expand(other, reached)
            if expanded & (1 << b):
                return True
            if expanded == reached:
                return False
            reached = expanded
        return False

    def offer(self, state: int, edge: int, code: int, radius: int | None = None) -> int:
        """Toggle the offered edge on enabled outside-degree parity rows.

        Code bits 1, 2, and 4 enable the (0,0), (1,1), and mixed rows. Both the
        parity and optional bypass tests ignore the edge being offered.
        """
        if not 0 <= code <= 7:
            raise ValueError("local table code must be in 0..7")
        a, b = self.edges[edge]
        bit = 1 << edge
        other = state & ~bit
        p = (other & self._incident[a]).bit_count() & 1
        q = (other & self._incident[b]).bit_count() & 1
        row = 4 if p != q else 2 if p else 1
        return (
            state ^ bit
            if code & row and (radius is None or self.has_bypass(other, edge, radius))
            else state
        )

    def trace(
        self, state: int, word: Word, code: int, radius: int | None = None
    ) -> Iterable[int]:
        """Yield the initial mask and the mask after each offer (including idle)."""
        yield state
        for edge in word:
            state = self.offer(state, edge, code, radius)
            yield state

    def replay(
        self, state: int, word: Word, code: int, radius: int | None = None
    ) -> int:
        for edge in word:
            state = self.offer(state, edge, code, radius)
        return state

    def compile_word(
        self, word: Word, code: int, radius: int | None = None
    ) -> Permutation:
        return tuple(
            self.replay(state, word, code, radius) for state in range(self.state_count)
        )

    def components(self, state: int) -> tuple[int, ...]:
        left = (1 << self.size) - 1
        parts: list[int] = []
        while left:
            reached = left & -left
            while (expanded := self._expand(state, reached)) != reached:
                reached = expanded
            parts.append(reached)
            left &= ~reached
        return tuple(parts)

    def relabel(self, state: int, vertex_map: tuple[int, ...]) -> int:
        if tuple(sorted(vertex_map)) != tuple(range(self.size)):
            raise ValueError("vertex map must be a permutation")
        mapped = 0
        for index, (a, b) in enumerate(self.edges):
            if state >> index & 1:
                u, v = vertex_map[a], vertex_map[b]
                mapped |= 1 << self.edge_index[(min(u, v), max(u, v))]
        return mapped

    def odd_count(self, state: int) -> int:
        return sum((state & mask).bit_count() & 1 for mask in self._incident)


@dataclass(frozen=True)
class CleanLayout:
    data_edges: tuple[int, ...]
    work_state: int

    @property
    def data_mask(self) -> int:
        return sum(1 << edge for edge in self.data_edges)

    def encode(self, data: int) -> int:
        return self.work_state | sum(
            ((data >> slot) & 1) << edge for slot, edge in enumerate(self.data_edges)
        )


def quartet_target(data: int) -> int:
    """Complement at weight two; fix the other ten four-bit inputs."""
    return data ^ 15 if data.bit_count() == 2 else data


_DATA = (0, 1, 2, 3)
_BALANCED = tuple(data for data in range(16) if data.bit_count() == 2)


@dataclass(frozen=True)
class GateWitness:
    code: int
    radius: int | None
    layout: CleanLayout
    word: Word

    def permutation(self, graph: LooplessGraph) -> Permutation:
        return graph.compile_word(self.word, self.code, self.radius)


def _word(digits: str) -> Word:
    return tuple(map(int, digits))


def _conjugates(base: str, repetitions: int, routes: tuple[str, ...]) -> Word:
    # Replay left to right: undo the route, apply the base, then redo the route.
    # Every single offer is an involution, also with a bypass guard.
    reduced: list[int] = []
    for route in routes:
        for edge in _word(route[::-1] + base * repetitions + route):
            if reduced and reduced[-1] == edge:
                reduced.pop()
            else:
                reduced.append(edge)
    return tuple(reduced)


BLANK_OR = GateWitness(
    6, None, CleanLayout(_DATA, 0), _word("403412431201240120124034214304")
)
BLANK_NAND = GateWitness(
    5,
    None,
    CleanLayout(_DATA, 0),
    _word("10432010403010212010212010212304010234014320132420102120102120102142310234"),
)
GUARDED_OR = GateWitness(
    6,
    3,
    CleanLayout(_DATA, 48),
    _conjugates("0101303", 4, ("210312303", "02023404", "204313514", "515304")),
)
GUARDED_NAND = GateWitness(
    5,
    2,
    CleanLayout(_DATA, 48),
    _conjugates("0104", 20, ("014253", "04253121", "01052434", "4530510")),
)


def transpositions(permutation: Permutation) -> tuple[tuple[int, int], ...]:
    """List nontrivial 2-cycles of an involution; reject other maps."""
    if sorted(permutation) != list(range(len(permutation))) or any(
        permutation[target] != start for start, target in enumerate(permutation)
    ):
        raise ValueError("expected an involutive permutation")
    return tuple(
        (start, target) for start, target in enumerate(permutation) if start < target
    )


def nontrivial_cycles(permutation: Permutation) -> tuple[tuple[int, ...], ...]:
    """Return each nontrivial cycle from its smallest state in forward order."""
    if sorted(permutation) != list(range(len(permutation))):
        raise ValueError("expected a permutation")
    seen: set[int] = set()
    cycles: list[tuple[int, ...]] = []
    for start in range(len(permutation)):
        cycle: list[int] = []
        state = start
        while state not in seen:
            cycle.append(state)
            seen.add(state)
            state = permutation[state]
        if len(cycle) > 1:
            cycles.append(tuple(cycle))
    return tuple(cycles)


def k4_layouts(graph: LooplessGraph) -> Iterable[CleanLayout]:
    if graph.size != 4:
        raise ValueError("the layout census is defined on K4")
    for data in combinations(range(6), 4):
        a, b = (edge for edge in range(6) if edge not in data)
        for work in (0, 1 << a, 1 << b, (1 << a) | (1 << b)):
            yield CleanLayout(data, work)


def _orbit_labels(graph: LooplessGraph, code: int, radius: int | None) -> list[int]:
    labels = [-1] * graph.state_count
    for start in range(graph.state_count):
        if labels[start] != -1:
            continue
        labels[start] = start
        pending = [start]
        while pending:
            state = pending.pop()
            for edge in range(len(graph.edges)):
                target = graph.offer(state, edge, code, radius)
                if labels[target] == -1:
                    labels[target] = start
                    pending.append(target)
    return labels


def target_reachability(
    graph: LooplessGraph, code: int, radius: int | None = None
) -> dict[int, int]:
    """Histogram of the number of separately reachable balanced targets/layout."""
    labels = _orbit_labels(graph, code, radius)
    return dict(
        sorted(
            Counter(
                sum(
                    labels[layout.encode(data)]
                    == labels[layout.encode(quartet_target(data))]
                    for data in _BALANCED
                )
                for layout in k4_layouts(graph)
            ).items()
        )
    )


def fixed_work_supports(graph: LooplessGraph) -> tuple[int, ...]:
    """Moved points per unguarded data offer, on each fixed-work input slice.

    The control is a Boolean polynomial of degree at most two in the other
    three data bits, so it has even support on that 3-cube. Each support point
    contributes a transposition (two moved points). Products on a fixed-work
    slice remain even, whereas the desired clean quartet is odd.
    """
    return tuple(
        sum(graph.offer(state, edge, code) != state for state in states)
        for layout in k4_layouts(graph)
        for states in (tuple(layout.encode(data) for data in range(16)),)
        for code in range(8)
        for edge in layout.data_edges
    )


@dataclass(frozen=True)
class StabilizerWitness:
    start: int
    target: int
    vertex_map: tuple[int, ...]
    moved_target: int


def equivariance_obstructions(
    graph: LooplessGraph,
) -> dict[CleanLayout, StabilizerWitness]:
    """For each obstructed layout, exhibit a stabilizer that does not fix its target."""
    result: dict[CleanLayout, StabilizerWitness] = {}
    vertex_maps = tuple(permutations(range(graph.size)))
    for layout in k4_layouts(graph):
        for data in _BALANCED:
            start = layout.encode(data)
            target = layout.encode(quartet_target(data))
            for vertex_map in vertex_maps:
                if graph.relabel(start, vertex_map) != start:
                    continue
                moved = graph.relabel(target, vertex_map)
                if moved != target:
                    result[layout] = StabilizerWitness(start, target, vertex_map, moved)
                    break
            if layout in result:
                break
    return result


def is_affine(function: tuple[int, ...]) -> bool:
    """Test a complete bit-cube map by its origin and basis values."""
    if not function or len(function) & (len(function) - 1):
        raise ValueError("expected a nonempty complete Boolean cube")
    origin = function[0]
    for state, value in enumerate(function):
        want = origin
        while state:
            bit = state & -state
            want ^= function[bit] ^ origin
            state ^= bit
        if want != value:
            return False
    return True


def affine_codes(graph: LooplessGraph) -> tuple[int, ...]:
    return tuple(
        code
        for code in range(8)
        if all(
            is_affine(
                tuple(
                    graph.offer(state, edge, code) for state in range(graph.state_count)
                )
            )
            for edge in range(len(graph.edges))
        )
    )


def vacuum_quiet_codes(graph: LooplessGraph) -> tuple[int, ...]:
    return tuple(
        code
        for code in range(8)
        if all(graph.offer(0, edge, code) == 0 for edge in range(len(graph.edges)))
    )


def _conserving_codes(
    graph: LooplessGraph, observable: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(
        code
        for code in range(8)
        if all(
            observable[state] == observable[graph.offer(state, edge, code)]
            for state in range(graph.state_count)
            for edge in range(len(graph.edges))
        )
    )


def odd_count_preserving_codes(graph: LooplessGraph) -> tuple[int, ...]:
    return _conserving_codes(
        graph, tuple(map(graph.odd_count, range(graph.state_count)))
    )


def link_plus_half_odd_preserving_codes(graph: LooplessGraph) -> tuple[int, ...]:
    return _conserving_codes(
        graph,
        tuple(
            state.bit_count() + graph.odd_count(state) // 2
            for state in range(graph.state_count)
        ),
    )


def main() -> None:
    graph = LooplessGraph(4)
    witnesses = (BLANK_OR, BLANK_NAND, GUARDED_OR, GUARDED_NAND)
    print(
        json.dumps(
            {
                "carrier": "finite undirected loopless graph; fixed addressed offer words",
                "addressed_witnesses": [
                    {
                        "code": w.code,
                        "bypass_radius": w.radius,
                        "work_state": w.layout.work_state,
                        "word_length": len(w.word),
                        "clean_inputs": sum(
                            permutation[w.layout.encode(data)]
                            == w.layout.encode(quartet_target(data))
                            for data in range(16)
                        ),
                        "full_cycles": nontrivial_cycles(permutation),
                    }
                    for w in witnesses
                    for permutation in (w.permutation(graph),)
                ],
                "reachable_balanced_targets_per_layout": [
                    {
                        "code": code,
                        "bypass_radius": radius,
                        "histogram": target_reachability(graph, code, radius),
                    }
                    for code, radius in (
                        (6, None),
                        (5, None),
                        (1, None),
                        (2, None),
                        (6, 2),
                        (6, 3),
                        (5, 2),
                    )
                ],
                "fixed_work_moved_point_supports": sorted(
                    set(fixed_work_supports(graph))
                ),
                "layouts_with_stabilizer_obstruction": len(
                    equivariance_obstructions(graph)
                ),
                "unguarded_affine_codes": affine_codes(graph),
                "unguarded_vacuum_quiet_codes": vacuum_quiet_codes(graph),
                "unguarded_odd_count_preserving_codes": odd_count_preserving_codes(
                    graph
                ),
                "unguarded_link_plus_half_odd_preserving_codes": link_plus_half_odd_preserving_codes(
                    graph
                ),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
