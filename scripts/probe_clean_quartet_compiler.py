"""Finite clean-bond compiler for a four-site complement-at-weight-two gate.

The opportunity graph, pair offers, and a clean serial schedule are supplied.
The K4 compiler neither selects a quartet nor keeps arbitrary interleaved
exterior offers from changing its output. Sparse clean reachability is not a
fixed word or a stepwise equivalence of raw and clean dynamics.

Run: python3 -m scripts.probe_clean_quartet_compiler
"""

from __future__ import annotations

import json
import sys
from collections import deque
from dataclasses import asdict, dataclass
from itertools import pairwise, permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_relational_quartet_records import (
    Graph,
    Pair,
    Quartet,
    Rule,
    State,
    Word,
    fresh,
)

_K4 = (0, 1, 2, 3)
_WORD: Word = (
    (0, 1),
    (0, 2),
    (0, 3),
    (2, 3),
    (1, 3),
    (0, 3),
    (0, 1),
    (0, 2),
    (2, 3),
    (1, 3),
    (0, 3),
    (0, 1),
    (1, 3),
    (0, 2),
    (2, 3),
)
_PATH: Word = ((0, 1), (1, 2), (2, 3))
# Bind both arms, bridge, swap along both arms, unbridge, unbind both arms.
_PATH_WORD: Word = ((0, 1), (2, 3), (1, 2), (0, 1), (2, 3), (1, 2), (0, 1), (2, 3))


def compiled_offers(quartet: Quartet = _K4) -> Word:
    """The fixed word on four distinct ports; caller supplies its opportunities."""
    if len(quartet) != 4 or len(set(quartet)) != 4:
        raise ValueError("the compiler requires four distinct ports")
    return tuple(
        (min(quartet[a], quartet[b]), max(quartet[a], quartet[b])) for a, b in _WORD
    )


def _offer_at(
    graph: Graph, before: State, degrees: tuple[int, ...], i: int, rule: Rule
) -> State:
    bits, bonds = before
    a, b = graph.edges[i]
    da, db = degrees[a], degrees[b]
    if (
        bonds & (1 << i)
        and ((bits >> a) ^ (bits >> b)) & 1
        and ((da, db) == (1, 2) or (da, db) == (2, 1))
    ):
        return bits ^ ((1 << a) | (1 << b)), bonds
    return graph._move(before, degrees, i, rule)


def raw_offer(
    graph: Graph, before: State, pair: Pair, rule: Rule = Rule.GUARDED_SAME_SIGN
) -> State:
    """Prior bridge/dimer rule plus a bit-only swap on a bonded unlike 1–2 arm."""
    a, b = pair
    i = graph._indices.get((min(a, b), max(a, b)))
    if i is None:
        return before
    return _offer_at(graph, before, graph.degrees(before[1]), i, rule)


def replay(
    graph: Graph, start: State, word: Word, rule: Rule = Rule.GUARDED_SAME_SIGN
) -> tuple[State, ...]:
    trace = [start]
    for pair in word:
        trace.append(raw_offer(graph, trace[-1], pair, rule))
    return tuple(trace)


def _row(graph: Graph, before: State) -> tuple[State, ...]:
    degrees = graph.degrees(before[1])
    return tuple(
        _offer_at(graph, before, degrees, i, Rule.GUARDED_SAME_SIGN)
        for i in range(len(graph.edges))
    )


def _raw_distances(graph: Graph, start: State) -> dict[State, int]:
    found = {start: 0}
    queue = deque([start])
    while queue:
        before = queue.popleft()
        for i, after in enumerate(_row(graph, before)):
            if before != after and raw_offer(graph, after, graph.edges[i]) != before:
                raise ArithmeticError(
                    f"non-involutory pair offer: {before=}, {after=}, {i=}"
                )
            if after not in found:
                found[after] = found[before] + 1
                queue.append(after)
    return found


def clean_distances(graph: Graph, bits: int) -> dict[int, int]:
    """Distance in raw offers from one clean input to every reachable clean end."""
    return {
        end_bits: distance
        for (end_bits, bonds), distance in _raw_distances(graph, (bits, 0)).items()
        if bonds == 0
    }


def _target(bits: int) -> int:
    return bits ^ 15 if bits.bit_count() == 2 else bits


def _show_bits(bits: int, size: int) -> str:
    return "".join(str((bits >> i) & 1) for i in range(size))


@dataclass(frozen=True)
class TruthTable:
    correct_inputs: int
    clean_outputs: int
    effective_offers_by_weight: tuple[tuple[int, ...], ...]
    wrong_inputs: tuple[str, ...]


def truth_table(rule: Rule) -> TruthTable:
    graph = Graph.complete(4)
    costs: list[set[int]] = [set() for _ in range(5)]
    wrong = []
    clean = 0
    for bits in range(16):
        trace = replay(graph, (bits, 0), compiled_offers(), rule)
        if trace[-1] != (_target(bits), 0):
            wrong.append(_show_bits(bits, 4))
        clean += trace[-1][1] == 0
        costs[bits.bit_count()].add(sum(a != b for a, b in pairwise(trace)))
    return TruthTable(
        16 - len(wrong), clean, tuple(tuple(sorted(x)) for x in costs), tuple(wrong)
    )


_ProductState = tuple[int, ...]
_ProductMoves = tuple[tuple[tuple[int, ...], ...], ...]


def _product_moves(
    graph: Graph, starts: tuple[State, ...], goals: tuple[State, ...]
) -> tuple[_ProductMoves, _ProductState, _ProductState]:
    """Dense local transition tables ordered by letter, then input, then state."""
    tables = []
    start_ids = []
    goal_ids = []
    for start, goal in zip(starts, goals, strict=True):
        states = sorted(
            _raw_distances(graph, start).keys() | _raw_distances(graph, goal).keys()
        )
        ids = {state: i for i, state in enumerate(states)}
        rows = [tuple(ids[after] for after in _row(graph, state)) for state in states]
        tables.append(tuple(tuple(col) for col in zip(*rows, strict=True)))
        start_ids.append(ids[start])
        goal_ids.append(ids[goal])
    return (
        tuple(tuple(col) for col in zip(*tables, strict=True)),
        tuple(start_ids),
        tuple(goal_ids),
    )


def _product_ball(
    moves: _ProductMoves, origin: _ProductState, depth: int | None
) -> tuple[set[_ProductState], tuple[int, ...]]:
    seen = {origin}
    frontier = {origin}
    sizes = [1]
    while frontier and (depth is None or len(sizes) <= depth):
        following = set()
        for row in frontier:
            for per_input in moves:
                after = tuple(table[i] for table, i in zip(per_input, row, strict=True))
                if after not in seen:
                    following.add(after)
        seen.update(following)
        frontier = following
        sizes.append(len(frontier))
    return seen, tuple(sizes)


@dataclass(frozen=True)
class ShortestCompiler:
    minimum_offers: int
    representative_inputs: tuple[int, ...]
    forward_layers: tuple[int, ...]
    backward_layers: tuple[int, ...]
    depth_7_overlap: int


def shortest_compiler_certificate() -> ShortestCompiler:
    """Use depth-7 balls to exclude lengths 0–14 and replay the 15-offer upper bound."""
    graph = Graph.complete(4)
    # Inputs 0 and 15 are fixed by every offer. One representative per other
    # global complement pair suffices (a full-table witness is checked below).
    reps = tuple(range(1, 8))
    moves, start, goal = _product_moves(
        graph, tuple((b, 0) for b in reps), tuple((_target(b), 0) for b in reps)
    )
    left, left_layers = _product_ball(moves, start, 7)
    right, right_layers = _product_ball(moves, goal, 7)
    overlap = len(left & right)
    # Every letter is its own inverse, so a word of length at most 14
    # would have a midpoint in both balls. Subset disjointness alone suffices
    # for a lower bound on the all-input gate, even without complement symmetry.
    if (
        overlap
        or len(compiled_offers()) != 15
        or truth_table(Rule.GUARDED_SAME_SIGN).correct_inputs != 16
    ):
        raise ArithmeticError("failed to certify exactly 15 serial offers")
    return ShortestCompiler(15, reps, left_layers, right_layers, overlap)


@dataclass(frozen=True)
class BarePath:
    single_input_minimum: int
    single_input_word: Word
    changing_input: str
    fixed_input: str
    common_word_exists: bool
    product_reachable_states: int
    parity_pair: Pair
    parities_to_changed: tuple[int, ...]
    parities_to_fixed: tuple[int, ...]


def _end_parities(
    graph: Graph, start: State, goal: State, counted: Pair
) -> tuple[int, ...]:
    """Track every offered occurrence, including refused offers."""
    seen = {(start, 0)}
    queue = deque(seen)
    while queue:
        state, parity = queue.popleft()
        for pair in graph.edges:
            step = (raw_offer(graph, state, pair), parity ^ (pair == counted))
            if step not in seen:
                seen.add(step)
                queue.append(step)
    return tuple(p for p in (0, 1) if (goal, p) in seen)


def bare_path_control() -> BarePath:
    graph = Graph(4, _PATH)
    changing, fixed = "0110", "1000"
    start = (fresh(changing), fresh(fixed))
    goal = (fresh("1001"), start[1])
    moves, source, target = _product_moves(graph, start, goal)
    reached, _ = _product_ball(moves, source, None)
    minimum = clean_distances(graph, start[0][0])[goal[0][0]]
    counted = (0, 1)
    return BarePath(
        minimum,
        _PATH_WORD,
        changing,
        fixed,
        target in reached,
        len(reached),
        counted,
        _end_parities(graph, start[0], goal[0], counted),
        _end_parities(graph, start[1], goal[1], counted),
    )


def _path_masks(graph: Graph) -> tuple[tuple[int, int], ...]:
    edges = set(graph.edges)
    return tuple(
        sorted(
            {
                ((1 << a) | (1 << b) | (1 << c) | (1 << d), (1 << b) | (1 << c))
                for a, b, c, d in permutations(range(graph.size), 4)
                if a < d
                and all(
                    (min(u, v), max(u, v)) in edges for u, v in ((a, b), (b, c), (c, d))
                )
            }
        )
    )


def _macro_component(start: int, masks: tuple[tuple[int, int], ...]) -> set[int]:
    seen = {start}
    queue = deque([start])
    while queue:
        bits = queue.popleft()
        for sites, middle in masks:
            after = bits ^ sites
            if (bits & sites) in (middle, sites ^ middle) and after not in seen:
                seen.add(after)
                queue.append(after)
    return seen


@dataclass(frozen=True)
class OpportunityCensus:
    sites: int
    graphs: int
    graph_inputs: int
    raw_states: int
    nontrivial_graph_inputs: int


def opportunity_census(size: int) -> OpportunityCensus:
    """Exact raw-clean vs simple-path macro closure over all labelled graphs of size <=5."""
    if not 0 <= size <= 5:
        raise ValueError("the exhaustive opportunity census supports 0 through 5 sites")
    all_edges = Graph.complete(size).edges
    graphs = 1 << len(all_edges)
    raw_states = nontrivial = 0
    for present in product((False, True), repeat=len(all_edges)):
        graph = Graph(
            size, tuple(e for e, yes in zip(all_edges, present, strict=True) if yes)
        )
        masks = _path_masks(graph)
        unchecked = set(range(1 << size))
        while unchecked:
            bits = unchecked.pop()
            raw = _raw_distances(graph, (bits, 0))
            clean = {b for b, bonds in raw if bonds == 0}
            macro = _macro_component(bits, masks)
            if clean != macro:
                raise ArithmeticError(
                    f"closure mismatch: {size=}, {graph.edges=}, {bits=}, {clean=}, {macro=}"
                )
            # Pair involutions make the raw component the same from each member;
            # the macro flips are also involutions. One traversal checks all.
            unchecked.difference_update(clean)
            raw_states += len(raw)
            if len(clean) > 1:
                nontrivial += len(clean)
    return OpportunityCensus(size, graphs, graphs * (1 << size), raw_states, nontrivial)


@dataclass(frozen=True)
class Disturbance:
    input_bits: str
    injected_pair: Pair
    interrupt_after_offers: int
    both_injections_effective: bool
    undisturbed_output: str
    disturbed_output: str
    disturbed_final_bonds: int
    exterior_restored: bool


def disturbance_control() -> Disturbance:
    graph = Graph.complete(5)
    initial = "01100"
    pair = (1, 4)
    start = fresh(initial)
    word = compiled_offers()
    split = 12
    undisturbed = replay(graph, start, word)[-1]
    trace = replay(graph, start, (pair,) + word[:split] + (pair,) + word[split:])
    bits, bonds = trace[-1]
    changed = trace[0] != trace[1] and trace[split + 1] != trace[split + 2]
    return Disturbance(
        initial,
        pair,
        split,
        changed,
        _show_bits(undisturbed[0], 5),
        _show_bits(bits, 5),
        bonds,
        not (bits ^ start[0]) & (1 << 4) and bonds == 0,
    )


def report() -> dict[str, object]:
    clique = Graph.complete(4)
    reach = {
        _show_bits(b, 4): {
            _show_bits(end, 4): d for end, d in clean_distances(clique, b).items()
        }
        for b in range(16)
    }
    return {
        "scope": {
            "finite_probe": True,
            "supplied_ports_opportunities_and_schedule": True,
            "arbitrary_interleaving_supported": False,
            "strong_bisimulation_checked": False,
            "geometry_or_physical_claim": False,
        },
        "compiled_offers": compiled_offers(),
        "truth_tables": {rule.value: asdict(truth_table(rule)) for rule in Rule},
        "single_input_clique_clean_distances": reach,
        "shortest_serial_offers": asdict(shortest_compiler_certificate()),
        "bare_path_control": asdict(bare_path_control()),
        "opportunity_census": [asdict(opportunity_census(n)) for n in range(6)],
        "disturbance": asdict(disturbance_control()),
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
