"""Exhaustive finite probe of four-site records from reversible pair offers.

The opportunity graph and, for the main rule, a distinguished zero are supplied.
Initially there are no dynamic bonds. At each tick one unordered opportunity
pair is offered uniformly; a refused offer leaves the state unchanged. The bits
and dynamic bonds, not an externally designated quartet, evolve. A bridge is a
reversible local record of current flips, not an irreversible readout or a
claim of intrinsic spacetime geometry.

On a complete opportunity graph the count with k constituent dimers and q
bridges is C(n0,k) C(n1,k) k! times k!/((k-2q)! 2**q q!); a shortest arrival
uses k+q accepted offers. The literal traversal below tests those predictions,
not a state generator that assumes them. On sparse opportunities a fresh
0–1–1–0 path predicts a record: bind the two outside pairs, then bridge the
middle pair. Conversely the record's three dynamic bonds must be opportunities
and pointwise bit XOR nonisolated reconstructs that fresh path.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from enum import Enum
from fractions import Fraction
from itertools import combinations, pairwise
from math import comb, factorial
from typing import TypedDict

Pair = tuple[int, int]
Word = tuple[Pair, ...]
State = tuple[int, int]  # site bits and dynamic-edge bits, respectively
Quartet = tuple[int, int, int, int]  # ordered along the dynamic path
Record = tuple[Pair, Quartet]


class Rule(Enum):
    ZERO_ONLY = "zero_only"
    SAME_SIGN = "naive_same_sign"
    GUARDED_SAME_SIGN = "guarded_same_sign"


def _pairs(size: int) -> Word:
    return tuple(combinations(range(size), 2))


def fresh(word: str) -> State:
    if any(bit not in "01" for bit in word):
        raise ValueError("fresh word must be binary")
    return sum(1 << i for i, bit in enumerate(word) if bit == "1"), 0


class Graph:
    def __init__(self, size: int, opportunities: Word) -> None:
        self.size = size
        self.edges: Word = tuple(
            sorted({(min(a, b), max(a, b)) for a, b in opportunities})
        )
        self._indices = {pair: i for i, pair in enumerate(self.edges)}
        incident = [0] * size
        neighbors = [0] * size
        for i, (a, b) in enumerate(self.edges):
            if not 0 <= a < b < size:
                raise ValueError(f"invalid opportunity: {(a, b)} for {size} sites")
            incident[a] |= 1 << i
            incident[b] |= 1 << i
            neighbors[a] |= 1 << b
            neighbors[b] |= 1 << a
        self._incident = tuple(incident)
        self._neighbors = tuple(neighbors)

    @classmethod
    def complete(cls, size: int) -> Graph:
        return cls(size, _pairs(size))

    def degrees(self, bonds: int) -> tuple[int, ...]:
        return tuple((mask & bonds).bit_count() for mask in self._incident)

    def _other_neighbor(self, site: int, single_bond: int) -> int:
        a, b = self.edges[single_bond.bit_length() - 1]
        return b if a == site else a

    def _loose_ends(
        self, a: int, b: int, external_bonds: int, degrees: tuple[int, ...]
    ) -> Pair | None:
        # The candidate endpoints each have exactly one remaining neighbor.
        u = self._other_neighbor(a, self._incident[a] & external_bonds)
        v = self._other_neighbor(b, self._incident[b] & external_bonds)
        return (u, v) if degrees[u] == degrees[v] == 1 else None

    def _move(
        self, before: State, degrees: tuple[int, ...], i: int, rule: Rule
    ) -> State:
        bits, bonds = before
        a, b = self.edges[i]
        da, db = degrees[a], degrees[b]
        left, right = (bits >> a) & 1, (bits >> b) & 1
        edge = 1 << i
        adjacent = bool(bonds & edge)
        if left != right:
            if (not adjacent and da == db == 0) or (adjacent and da == db == 1):
                # Single dimer bind/unbind: swap both unlike bits.
                return bits ^ ((1 << a) | (1 << b)), bonds ^ edge
        elif (
            (left == 0 or rule is not Rule.ZERO_ONLY)
            and ((not adjacent and da == db == 1) or (adjacent and da == db == 2))
            and (
                rule is not Rule.GUARDED_SAME_SIGN
                or self._loose_ends(a, b, bonds & ~edge, degrees) is not None
            )
        ):
            # Bridge/unbridge: leave the bits alone. The guarded variant uses
            # the same outside-neighbor test with the central bond excluded.
            return bits, bonds ^ edge
        return before

    def offer(self, before: State, pair: Pair, rule: Rule = Rule.ZERO_ONLY) -> State:
        a, b = pair
        i = self._indices.get((min(a, b), max(a, b)))
        if i is None:
            return before
        return self._move(before, self.degrees(before[1]), i, rule)

    def records(self, state: State, rule: Rule = Rule.ZERO_ONLY) -> tuple[Record, ...]:
        bits, bonds = state
        degrees = self.degrees(bonds)
        found: list[Record] = []
        for i, (a, b) in enumerate(self.edges):
            edge = 1 << i
            if not (bonds & edge and degrees[a] == degrees[b] == 2):
                continue
            left, right = (bits >> a) & 1, (bits >> b) & 1
            if left != right or (left == 1 and rule is Rule.ZERO_ONLY):
                continue
            loose = self._loose_ends(a, b, bonds ^ edge, degrees)
            if loose is not None:
                u, v = loose
                if (bits >> u) & 1 != left and (bits >> v) & 1 != right:
                    found.append(((a, b), (u, a, b, v)))
        return tuple(found)

    def has_fresh_path(self, bits: int) -> bool:
        """Find a simple 0–1–1–0 path; other opportunity chords are allowed."""
        for a, b in self.edges:
            if not (bits & (1 << a) and bits & (1 << b)):
                continue
            left_zeros = self._neighbors[a] & ~bits
            right_zeros = self._neighbors[b] & ~bits
            if (
                left_zeros
                and right_zeros
                and (left_zeros | right_zeros).bit_count() >= 2
            ):
                return True
        return False


def replay(
    graph: Graph, start: State, word: Word, rule: Rule = Rule.ZERO_ONLY
) -> tuple[State, ...]:
    trace = [start]
    for pair in word:
        trace.append(graph.offer(trace[-1], pair, rule))
    return tuple(trace)


def pair_fair_word(graph: Graph) -> Word:
    return tuple(pair for pair in graph.edges for _ in range(2))


def reachable(
    graph: Graph, start: State, rule: Rule = Rule.ZERO_ONLY
) -> dict[State, tuple[int, int]]:
    """Breadth-first discovery using actual offers, returning depth and path count."""
    found = {start: (0, 1)}
    queue = deque([start])
    while queue:
        before = queue.popleft()
        depth, words = found[before]
        next_depth = depth + 1
        degrees = graph.degrees(before[1])
        for i in range(len(graph.edges)):
            after = graph._move(before, degrees, i, rule)
            prior = found.get(after)
            if prior is None:
                found[after] = next_depth, words
                queue.append(after)
            elif prior[0] == next_depth:
                found[after] = next_depth, prior[1] + words
    return found


def _shape_counts(
    graph: Graph, start: State, state: State, records: tuple[Record, ...]
) -> Pair:
    bits, bonds = state
    degrees = graph.degrees(bonds)
    flipped = bits ^ start[0]
    occupied = sum(1 << i for i, degree in enumerate(degrees) if degree)
    if flipped != occupied:
        raise ArithmeticError(f"bit XOR nonisolated invariant fails: {state}, {start}")
    bridge_mask = 0
    quartet_sites = 0
    for pair, quartet in records:
        sites = sum(1 << i for i in set(quartet))
        if sites.bit_count() != 4 or sites & quartet_sites or sites & ~flipped:
            raise ArithmeticError(
                f"record does not certify a disjoint flipped quartet: {state}"
            )
        quartet_sites |= sites
        bridge_mask |= 1 << graph._indices[pair]
    constituents = bonds ^ bridge_mask
    if any(degree > 1 for degree in graph.degrees(constituents)) or any(
        constituents & (1 << i) and ((bits >> a) ^ (bits >> b)) & 1 == 0
        for i, (a, b) in enumerate(graph.edges)
    ):
        raise ArithmeticError(
            f"not a union of unlike dimers and certified paths: {state}"
        )
    return constituents.bit_count(), len(records)


def _complete_formula(n0: int, n1: int, rule: Rule) -> dict[Pair, int]:
    # Pick k zero sites, k one sites, a perfect matching, and q unordered
    # pairs of constituent dimers. A symmetric bridge has two sign choices.
    signs = 1 if rule is Rule.ZERO_ONLY else 2
    return {
        (k, q): comb(n0, k)
        * comb(n1, k)
        * factorial(k)
        * (factorial(k) // (factorial(k - 2 * q) * 2**q * factorial(q)))
        * signs**q
        for k in range(min(n0, n1) + 1)
        for q in range(k // 2 + 1)
    }


class Bucket(TypedDict):
    constituent_dimers: int
    bridges: int
    shortest_depth: int
    states: int


class BalancedCensus(TypedDict):
    sites: int
    reachable_states: int
    states_with_record: int
    states_with_two_records: int
    minimum_offers_to_record: int
    shortest_ordered_offer_words: int
    exact_probability_at_minimum_iid_uniform_offers: str
    shape_depth_and_multiplicities_checked_states: int
    shape_buckets: list[Bucket]
    pair_fair_word: Word
    pair_fair_returns_fresh_without_record: bool


def balanced_census(size: int, rule: Rule) -> BalancedCensus:
    half = size // 2
    if size < 4 or size % 2 or rule is Rule.SAME_SIGN:
        raise ValueError(
            "balanced shape census requires even size >= 4 and a shape rule"
        )
    graph = Graph.complete(size)
    start = fresh("0" * half + "1" * half)
    found = reachable(graph, start, rule)
    shapes: Counter[Pair] = Counter()
    positive_depths: Counter[int] = Counter()
    for state, (depth, words) in found.items():
        records = graph.records(state, rule)
        k, q = _shape_counts(graph, start, state, records)
        if depth != k + q:
            raise ArithmeticError(f"wrong shortest depth for {(k, q)}: {depth}")
        shapes[k, q] += 1
        if q:
            positive_depths[depth] += words
    if shapes != _complete_formula(half, half, rule):
        raise ArithmeticError(
            f"literal counts disagree with complete-graph formula: {shapes}"
        )
    minimum = min(positive_depths)
    fair = pair_fair_word(graph)
    fair_trace = replay(graph, start, fair, rule)
    if fair_trace[-1] != start or any(
        graph.records(state, rule) for state in fair_trace
    ):
        raise ArithmeticError(f"pair-fair countercontrol failed: {size}, {rule}")
    return {
        "sites": size,
        "reachable_states": len(found),
        "states_with_record": sum(n for (_, q), n in shapes.items() if q > 0),
        "states_with_two_records": sum(n for (_, q), n in shapes.items() if q == 2),
        "minimum_offers_to_record": minimum,
        "shortest_ordered_offer_words": positive_depths[minimum],
        "exact_probability_at_minimum_iid_uniform_offers": str(
            Fraction(positive_depths[minimum], len(graph.edges) ** minimum)
        ),
        "shape_depth_and_multiplicities_checked_states": sum(shapes.values()),
        "shape_buckets": [
            {
                "constituent_dimers": k,
                "bridges": q,
                "shortest_depth": k + q,
                "states": n,
            }
            for (k, q), n in sorted(shapes.items())
        ],
        "pair_fair_word": fair,
        "pair_fair_returns_fresh_without_record": True,
    }


class OpportunityCensus(TypedDict):
    sites: int
    graph_word_pairs: int
    admitting_pairs: int


def opportunity_census(size: int) -> OpportunityCensus:
    pairs = _pairs(size)
    graphs = 1 << len(pairs)
    words = 1 << size
    admitting = 0
    for mask in range(graphs):
        graph = Graph(
            size, tuple(pair for i, pair in enumerate(pairs) if mask & (1 << i))
        )
        for bits in range(words):
            actual = any(graph.records(s) for s in reachable(graph, (bits, 0)))
            predicts = graph.has_fresh_path(bits)
            if actual != predicts:
                raise ArithmeticError(
                    f"opportunity path criterion fails: {graph.edges}, {bits}"
                )
            admitting += actual
    return {
        "sites": size,
        "graph_word_pairs": graphs * words,
        "admitting_pairs": admitting,
    }


class SymmetricControl(TypedDict):
    opportunities: Word
    fresh_word: str
    offers: Word
    naive_final_degrees: tuple[int, ...]
    naive_all_offers_change_state: bool
    guard_refuses_final_offer: bool


def symmetric_controls() -> dict[str, SymmetricControl]:
    cases = (
        (
            "cycle_four",
            "0110",
            ((0, 1), (1, 2), (2, 3), (0, 3)),
            ((0, 1), (2, 3), (1, 2), (0, 3)),
        ),
        (
            "path_six",
            "011001",
            ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5)),
            ((0, 1), (2, 3), (4, 5), (1, 2), (3, 4)),
        ),
    )
    result: dict[str, SymmetricControl] = {}
    for name, bits, edges, offers in cases:
        graph = Graph(len(bits), edges)
        naive = replay(graph, fresh(bits), offers, Rule.SAME_SIGN)
        guarded = replay(graph, fresh(bits), offers, Rule.GUARDED_SAME_SIGN)
        changed = all(before != after for before, after in pairwise(naive))
        refused = guarded[:-1] == naive[:-1] and guarded[-1] == guarded[-2]
        if not changed or not refused:
            raise ArithmeticError(f"symmetric countercontrol failed: {name}")
        result[name] = {
            "opportunities": graph.edges,
            "fresh_word": bits,
            "offers": offers,
            "naive_final_degrees": graph.degrees(naive[-1][1]),
            "naive_all_offers_change_state": changed,
            "guard_refuses_final_offer": refused,
        }
    return result


def report() -> dict[str, object]:
    graph = Graph.complete(6)
    start = fresh("011001")
    word = ((0, 1), (2, 3), (4, 5), (1, 2))
    states = replay(graph, start, word)
    recorded = states[-1]
    erased = graph.offer(recorded, word[-1])
    records = graph.records(recorded)
    if len(records) != 1 or erased != states[-2] or graph.records(erased):
        raise ArithmeticError("reversible central record example failed")
    return {
        "scope": {
            "finite_executable_probe": True,
            "opportunity_graph_supplied": True,
            "positive_asymmetry_supplied": True,
            "intrinsic_spacetime": False,
            "irreversible_event": False,
            "fundamental_quartet": False,
            "record_certifies_no_other_flips": False,
        },
        "complete_opportunity_graphs_zero_only": [
            balanced_census(n, Rule.ZERO_ONLY) for n in (4, 6, 8)
        ],
        "complete_opportunity_graphs_guarded_same_sign": [
            balanced_census(n, Rule.GUARDED_SAME_SIGN) for n in (4, 6, 8)
        ],
        "opportunity_graphs": [opportunity_census(n) for n in (4, 5)],
        "naive_symmetric_counterexamples": symmetric_controls(),
        "local_but_erasable_record": {
            "fresh_word": "011001",
            "offers": word,
            "records_at_hit": records,
            "all_flipped_sites_at_hit": [
                i for i in range(graph.size) if (recorded[0] ^ start[0]) & (1 << i)
            ],
            "repeat_central_offer_restores_prior_state": erased == states[-2],
            "records_after_repeat": graph.records(erased),
        },
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, sort_keys=True))
