"""Exact finite counterexample to third-order marginal closure on C16².

The incidence, conserved-bond offer rule, preparations and uniform choice of
enabled raw events are supplied. Coordinates only describe fixtures and
readouts. No orbit or matching is selected after the move.

Run: python3 -m scripts.probe_active_triple_witness
"""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
import json

from .probe_conserved_bond_gait import Marks, Ports, cycle_square, fixture, link, need, offers


N = 16
# Both mixtures have S0, S4 in their representatives. The pairs below give
# the starting vertices of the two long bonds.
LEFT = ((1, 13), (5, 9))
RIGHT = ((1, 5), (6, 10))


def transform(state: Marks, shift: int, direction: int = 1) -> Marks:
    return frozenset(
        frozenset((shift + direction * v) % N for v in bond) for bond in state
    )


def preparation(long_pairs):
    distribution = Counter()
    for a, b in long_pairs:
        seed = frozenset((link(0, 1), link(4, 5), link(a, (a + 2) % N), link(b, (b + 2) % N)))
        orbit = {transform(seed, i, h) for i in range(N) for h in (-1, 1)}
        need(len(orbit) == 2 * N, "fixture must have a full dihedral orbit")
        for state in orbit:
            distribution[state] += Fraction(1, len(long_pairs) * len(orbit))
    need(sum(distribution.values()) == 1, "preparation is not normalized")
    return distribution


def recurrent_component(ports, seed):
    """Find the forward closure, verifying its reverse reachability and activity."""
    seen = {seed}
    work = [seed]
    reverse = defaultdict(set)
    while work:
        state = work.pop()
        moves = offers(ports, state)
        need(bool(moves), "jam in the prepared active region")
        for move in moves:
            target = move.apply(state)
            reverse[target].add(state)
            if target not in seen:
                seen.add(target)
                work.append(target)
    backwards = {seed}
    work = [seed]
    while work:
        for state in reverse[work.pop()]:
            if state not in backwards:
                backwards.add(state)
                work.append(state)
    need(backwards == seen, "forward closure was not strongly connected")
    return seen


def certificate():
    ports = Ports.from_graph(cycle_square(N))
    bonds = ports.short_links | ports.motifs.keys()
    seed = fixture(N, 0, 1)[0] | fixture(N, 8, 1)[0]
    components = (recurrent_component(ports, seed),
                  recurrent_component(ports, transform(seed, 1)))
    component_sizes = tuple(map(len, components))
    region = components[0] | components[1]
    need(component_sizes == (2944, 2944) and len(region) == 5888,
         "prepared active region changed")

    distributions = (preparation(LEFT), preparation(RIGHT))
    moments = (Counter(), Counter())
    pair = {link(0, 1), link(3, 4)}
    outputs = []
    move_degrees = []
    for distribution, inclusions in zip(distributions, moments):
        need(distribution.keys() <= region, "support escaped the prepared recurrent components")
        probability = Fraction(0)
        degrees = Counter()
        for state, weight in distribution.items():
            need(state <= bonds and len(state) == 4 and len(state & ports.short_links) == 2,
                 "expected two raw bonds of each type")
            for size in range(1, 5):
                for subset in combinations(state, size):
                    inclusions[frozenset(subset)] += weight
            moves = offers(ports, state)
            degrees[len(moves)] += weight
            probability += weight * Fraction(sum(pair <= move.apply(state) for move in moves),
                                              len(moves))
        outputs.append(probability)
        move_degrees.append(degrees)

    checked, mismatches = [], []
    for size in range(1, 5):
        total = differing = 0
        for subset in combinations(bonds, size):
            key = frozenset(subset)
            total += 1
            differing += moments[0][key] != moments[1][key]
        checked.append(total)
        mismatches.append(differing)
    need(checked[:3] == [32, 496, 4960] and mismatches == [0, 0, 0, 128],
         "raw inclusion witness changed")
    need(outputs == [Fraction(1, 32), Fraction(1, 96)], "next-pair witness changed")
    need(all(row == {1: Fraction(1, 2), 3: Fraction(1, 2)} for row in move_degrees),
         "raw offer-count distributions changed")
    return {
        "subsets_checked": tuple(checked[:3]),
        "mismatches": tuple(mismatches[:3]),
        "fourth_order_mismatches": mismatches[3],
        "component_sizes": component_sizes,
        "active_region_size": len(region),
        "next_pair": tuple(outputs),
        "move_degrees": tuple(move_degrees),
    }


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2, default=str))
