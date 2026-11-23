"""Time reversal of *states* and passive histories in a finite conserved-bond sector.

Run: python3 -m scripts.probe_native_temporal_reversal
The only dynamics is the existing local offer rule. The reversal map, reader,
uniform preparation and sampling by event count are analysis choices. In
particular a return is conditional on a positive initial read, whereas the
three pair correlations all come from the same unconditioned triples.
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, pairwise, product

if __package__:
    from .probe_conserved_bond_gait import (
        Graph,
        Marks,
        Ports,
        Vertex,
        cycle_square,
        link,
        need,
        offers,
    )
else:
    from probe_conserved_bond_gait import (
        Graph,
        Marks,
        Ports,
        Vertex,
        cycle_square,
        link,
        need,
        offers,
    )


@dataclass(frozen=True)
class Reading:
    midpoint: Vertex
    phase: str
    reversed_state: Marks


def decode(graph: Graph, ports: Ports, marks: Marks) -> Reading:
    """Read a two-bond motif using three short steps on each arm; no addresses."""
    if len(marks) != 2 or len(marks & ports.short_links) != 1:
        raise ValueError("expected one short and one long bond")
    (short,) = marks & ports.short_links
    (long,) = marks - {short}
    a, b = long
    (mid,) = graph[a] & graph[b]

    def walk(first):
        vertices = [mid, first]
        for _ in range(2):
            prev, here = vertices[-2:]
            (nxt,) = (
                v
                for v in graph[here]
                if v != prev and link(here, v) in ports.short_links
            )
            vertices.append(nxt)
        return dict(zip("CAB", (link(x, y) for x, y in pairwise(vertices))))

    arms = (walk(a), walk(b))
    for arm, other in (arms, arms[::-1]):
        for phase, bond in arm.items():
            if short == bond:
                reflected = other[{"A": "A", "B": "C", "C": "B"}[phase]]
                return Reading(mid, phase, frozenset((long, reflected)))
    raise ValueError("short bond is outside the active two-bond motif")


def pair_correlations(counts):
    """Read C01, C12 and C02 from a single positive (nonnegative mass) history."""
    if (
        not counts
        or any(
            len(q) != 3 or any(bit not in (-1, 1) for bit in q) or mass < 0
            for q, mass in counts.items()
        )
        or not sum(counts.values())
    ):
        raise ValueError("expected nonzero nonnegative counts of binary triples")
    return tuple(
        Fraction(
            sum(mass * q[i] * q[j] for q, mass in counts.items()), sum(counts.values())
        )
        for i, j in ((0, 1), (1, 2), (0, 2))
    )


def k_value(c):
    return c[0] + c[1] - c[2]


def return_counts(mask, paths):
    return {
        "lags": [0, 2, 4, 6],
        "conditioned_on": len(mask),
        "return_counts": [
            sum(paths[s][lag] in mask for s in mask) for lag in (0, 2, 4, 6)
        ],
    }


def audit_sector(n):
    if n < 9:
        raise ValueError("the return probe uses rings of size at least 9")
    graph = cycle_square(n)
    ports = Ports.from_graph(graph)
    transitions, centers = {}, {}
    for pair in combinations(ports.short_links | ports.motifs.keys(), 2):
        s = frozenset(pair)
        moves = offers(ports, s)
        if moves:
            (move,) = moves
            transitions[s], centers[s] = move.apply(s), move.center
    need(
        len(transitions) == 6 * n and set(transitions) == set(transitions.values()),
        "active two-bond shell is not the expected permutation",
    )
    readings = {s: decode(graph, ports, s) for s in transitions}
    reverse = {s: r.reversed_state for s, r in readings.items()}
    need(
        all(
            reverse[reverse[s]] == s and transitions[reverse[t]] == reverse[s]
            for s, t in transitions.items()
        ),
        "state reversal identity failed",
    )
    ordinary = sum(transitions[t] == s for s, t in transitions.items())
    need(ordinary == 0, "ordinary detailed balance control changed")
    same_center = sum(centers[reverse[t]] == centers[s] for s, t in transitions.items())
    need(same_center < len(transitions), "raw event-label control changed")

    paths = {}
    for s in transitions:
        p = [s]
        for _ in range(6):
            p.append(transitions[p[-1]])
        paths[s] = p
    markers = [
        {s for s, r in readings.items() if link(v, r.midpoint) in ports.motifs}
        for v in graph
    ]
    masks = [
        {s for s, r in readings.items() if r.phase in subset}
        for size in range(4)
        for subset in combinations("ABC", size)
    ]
    outer = {s for s, r in readings.items() if r.phase == "A"}
    for mask in [*markers, outer]:
        need(
            all((s in mask) == (reverse[s] in mask) for s in transitions),
            "registered return observable is not J-even",
        )
    marker_returns = return_counts(markers[0], paths)
    need(
        marker_returns["conditioned_on"] == 12
        and marker_returns["return_counts"] == [12, 4, 2, 6]
        and all(return_counts(m, paths) == marker_returns for m in markers),
        "long-neighbor conditional return changed",
    )
    outer_returns = return_counts(outer, paths)
    need(
        outer_returns["conditioned_on"] == 2 * n
        and outer_returns["return_counts"] == [2 * n, 0, 0, 2 * n],
        "marker-free outer-touch conditional return changed",
    )
    p_aa = Fraction(sum(transitions[s] in outer for s in outer), len(outer))
    not_outer = transitions.keys() - outer
    p_na = Fraction(sum(transitions[s] in outer for s in not_outer), len(not_outer))
    fit = p_aa**2 + (1 - p_aa) * p_na
    actual = Fraction(outer_returns["return_counts"][1], len(outer))
    need(
        fit != actual,
        "stationary one-step binary Markov fit now predicts the lag-two return",
    )
    memory = {
        "P_A_next_given_A": str(p_aa),
        "P_A_next_given_not_A": str(p_na),
        "one_step_fit_lag2": str(fit),
        "actual_lag2": str(actual),
    }

    words = [tuple(centers[state] for state in p[:3]) for p in paths.values()]
    missing = []
    for length in (1, 2, 3):
        support = {word[:length] for word in words}
        missing.append(sum(w[::-1] not in support for w in support))

    def midpoint_word(a, b, c):
        return link(b, c) in ports.motifs and graph[b] & graph[c] == {a}

    forward = sum(midpoint_word(*w) for w in words)
    backward = sum(midpoint_word(*w[::-1]) for w in words)
    need(
        missing == [0, 0, 4 * n] and (forward, backward) == (2 * n, 0),
        "local pivot-trace asymmetry changed",
    )
    pivot = {
        "unsupported_reversals_by_length": missing,
        "distinct_triples": len(set(words)),
        "first_is_long_midpoint": forward,
        "last_is_long_midpoint": backward,
    }

    gaps = ((1, 1), (1, 2), (2, 1), (2, 2), (3, 3))
    ks = []
    example = None
    for mask in [*markers, *masks]:
        for d, e in gaps:
            counts = Counter(
                tuple(1 if p[idx] in mask else -1 for idx in (0, d, d + e))
                for p in paths.values()
            )
            c = pair_correlations(counts)
            ks.append(k_value(c))
            need(
                -3 <= ks[-1] <= 1 and sum(counts.values()) == len(paths),
                "passive histories violate their binary joint bound",
            )
            if example is None:
                example = {
                    "reader": "first external marker",
                    "gaps": [d, e],
                    "triple_counts": {
                        "".join("+" if bit == 1 else "-" for bit in q): count
                        for q, count in sorted(counts.items())
                    },
                    "C01_C12_C02": list(map(str, c)),
                    "K": str(ks[-1]),
                }
    return {
        "n": n,
        "active_states": len(paths),
        "J_squared_and_reversing": True,
        "ordinary_reverse_edges": ordinary,
        "same_center_under_J": same_center,
        "long_neighbor_reader": marker_returns,
        "outer_touch_reader": outer_returns,
        "outer_touch_memory_control": memory,
        "pivot_traces": pivot,
        "passive_histories": {
            "readers": "all markers and all eight phase subsets",
            "clock_gaps": gaps,
            "reader_clock_cases": len(ks),
            "histories_counted": len(paths) * len(ks),
            "min_K": str(min(ks)),
            "max_K": str(max(ks)),
            "example": example,
        },
    }


def supplied_target():
    """An algebraic comparison target, not a native gait output or an experiment."""
    f = Fraction
    target = (f(1, 2), f(1, 2), f(-1, 2))
    joint_rows = sorted(
        {(a * b, b * c, a * c) for a, b, c in product((-1, 1), repeat=3)}, reverse=True
    )
    joint_min, joint_max = min(map(k_value, joint_rows)), max(map(k_value, joint_rows))
    context_max = max(map(k_value, product((-1, 1), repeat=3)))
    # Normalized signed mass with total negative part N has K <= max + (max-min)*N.
    # A mixture with unrestricted pair contexts of fraction p has K <= max + (3-max)*p.
    excess = k_value(target) - joint_max
    min_neg = excess / (joint_max - joint_min)
    min_context = excess / (context_max - joint_max)
    signed = [
        (row, f(3, 8) if k_value(row) == joint_max else -f(1, 8)) for row in joint_rows
    ]
    mixture = [
        (row, f(1, 4), "common_history")
        for row in joint_rows
        if k_value(row) == joint_max
    ]
    mixture.append(((1, 1, -1), f(1, 4), "pair_context"))

    for witness in (signed, mixture):
        need(
            sum(w[1] for w in witness) == 1
            and tuple(sum(w[0][i] * w[1] for w in witness) for i in range(3)) == target,
            "cost witness fails to reproduce supplied pair correlations",
        )
    need(
        sum(-w for _, w in signed if w < 0) == min_neg
        and sum(w for _, w, kind in mixture if kind == "pair_context") == min_context,
        "cost witness misses its lower bound",
    )
    return {
        "origin": "supplied correlations for two equal pi/3 steps; not measured or generated",
        "C01_C12_C02": list(map(str, target)),
        "K": str(k_value(target)),
        "common_history_K_range": [joint_min, joint_max],
        "arbitrary_pair_context_K_max": context_max,
        "min_negative_mass": str(min_neg),
        "min_pair_context_fraction": str(min_context),
        "signed_witness": [{"products": row, "weight": str(w)} for row, w in signed],
        "pair_context_mixture": [
            {"products": row, "weight": str(w), "kind": kind}
            for row, w, kind in mixture
        ],
    }


def report():
    return {
        "sectors": [audit_sector(n) for n in (9, 10, 13, 16, 21)],
        "supplied_comparison": supplied_target(),
        "boundary": "Active two-bond states only; no global microscopic reversal, physical "
        "clock, probabilistic postulate or QM derivation. Repeated counts use "
        "the same uniform shell, not independent experimental observations. "
        "Comparison costs concern representations of supplied pair correlations.",
    }


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
