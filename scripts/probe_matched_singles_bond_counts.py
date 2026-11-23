"""Exact matched-singles, two-short-edge detector on the supplied C16² bond gait.

One trial uniformly rotates the whole preparation, runs t elementary steps,
then counts occupied edges in the fixed adjacent bin R=(S0,S1). There is
no conditioning on packet readings. The stochastic clock is supplied: choose
uniformly among distinct enabled Moves, or idle if none. This is a finite
classical occupancy comparison, not a spin, exchange-statistics, Born or
laboratory correlation prediction. Initial correlations are prepared.

Run: python3 -m scripts.probe_matched_singles_bond_counts
"""

from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from math import comb

if __package__:
    from .probe_conserved_bond_gait import Ports, cycle_square, link, need, offers
    from .probe_two_packet_matchings import isolated_table, readings
else:
    from probe_conserved_bond_gait import Ports, cycle_square, link, need, offers
    from probe_two_packet_matchings import isolated_table, readings


N = 16


def preparations():
    def edge(i, step):
        return link(i % N, (i + step) % N)

    return {name: frozenset((edge(0, 1), edge(short, 1), edge(-3, 2), edge(tail, 2)))
            for name, short, tail in (("near", 1, 3), ("far", 8, 5))}


def advance(ports, distribution):
    """Push exact mass along the raw event kernel, counting Moves, not readings."""
    result = Counter()
    for state, mass in distribution.items():
        events = offers(ports, state)
        if not events:
            result[state] += mass
            continue
        share = mass / len(events)
        for event in events:
            result[event.apply(state)] += share
    return result


def detector_row(ports, table, distribution):
    """Read the fixed detector over all rotations of each raw state.

    In the two-short sector there is one double-hit rotation iff the shorts
    share a vertex. Each short hits exactly twice in the N rotations, so the
    number of single-hit rotations is 4 - 2*double. The matching count is
    invariant under rotation and only stratifies the already-weighted hits.
    """
    joint = Counter()
    for state, mass in distribution.items():
        short = state & ports.short_links
        long = state - short
        need(len(short) == len(long) == 2 and long <= ports.motifs.keys(),
             "left the two-short/two-long shell")
        k = len(readings(table, short, long))
        a, b = short
        double = int(bool(a & b))
        single = 4 - 2 * double
        for c, multiplicity in enumerate((N - single - double, single, double)):
            joint[c, k] += mass * Fraction(multiplicity, N)
    matrix = tuple(tuple(joint[c, k] for k in range(3)) for c in range(3))
    counts = tuple(map(sum, matrix))
    mean = counts[1] + 2 * counts[2]
    need(sum(counts) == 1 and mean == Fraction(1, 4), "detector normalization or singles drift")
    return {"p_count_and_matching": matrix, "p_count": counts, "mean_count": mean,
            "g_bin": 2 * counts[2] / mean**2,
            "p_matching": tuple(map(sum, zip(*matrix))),
            "p_adjacent_and_matching": tuple(N * q for q in matrix[2])}


def histories():
    # The raw kernel commutes with rotations: rotating just before measurement
    # is equivalent to the uniform lab-frame rotation at preparation.
    ports = Ports.from_graph(cycle_square(N))
    table = isolated_table(ports)
    result = {}
    for name, start in preparations().items():
        dist = {start: Fraction(1)}
        rows = []
        for t in range(11):
            rows.append({"t": t, **detector_row(ports, table, dist)})
            if t < 10:
                dist = advance(ports, dist)
        result[name] = rows
    return result


def references():
    """Benchmarks, not transition kernels or physical fits."""
    p_bin = Fraction(2, N)
    mean = 2 * p_bin
    return {
        "two_uniform_distinct_short_edges": 2 * Fraction(1, comb(N, 2)) / mean**2,
        # In this null two draws may land on the same edge; count both draws.
        "two_iid_draws_with_replacement_counting_multiplicity": 2 * p_bin**2 / mean**2,
        "poisson_count_fluctuating_total": 1,
    }


def main():
    print(json.dumps({
        "scope": "supplied C16², rotation mixture and uniform enabled-event law; not a quantum fit",
        "detector": "N_R = occupied short edges in (S0,S1); g_bin = E[N_R(N_R-1)]/E[N_R]^2",
        "axes": "p_count_and_matching[count=0,1,2][full active matchings=0,1,2]; joint, not conditional",
        "each_boolean_edge_factorial": 0,
        "each_short_or_long_single": str(Fraction(2, N)),
        "reference_g_bin": references(),
        "unconditioned_histories": histories(),
    }, default=str, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
