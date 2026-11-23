"""Are *all* simultaneous raw pair rates sufficient to predict the next pair rate?

Finite C16² comparison only. Each preparation is a uniformly rotated and
reflected four-bond pattern. The event kernel uses incidence alone; uniform
weight per offered Move is a supplied clock (idle if jammed). Mixed orbit
weights are not inferred from reachability. No packet IDs or material
particle statistics enter the detector. Run: python3 -m scripts.probe_hidden_pair_correlations
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product

if __package__:
    from .probe_conserved_bond_gait import (
        Ports,
        cycle_square,
        fixture,
        link,
        need,
        offers,
    )
    from .probe_two_packet_matchings import isolated_table, readings
else:
    from probe_conserved_bond_gait import (
        Ports,
        cycle_square,
        fixture,
        link,
        need,
        offers,
    )
    from probe_two_packet_matchings import isolated_table, readings


N = 16
# S_i has index i and L_i has index N+i. These coordinates define only
# preparations, symmetries and lab-frame readouts, never the event kernel.
EDGES = tuple(link(i, (i + d) % N) for d in (1, 2) for i in range(N))
INDEX = {e: i for i, e in enumerate(EDGES)}
PERMS = tuple(tuple((d-1)*N + (a + h*i - (d if h < 0 else 0)) % N
                    for d in (1, 2) for i in range(N))
              for a, h in product(range(N), (1, -1)))
PREPS = {"A": (0, 4, 17, 25), "B": (0, 4, 21, 29),
         "U": (0, 4, 16, 24), "V": (0, 4, 23, 31)}


def orbit(s):
    return {tuple(sorted(p[i] for i in s)) for p in PERMS}


def raw(s):
    return frozenset(EDGES[i] for i in s)


def indices(s):
    return tuple(sorted(INDEX[e] for e in s))


def kind(table, s):
    return len(readings(table, [EDGES[i] for i in s if i < N],
                        [EDGES[i] for i in s if i >= N]))


def inclusions(states, k):
    """Lab-frame inclusion probabilities, sparse; unlisted slots are zero."""
    counts = Counter(t for s in states for t in combinations(s, k))
    return Counter({t: Fraction(v, len(states)) for t, v in counts.items()})


def next_pair_rates(ports, states):
    result = Counter()
    for s in states:
        marks = raw(s)
        events = offers(ports, marks)
        targets = [indices(m.apply(marks)) for m in events] or [s]
        weight = Fraction(1, len(states) * len(targets))
        for t in targets:
            for pair in combinations(t, 2):
                result[pair] += weight
    return result


def differences(a, b):
    rates = [(inclusions(a, k), inclusions(b, k)) for k in (1, 2, 3)]
    return [sum(p[t] != q[t] for t in p.keys() | q.keys()) for p, q in rates]


def named_readout(ports, table, s):
    marks = raw(s)
    events = offers(ports, marks)
    separations = []
    for m in events:
        a, b = sorted(INDEX[e] for e in m.apply(marks) & ports.short_links)
        separations.append(min(b-a, N-(b-a)))
    group = orbit(s)
    rates = next_pair_rates(ports, group)
    joint = [rates[0, i] for i in (3, 5)]
    return {"orbit_size": len(group), "matchings": kind(table, s),
            "offer_count": len(events), "successor_short_separations": sorted(separations),
            "post_joint_s0_s3_s0_s5": joint, "post_g_s0_s3_s0_s5": [p * 64 for p in joint]}


def census(ports, table):
    """For a uniform orbit, each labelled pair probability is the number
    of pairs of its symmetry type in a state divided by that type's size.
    Thus the sorted six pair types are a *complete* pair-rate signature.
    No mixed distribution over different symmetry orbits is classified.
    """
    pair_type = {}
    for pair in combinations(range(2*N), 2):
        if pair not in pair_type:
            pair_group = orbit(pair)
            pair_type.update(dict.fromkeys(pair_group, min(pair_group)))
    remaining = {s + t for s, t in product(combinations(range(N), 2),
                                           combinations(range(N, 2*N), 2))}
    size = len(remaining)
    fibers = defaultdict(list)
    while remaining:
        s = next(iter(remaining))
        group = orbit(s)
        remaining.difference_update(group)
        signature = tuple(sorted(pair_type[t] for t in combinations(s, 2)))
        fibers[signature].append(min(group))
    collisions = [sorted(f) for f in fibers.values() if len(f) > 1]
    strata = Counter()
    masks = Counter()
    for j, f in enumerate(sorted(collisions)):
        need(len(f) == 2, "collision fiber is no longer binary")
        a, b = f
        ka, kb = sorted((kind(table, a), kind(table, b)))
        strata[f"{ka},{kb}"] += 1
        p, q = (next_pair_rates(ports, orbit(s)) for s in f)
        for pair in set(pair_type.values()):
            if p[pair] != q[pair]:
                masks[pair] |= 1 << j
    all_mask = (1 << len(collisions)) - 1
    sorted_types = sorted(set(pair_type.values()))
    single = [t for t in sorted_types if masks[t] == all_mask]
    two = [] if single else [(a, b) for a, b in combinations(sorted_types, 2)
                             if masks[a] | masks[b] == all_mask]
    return ({"raw_states": size, "orbits": sum(map(len, fibers.values())),
             "pair_signatures": len(fibers), "collision_matching_counts": dict(strata),
             "largest_fiber": max(map(len, fibers.values()))},
            {"labelling": "edge indices 0..15 = shorts, 16..31 = longs",
             "single_complete_panel_representatives": single,
             "example_complete_two_panel_if_needed": two[:1],
             "max_fibers_resolved_by_one": max(m.bit_count() for m in masks.values())})


def reachability(ports):
    # Exactly t legal events: a jam is not an extra event here.
    start = fixture(N, 0, 1)[0] | fixture(N, 8, 1)[0]
    targets = {k: {raw(t) for t in orbit(PREPS[k])} for k in ("A", "B")}
    states = {start}
    first = {}
    for t in range(21):
        for k, group in targets.items():
            if states & group:
                first.setdefault(k, t)
        if t < 20:
            states = {m.apply(s) for s in states for m in offers(ports, s)}
    return {"first_event": first, "members_at_20": {k: len(states & v) for k, v in targets.items()}}


def idle_mixture_control(ports):
    """Two different fair mixtures give equal pair tables at every held snapshot.

    Each component's orbit is uniform. No legal event, history of positive
    event length, or independently resampled preparation is used for a later
    snapshot of a jammed trial.
    """
    mixtures = []
    for long_pairs in (((4, 5), (6, 9)), ((4, 7), (5, 6))):
        a, b = (orbit((0, 1, N+i, N+j)) for i, j in long_pairs)
        need(len(a) == len(b) == 32 and not a & b, "uniform union is not the fair mixture")
        mixtures.append(a | b)
    x, y = mixtures
    return {"long_starts_on_common_s0_s1": [[[4, 5], [6, 9]], [[4, 7], [5, 6]]],
            "support_sizes": [len(x), len(y)], "shared_states": len(x & y),
            "states_with_any_legal_move": sum(bool(offers(ports, raw(s))) for s in x | y),
            "different_inclusion_slots": differences(x, y),
            "p_triple_s0_l3_l4": [inclusions(s, 3)[0, N+3, N+4] for s in (x, y)],
            "time": "held snapshots only; none of these states has a next legal event"}


def run():
    ports = Ports.from_graph(cycle_square(N))
    table = isolated_table(ports)
    coverage, panel = census(ports, table)
    return {
        "scope": "panel identifies uniform dihedral orbits only; mixed-orbit control; no physical statistics",
        "clock": "uniform distinct enabled raw events; single-offer U/V needs no tie-break",
        "denominator": "both singles 1/8 by dihedral invariance and two conserved shorts",
        "named": {k: named_readout(ports, table, s) for k, s in PREPS.items()},
        "initial_different_inclusion_slots": differences(orbit(PREPS["A"]), orbit(PREPS["B"])),
        "initial_triple_s0_s4_l1": {k: inclusions(orbit(PREPS[k]), 3)[0, 4, N+1]
                                     for k in ("A", "B")},
        "uv_initial_different_inclusion_slots": differences(orbit(PREPS["U"]), orbit(PREPS["V"])),
        "census": coverage, "followup_pair_panel": panel,
        "idle_mixture_control": idle_mixture_control(ports),
        "reachable_from_fixed_input": reachability(ports),
    }


if __name__ == "__main__":
    print(json.dumps(run(), default=str, indent=2))
