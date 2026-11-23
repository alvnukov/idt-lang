"""Finite optional no-jam test for the anonymous rule 000 <-> 111.

Choose the offered triples, not their firing order. A raw state is jammed
when all offered triples are mixed. Excluding jams is exactly the failure
of Property B (two-colourability); it is a comparison criterion, not a
physical requirement. No space or coordinates enter the family search.

Run: python3 -m scripts.probe_unanimous_fano_clock [--json]
"""

import argparse
import json
from collections import Counter, defaultdict
from functools import reduce
from itertools import combinations, permutations
from math import comb
from operator import and_, xor

from scripts.probe_binary_unanimous_triples import offer


def covering_families(n, size):
    """All simple size-edge families covering every colouring by a uniform edge."""
    triples = tuple(sum(1 << i for i in t) for t in combinations(range(n), 3))
    # One representative of each complementary colouring pair suffices.
    states = range(1 << (n - 1))
    covers = [sum(1 << s for s in states if offer(s, t) != s) for t in triples]
    suffix = [0] * (len(triples) + 1)
    for j in reversed(range(len(triples))):
        suffix[j] = covers[j] | suffix[j + 1]

    hits = []
    path = []

    def visit(start, left, uncovered):
        if uncovered & ~suffix[start]:
            return
        if not left:
            if not uncovered:
                hits.append(tuple(path))
            return
        for j in range(start, len(triples) - left + 1):
            path.append(triples[j])
            visit(j + 1, left - 1, uncovered & ~covers[j])
            path.pop()

    visit(0, size, (1 << len(states)) - 1)
    return tuple(hits)


def syndrome(state):
    """XOR labels 1..7 are assigned only after the unrestricted search."""
    return reduce(xor, (i + 1 for i in range(7) if state >> i & 1), 0)


def shape(group, enabled):
    degrees = sorted(len(enabled[s]) for s in group)
    if degrees == [2] * 6:
        return "C6"  # graph is connected, simple and undirected
    if degrees == [1] * (len(group) - 1) + [len(group) - 1]:
        return f"K1,{len(group) - 1}"
    return "other"


def dynamics(lines):
    states = range(128)
    enabled = {s: tuple(t for t in lines if offer(s, t) != s) for s in states}
    sectors = defaultdict(set)
    for s in states:
        sectors[syndrome(s), s.bit_count() % 3].add(s)

    seen = set()
    shapes, clock_points = Counter(), Counter()
    matched = flips = complements = no_persistent = 0
    for start in states:
        if start in seen:
            continue
        group = {start}
        frontier = [start]
        while frontier:
            s = frontier.pop()
            for t in enabled[s]:
                dest = offer(s, t)
                if dest not in group:
                    group.add(dest)
                    frontier.append(dest)
        seen.update(group)
        kind = shape(group, enabled)
        shapes[kind] += 1
        tag = syndrome(start), start.bit_count() % 3
        if group == sectors[tag]:
            matched += len(group)
        # Compute point intersections from raw incidence, not from the sector.
        common = reduce(and_, (t for s in group for t in enabled[s]), 127)
        if not common:
            no_persistent += len(group)
        if kind != "C6":
            continue
        for s in group:
            point = reduce(and_, enabled[s])
            if point == common and point.bit_count() == 1 and point.bit_length() == tag[0]:
                clock_points[point.bit_length()] += 1
                flips += sum(bool((offer(s, t) ^ s) & point) for t in enabled[s])
                other = s ^ 127
                complements += int(other in group and enabled[other] == enabled[s]
                                   and (s & point) != (other & point))

    degree_matches = 0
    for s in states:
        k = s.bit_count()
        # Seven lines partition the 21 pairs. A uniform line contributes
        # three same-colour pairs, a mixed line one.
        degree_matches += 2 * len(enabled[s]) == comb(k, 2) + comb(7 - k, 2) - 7
    return (
        {"components": dict(shapes), "states_matched_to_exact_sector": matched,
         "empty_sectors": [[a, b] for a in range(8) for b in range(3) if (a, b) not in sectors],
         "states_matching_degree_formula": degree_matches,
         # All triple flips toggle total weight parity; this nonlocal readout
         # does not single out the common site or even distinguish supports.
         "active_events_flipping_global_parity":
             sum((s.bit_count() - offer(s, t).bit_count()) % 2 for s in states for t in enabled[s])},
        {"states_by_persistent_point": dict(sorted(clock_points.items())),
         "enabled_directed_events_flipping_persistent_point": flips,
         "phase_reversing_complements_in_same_sector": complements,
         "states_without_persistent_component_point": no_persistent},
    )


def verify():
    hits = {k: covering_families(7, k) for k in (6, 7)}
    # Independent of the search: compare its actual survivors to the complete
    # orbit of the standard Fano plane under site relabellings.
    model = tuple(t for t in combinations(range(7), 3)
                  if reduce(xor, (i + 1 for i in t)) == 0)
    orbit = {frozenset(sum(1 << perm[i] for i in t) for t in model)
             for perm in permutations(range(7))}
    lines = tuple(sum(1 << i for i in t) for t in model)
    dyn, clock = dynamics(lines)
    jams = [sum(all(offer(s, t) == s for t in lines if t != removed)
                for s in range(128)) for removed in lines]
    # A restored single-bit transfer changes only sites i and j. Test every
    # spectator setting, both directions, against a conserved XOR syndrome.
    excluded = sum(syndrome(s) != syndrome(s ^ (1 << i) ^ (1 << j))
                   for s in range(128) for i in range(7) for j in range(7)
                   if (s >> i) & 1 and not ((s >> j) & 1))
    return {
        "scope": "Simple undirected triples on at most seven sites, at most seven edges. "
                 "Smaller site sets embed by padding; no-jam is monotone under adding edges.",
        "search": {"labelled_candidate_counts": {k: comb(35, k) for k in hits},
                   "survivors": {k: len(v) for k, v in hits.items()},
                   "all_and_only_fano_relabellings": {frozenset(h) for h in hits[7]} == orbit},
        "dynamics": dyn, "clock": clock,
        "delete_one_line": {"jammed_states_per_deletion": jams},
        "transport": {"all_line_xors_zero": all(syndrome(t) == 0 for t in lines),
                      "directed_restored_moves_excluded": excluded},
        "boundary": "No-jam is optional. On the seven six-cycles the common enabled site "
                    "flips at every state-changing event; this gives no forced progression "
                    "under mixed offers, time scale, absolute phase in a shade-unlabelled "
                    "snapshot, physical detector or spatial embedding. Restored single-bit "
                    "transport is excluded on this support, not on every possible hardware.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = verify()
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(result["scope"])
        print("No-jam survivors by edge count:", result["search"]["survivors"])
        print("All and only Fano relabellings:", result["search"]["all_and_only_fano_relabellings"])
        print("Fano state components:", result["dynamics"]["components"])
        print("Clock-sector states by persistent site:", result["clock"]["states_by_persistent_point"])
        print(result["boundary"])
