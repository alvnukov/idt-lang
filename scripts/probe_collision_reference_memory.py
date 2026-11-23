"""Finite reference calibration in the one-command three-packet grammar.

Inputs are three named even five-germ records (an unordered multiset), a
fixed marked pair, a repeatable command, and an exact tagged occupancy.
Naming records and repeating preparations with the SAME retained root are
premises. No noise, joint multi-preparation query, free inspection of the
root, detector physics, charge, or origin-generation process is supplied.
Run independently: python3 scripts/probe_collision_reference_memory.py

An eligible input has majority y and singleton y XOR d with d differing at
one small and one large port h. A firing flips mask g_h (all but h) on each
packet. Anchored-at-r fires precisely on r in {y,y XOR g_h}; relative always
fires on eligible inputs. Any tagged output from one fixed preparation is
therefore constant on that edge and its complement. Idle and fired occupancies
can coincide at a poor tag. The majority tag distinguishes the two outcomes.

For a fixed partition the three g_h are independent, so eligible tests are
the edges of two disjoint 3-cubes. A nonadaptive set of tested edges identifies
all roots iff it has at most one isolated vertex and no isolated K2 component:
two different vertices can share a nonempty edge-incidence signature only
when they are isolated endpoints of one edge. Components containing neither
exception need at least 3 vertices. On 8 vertices there are at most 2 such
components without an isolate, or 3 total with one; across two cubes at most
5 components, hence at least 11 edges. Path partitions below attain it.
Adaptively, on 7 successive negative membership answers at least 2 roots
remain; 7 matching-edge tests followed by a split of the known pair suffice.
These optima count resettable one-preparation commands, not time or energy.
"""

from __future__ import annotations

import json
from itertools import combinations, combinations_with_replacement, pairwise

PORTS = tuple(range(5))
RECORDS = tuple(x for x in range(32) if x.bit_count() % 2 == 0)
TRIPLES = tuple(combinations_with_replacement(RECORDS, 3))
MARK = (3, 4)


def need(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def shifted(triple, shift):
    return tuple(sorted(x ^ shift for x in triple))


def generators(mark):
    return tuple(31 ^ (1 << h) for h in PORTS if h not in mark)


def tables(mark):
    """Construct forward and inverse exchanges independently at each named origin."""
    anchored = {r: {} for r in RECORDS}
    relative = {}
    for r, table in anchored.items():
        for h in set(PORTS) - set(mark):
            for s in mark:
                src = tuple(sorted((r, r, r ^ (1 << h) ^ (1 << s))))
                dst = shifted(src, 31 ^ (1 << h))
                for a, b in ((src, dst), (dst, src)):
                    need(table.setdefault(a, b) == b and relative.setdefault(a, b) == b,
                         "exchanges must be single valued")
    return anchored, relative


def edge(u, v):
    return tuple(sorted((u, v)))


def cubes(mark):
    gens = generators(mark)
    # Gray path in the three-generator span, represented by actual named
    # germ records; these temporary coordinates are not spatial coordinates.
    walk = [0]
    for g in gens:
        walk += [v ^ g for v in reversed(walk)]
    offset = next(r for r in RECORDS if r not in walk)
    other = [r ^ offset for r in walk]
    need(len(set(walk) | set(other)) == 16 and len(set(walk)) == 8, "two disjoint 3-cubes")
    return walk, other


def certificate(mark):
    first, second = cubes(mark)
    gens = generators(mark)
    edges = {edge(y, y ^ g) for y in RECORDS for g in gens}
    # Keep successive edges inside path pieces of sizes 1,3,4 and 3,5.
    pieces = (first[:1], first[1:4], first[4:], second[:3], second[3:])
    tests = [edge(u, v) for path in pieces for u, v in pairwise(path)]
    need(len(tests) == 11 and set(tests) <= edges, "valid nonadaptive certificate")
    anchors, rel = tables(mark)

    def preparation(e):
        y, v = e
        held_bit = 31 ^ y ^ v
        return tuple(sorted((y, y, y ^ held_bit ^ (1 << mark[0]))))

    def reports_departure(e, table):
        triple = preparation(e)
        return table.get(triple, triple).count(e[0]) == 0

    need(all(reports_departure(e, table) == (r in e) for e in edges for r, table in anchors.items()),
         "replay calibration edges as tagged occupancy commands")
    codes = {tuple(reports_departure(e, table) for e in tests) for table in anchors.values()}
    need(len(codes) == 16, "nonadaptive identification")

    # Independently search *all* 2^12 edge subsets of each isomorphic cube;
    # combine by number of zero codes; nonzero codes on distinct cubes differ.
    one_edges = sorted(e for e in edges if e[0] in first)
    need(len(edges) == 24 and len(one_edges) == 12, "membership test counts")
    best = {}
    for mask in range(1 << len(one_edges)):
        signatures = [sum(1 << i for i, e in enumerate(one_edges) if r in e and mask & (1 << i)) for r in first]
        nz = [v for v in signatures if v]
        isolates = len(first) - len(nz)
        if isolates <= 1 and len(set(nz)) == len(nz):
            best[isolates] = min(mask.bit_count(), best.get(isolates, 13))
    need(best == {0: 6, 1: 5} and min(best[a]+best[b] for a in best for b in best if a+b <= 1) == 11,
         "nonadaptive lower bound by exhaustive edge subsets")

    matching = sorted({edge(y, y ^ gens[0]) for y in RECORDS})
    depths = []
    for root in RECORDS:
        pair = matching[-1]
        queries = []
        for e in matching[:-1]:
            queries.append(e)
            if reports_departure(e, anchors[root]):
                pair = e
                break
        split = edge(pair[0], pair[0] ^ gens[1])
        queries.append(split)
        inferred = pair[0] if reports_departure(split, anchors[root]) else pair[1]
        need(inferred == root and set(queries) <= edges, "adaptive decoder")
        depths.append(len(queries))
    need(max(depths) == 8 and len(RECORDS)-2*7 == 2, "adaptive optimum")
    # Under the two-family promise this shorter test distinguishes laws, not
    # the retained root: relative answers yes on both disjoint matching edges.
    two = matching[:2]
    need(all(reports_departure(e, rel) for e in two)
         and not any(all(reports_departure(e, table) for e in two) for table in anchors.values()),
         "two positives exclude any fixed absolute root")
    return {"components": [first, second], "test_edges": sorted(tests), "min_edges_in_cube_by_isolates": best,
            "adaptive_matching": matching, "adaptive_worst_case": max(depths),
            "absolute_vs_relative_tests": [{"packets": preparation(e), "tag": e[0]} for e in two]}


def check_finite_laws():
    # Signatures on common named preparations, NOT on partition-specific lists.
    absolute, relative = set(), set()
    for mark in combinations(PORTS, 2):
        anchors, rel = tables(mark)
        moved = frozenset(rel)
        relative.add(moved)
        need(len(moved) == 96, "relative changed unordered preparations")
        for table in anchors.values():
            need(len(table) == 12, "absolute changed unordered preparations")
            absolute.add(frozenset(table))
        # Independent eligibility and root query on EVERY unordered input.
        edges = set()
        for triple in TRIPLES:
            a, y, c = triple
            delta = a ^ c
            differences = [h for h in PORTS if delta & (1 << h)]
            large = [h for h in differences if h not in mark]
            mixed = (a == y or y == c) and len(differences) == 2 and len(large) == 1
            firing_roots = {r for r, t in anchors.items() if triple in t}
            if not mixed:
                need(not firing_roots and triple not in moved, "ineligible inputs cannot identify roots")
                continue
            mask = 31 ^ (1 << large[0])
            after = shifted(triple, mask)
            expected = {y, y ^ mask}
            need(firing_roots == expected and rel[triple] == after and after.count(y) == 0, "majority tag")
            need(all(anchors[r][triple] == after and anchors[r][after] == triple for r in expected), "reversal")
            edges.add(edge(*sorted(expected)))
            for tag in RECORDS:
                # Even allowing any tag, its count bin has 0, 2, 14 or 16
                # possible roots; any possible nonconstant answer is an edge
                # membership bit, or its complement. Full output gives no more.
                counts = {triple.count(tag), after.count(tag)}
                need(len(counts) <= 2 and all(
                    anchors[r].get(triple, triple).count(tag) == (after if r in expected else triple).count(tag)
                    for r in RECORDS), "unexpected finer tag information")
        need(len(edges) == 24, "all edges exposed by majority tags")
    need((len(absolute), len(relative), len(absolute | relative)) == (160, 10, 170),
         "behavioral states on named preparations for all partitions")
    return {"fixed_partition_absolute": 16, "fixed_partition_relative": 1,
            "all_partitions_absolute": len(absolute), "all_partitions_relative": len(relative),
            "minimum_binary_behavior_index_bits": {"absolute_fixed_mark": 4, "absolute_with_mark": 8,
                                                    "relative_with_mark": 4}}


def translation_control():
    anchors, rel = tables(MARK)
    # Test passive relabeling on every changed input for every table.
    # Since translation is bijective and support size is fixed this also
    # covers unchanged inputs outside support.
    for shift in RECORDS:
        for r, table in anchors.items():
            need({shifted(x, shift): shifted(z, shift) for x, z in table.items()} == anchors[r ^ shift],
                 "passive frame shift changed predictions")
        need({shifted(x, shift): shifted(z, shift) for x, z in rel.items()} == rel,
             "relative law lost translation covariance")
    initial = (0, 0, 9)
    active = shifted(initial, 3)
    anchored_active = anchors[0].get(active, active)
    anchored_passive = anchors[3][active]
    need(anchors[0][initial] == (23, 30, 30) and active == (3, 3, 10) and anchored_active == active
         and rel[active] == anchored_passive == (20, 29, 29), "active translation control")
    return {"initial": initial, "absolute_output_root_0": anchors[0][initial],
            "translated_preparation": active, "translated_absolute_fixed_root": anchored_active,
            "translated_absolute_shifted_root": anchored_passive, "translated_relative": rel[active]}


if __name__ == "__main__":
    print(json.dumps({"status": "finite_named_record_command_only", "laws": check_finite_laws(),
                      "calibration_fixed_mark": certificate(MARK), "translation": translation_control(),
                      "resource_boundary": "Behavioral index capacity if a selectable law is not externally supplied; "
                      "not a mandatory internal register, storage cost, or spontaneous frame selection."}, sort_keys=True))
