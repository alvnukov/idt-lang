"""Derive real one-packet additive laws from a small, target-blind grammar.

Supplied: a rooted folded carrier with a persistent two-turn mark, its 3+2
partition, flat binary germ readouts (root = empty), tuples of packets, and
synchronized reversible collision channels. The experiments compare completed
collision endpoints, not conservation during each of the two internal hops.
These classical operations are hypotheses; the grammar was considered after
the signed ballot was known. Agreement is not a blind prediction of nature.

A: swap two occupied/empty port entries of one packet within either group.
B: exchange two selected columns between two packets if both remain even.
C: from two blanks and one nonblank, pick a port whose class (group and
occupancy on the nonblank) is a singleton, move all three via that port;
include the inverse. Each precise template is a reversible channel, idle
otherwise. The grammar exhausts these *particular* choices, not all possible
covariant dynamics. All available channels are an external menu, not a
deterministic schedule, a probability law, or spontaneous packet creation.
No target, charge filter, fitted weights, or final-value test in the updates.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import gcd, lcm

PORTS = tuple(range(5))
LARGE, SMALL = PORTS[:3], PORTS[3:]
PAIRS = tuple(combinations(PORTS, 2))
STATES = tuple(x for x in range(32) if x.bit_count() % 2 == 0)
INDEX = {x: i for i, x in enumerate(STATES)}


def need(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def germ(x, j):
    return (x >> j) & 1


def hop(x, j):
    # One base edge, in the fixed even representation: only the held germ
    # does not flip. The final comparison checks this against actual graphs.
    return x ^ (31 ^ (1 << j))


def occ(x):
    return (x & 7).bit_count(), (x & 24).bit_count()


def shuffle(x, i, j):
    if (i in SMALL) == (j in SMALL) and germ(x, i) != germ(x, j):
        return hop(hop(x, i), j)
    return x


def exchange(pair, i, j):
    x, y = pair
    delta = (x ^ y) & ((1 << i) | (1 << j))
    if delta.bit_count() % 2 == 0:
        return x ^ delta, y ^ delta
    return pair


def unique_classes(x):
    """Four possible raw port classes, including empty classes of size 0."""
    for name, block in (("large", LARGE), ("small", SMALL)):
        for value in (0, 1):
            entry = [j for j in block if germ(x, j) == value]
            if len(entry) == 1:
                yield (name, value), entry[0]


def ternary_library():
    specs = defaultdict(dict)
    occupations = sorted({occ(x) for x in STATES if x})
    for x in STATES:
        if not x:
            continue
        for (name, value), h in unique_classes(x):
            spec = (*occ(x), name, value)
            src = (0, 0, x)
            dst = tuple(sorted(hop(v, h) for v in src))
            rule = specs[spec]
            need(src not in rule and dst not in rule and src != dst, "not disjoint reversible exchanges")
            rule[src] = (dst, h)
            rule[dst] = (src, h)
    return occupations, dict(specs)


def fire(triple, rule):
    hit = rule.get(tuple(sorted(triple)))
    return triple if hit is None else tuple(hop(x, hit[1]) for x in triple)


def difference(a, b):
    d = [0]*len(STATES)
    for x, y in zip(a, b, strict=True):
        d[INDEX[x]] -= 1
        d[INDEX[y]] += 1
    return tuple(d if next((z for z in d if z), 0) >= 0 else (-z for z in d))


def kernel(rows, n=16):
    """Exact Gauss-Jordan elimination. Return a basis, not only a rank."""
    basis = {}
    for row in sorted(rows):
        v = list(map(Fraction, row))
        for p, b in sorted(basis.items()):
            a = v[p]
            if a:
                v = [x-a*y for x, y in zip(v, b, strict=True)]
        p = next((j for j, value in enumerate(v) if value), None)
        if p is None:
            continue
        a = v[p]
        v = [x/a for x in v]
        for i, old in basis.items():
            a = old[p]
            if a:
                basis[i] = [x-a*y for x, y in zip(old, v, strict=True)]
        basis[p] = v
    return [tuple(-basis[i][j] if i in basis else Fraction(i == j) for i in range(n))
            for j in range(n) if j not in basis]


def check_span(rows, vectors):
    # Membership and independence, together with kernel dimension, imply
    # spanning all real invariants (the integer matrix has the same rank).
    d = len(vectors)
    need(all(sum(x*y for x, y in zip(r, v, strict=True)) == 0 for r in rows for v in vectors), "not invariant")
    need(len(kernel(rows)) == d and len(kernel(vectors)) == len(STATES)-d, "incomplete basis")
    return d


def primitive(values):
    den = lcm(*(x.denominator for x in values))
    ns = tuple(int(x*den) for x in values)
    scale = gcd(*ns)
    need(scale != 0, "zero vector cannot orient a ray")
    return tuple(x//scale for x in ns)


def binary_layers():
    a, b = set(), set()
    for x, (i, j) in product(STATES, PAIRS):
        y = shuffle(x, i, j)
        need(shuffle(y, i, j) == x, "unary involution")
        a.add(difference((x,), (y,)))
    for pair, (i, j) in product(product(STATES, repeat=2), PAIRS):
        out = exchange(pair, i, j)
        need(exchange(out, i, j) == pair and all(x in INDEX for x in out), "binary reciprocity/parity")
        need(all(sum(germ(x, h) for x in pair) == sum(germ(x, h) for x in out) for h in PORTS),
             "raw column exchange")
        if pair != out:
            need(out == tuple(hop(hop(x, i), j) for x in pair), "two-hop implementation")
        b.add(difference(pair, out))
    a.discard((0,)*16)
    b.discard((0,)*16)
    return a, b


def relabel(x, image):
    return sum(germ(x, j) << image[j] for j in PORTS)


def audit_ternary(spec, rule, ab_rows):
    # Test actual ordered carriers, inverses, and setwise covariance. IDLE
    # self-loops need no constraint row. Covariance on the nonidle domain
    # implies covariance on the complement because relabelings are bijective.
    changed = 0
    for s in product(STATES, repeat=3):
        t = fire(s, rule)
        need(fire(t, rule) == s, "not reversible on labeled carriers")
        if t != s:
            changed += 1
            need(tuple(sorted(t)) == rule[tuple(sorted(s))][0], "ordered lift mismatch")
    for c, w in product(permutations(LARGE), permutations(SMALL)):
        image = c+w
        for s, (t, h) in rule.items():
            s2, t2 = (tuple(sorted(relabel(x, image) for x in cfg)) for cfg in (s, t))
            need(rule[s2] == (t2, image[h]), "rule is not 3+2 covariant")
    directed = [(s, t) for s, (t, _) in rule.items() if s[:2] == (0, 0)]
    need(2*len(directed) == len(rule), "inverse not captured")
    rows = {difference(s, t) for s, t in directed}
    occupation_changes = {
        tuple(sum(occ(x)[i] for x in t)-sum(occ(x)[i] for x in s) for i in (0, 1)) for s, t in directed}
    need(len(occupation_changes) == 1, "changed block counts differ across orbit")
    dc, dw = occupation_changes.pop()
    laws = ab_rows | rows
    # Constants are the trivial fixed packet count. Set f(blank)=0 to
    # remove them, then calibrate primitive integer values and orient by
    # f(mark)>0, with no target table involved.
    ground = (1,) + (0,)*15
    family = kernel(laws | {ground})
    need(len(kernel(laws)) == 2 and len(family) == 1, "template should select a single nonconstant line")
    field = primitive(family[0])
    if field[INDEX[24]] < 0:
        field = tuple(-z for z in field)
    need(field[INDEX[24]] > 0, "cannot orient by the mark")
    # On even states the unit slopes are half the two-of-a-kind readings.
    slopes = (Fraction(field[INDEX[3]], 2), Fraction(field[INDEX[24]], 2))
    ray = primitive(slopes)
    need(all(f == slopes[0]*occ(x)[0]+slopes[1]*occ(x)[1] for x, f in zip(STATES, field, strict=True)),
         "incorrect inferred slopes")
    need(dc*ray[0] + dw*ray[1] == 0, "ray not orthogonal to orbit increment")
    data = {"spec": list(spec), "delta": [dc, dw], "primitive_weight_ray": ray,
            "integer_weight_field_gcd": gcd(*(ray[0]*occ(x)[0]+ray[1]*occ(x)[1] for x in STATES)),
            "unordered_swaps": len(directed), "ordered_inputs_changed": changed}
    return rows, field, data


def compare_all_frames(fields, specs):
    # Independent native ballot. Target reader enters ONLY after the
    # complete collision library has been generated and its kernels solved.
    from scripts.probe_two_turn_germ_ballots import forced_completion, record, votes

    graph = forced_completion()
    matches = Counter({s: 0 for s in fields})
    changes = defaultdict(set)
    for root in range(len(graph)):
        reads = record(graph, root)
        for mark in set(range(len(graph))) - {root} - graph[root]:
            order = sorted(reads, key=lambda j: (reads[j][mark], j))
            coords = {v: sum(reads[j][v] << k for k, j in enumerate(order)) for v in range(len(graph))}
            need(coords[root] == 0 and coords[mark] == 24 and set(coords.values()) == set(STATES), "bad frame")
            ballot = {}
            for v, x in coords.items():
                need({coords[w] for w in graph[v]} == {hop(x, j) for j in PORTS}, "hop not a physical base edge")
                signed, _ = votes(reads, mark, v)
                ballot[x] = signed
                for spec, field in fields.items():
                    matches[spec] += int(field[INDEX[x]] == signed)
            for spec, rule in specs.items():
                for s, (t, _) in rule.items():
                    if s[:2] == (0, 0):
                        changes[spec].add(sum(ballot[x] for x in t)-sum(ballot[x] for x in s))
    return matches, changes


def preparation_components(rule, field):
    # Reachability of three unordered coaddressable packets under all moves
    # of the selected library; A/B can act with idle spectators. Do NOT
    # filter by any f. Compute the field partition only after the closure.
    triples = tuple(combinations_with_replacement(STATES, 3))
    yet, groups = set(triples), []
    while yet:
        seed = min(yet)
        component, todo = {seed}, [seed]
        while todo:
            s = todo.pop()
            neighbours = {tuple(sorted(fire(s, rule)))}
            for i, j in PAIRS:
                for k in range(3):
                    t = list(s)
                    t[k] = shuffle(s[k], i, j)
                    neighbours.add(tuple(sorted(t)))
                for k, l in combinations(range(3), 2):
                    t = list(s)
                    t[k], t[l] = exchange((s[k], s[l]), i, j)
                    neighbours.add(tuple(sorted(t)))
            todo.extend(neighbours-component)
            component.update(neighbours)
        need(component <= yet, "not a reversible component")
        yet -= component
        groups.append(component)
    need(sum(map(len, groups)) == len(triples) and {(0, 0, 0)} in groups, "blank-only closure")
    # Possible external preparation in a fixed frame: route one blank
    # through one large-held and one small-held edge; keep two blanks at
    # hand. This path is NOT available inside the collision-only schedule.
    prep_path = (0, hop(0, 0), hop(hop(0, 0), 3))
    need(prep_path == (0, 30, 9), "external two-step preparation")
    source = (0, 0, prep_path[-1])
    component, = (c for c in groups if source in c)
    need(tuple(sorted(fire(source, rule))) in component and fire(source, rule) != source, "seed fails to react")
    def val(s):
        return sum(field[INDEX[x]] for x in s)

    need(all(len({val(s) for s in c}) == 1 for c in groups), "post hoc field varies in component")
    sector_components = defaultdict(list)
    for c in groups:
        sector_components[val(min(c))].append(len(c))
    return {"triples": len(triples), "components": len(groups), "field_totals": len({val(s) for s in triples}),
            "all_blank_reachable": 1, "mixed_seed_reachable": len(component),
            "mixed_seed_total_sector_size": sum(val(s) == val(source) for s in triples),
            "external_single_packet_preparation_path": prep_path,
            "split_total_sectors": {k: sorted(v) for k, v in sector_components.items() if len(v) > 1}}


def probe():
    a, b = binary_layers()
    occupations, specs = ternary_library()
    ones, cs, ws = (1,)*16, tuple(occ(x)[0] for x in STATES), tuple(occ(x)[1] for x in STATES)
    dimensions = {
        "A": check_span(a, [tuple(int(occ(x) == o) for x in STATES) for o in [(0, 0), *occupations]]),
        "B": check_span(b, [ones, *(tuple(germ(x, j) for x in STATES) for j in PORTS)]),
        "A+B": check_span(a | b, [ones, cs, ws]),
    }
    fields, data, union = {}, {}, a | b
    for spec, rule in sorted(specs.items()):
        rows, fields[spec], data[spec] = audit_ternary(spec, rule, a | b)
        union = union | rows
    dimensions["A+B+all_C"] = check_span(union, [ones])
    matches, changes = compare_all_frames(fields, specs)
    for s, d in data.items():
        d["ballot_equal_at_2560_points"] = matches[s]
        d["forward_total_ballot_change"] = sorted(changes[s])
    winners = [s for s in fields if matches[s] == 2560]
    need(len(winners) == 1, "comparison did not select exactly one template")
    preferred, = winners
    need([s for s in fields if changes[s] == {0}] == winners, "collision ballot conservation mismatch")
    need(preferred == (1, 1, "large", 1), "signed ballot agreement did not reproduce")
    need(len(specs) == 7 and len(set(fields.values())) == 6, "singleton grammar coverage")
    return {"dimensions_real": dimensions, "A_and_B_nonzero_rows": [len(a), len(b)],
            "nonblank_occupations_without_singletons": [o for o in occupations if not any(k[:2] == o for k in specs)],
            "rules": list(data.values()), "matching_template": preferred,
            "preparation": preparation_components(specs[preferred], fields[preferred]),
            "scope": "post hoc agreement of two classical constructions, not physical charge or a firing law"}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, indent=2))
