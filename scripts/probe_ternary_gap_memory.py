"""Gap memory of indistinguishable T marks under undriven CS on a supplied ring.

Run: python3 -m scripts.probe_ternary_gap_memory [--json].

Reachability argument (elementary, not a Lean artifact). Clockwise after each
T, let H count b at odd minus even distances up to the next T. On a gap of
length L, complement the b bit at even distances. Now K = floor(L/2) + H
is its Hamming weight. Ordinary contacts exchange neighbouring transformed
bits, so every word with the same K is reachable with the marks fixed.
The whole fibre is connected and contains product_i binom(L_i,K_i) raw
states. Under uniform edge offers (including idle offers), the raw transition
matrix is symmetric, so the uniform law on a raw orbit is stationary. Its
pushforward weights fibres by these counts, not uniformly among fibres.

Only an a may cross a T. Inserting/deleting it at the front negates H;
at the back H is unchanged. For one T these operations affect the same
gap, giving one negation in total. For a nonempty gap an a can be exposed
at its front iff a zero is available in the transformed bits. At the back
it requires a zero for odd L and a one for even L. Hence each reduced hop
is realizable from its fibre, possibly after ordinary contacts; conversely
every raw move projects to a hop or stays in its fibre. Connected fibres
allow successive reduced hops to be lifted, giving exact reachability.

The cyclic list of |H| is conserved up to rotation and reversal, without
tag names: reversing a gap changes H by at most a sign. Since |H| <= ceil(L/2),
a gap with nonzero memory needs L >= 2|H|-1 ordinary sites. This is a
conditional separation bound, not a force or a universal exclusion rule.
External site indices make the audit reproducible; no geometry is inferred.
"""

import argparse
import json
from collections import deque
from itertools import combinations, product
from math import comb, prod

from scripts.probe_eight_label_interferometer import check
from scripts.probe_undriven_ternary_ring import active_moves, charge, ring_edges


def lengths(n, sites):
    """Clockwise gaps after the given sites, including zero and wraparound."""
    return tuple((q - p - 1) % n for p, q in zip(sites, sites[1:] + sites[:1]))


def reduce_word(raw):
    sites = tuple(i for i, x in enumerate(raw) if x == "T")
    if not sites or len(raw) < 3 or any(x not in "abT" for x in raw):
        raise ValueError("need a simple abT ring and at least one T")
    doubled = raw + raw
    gaps = (doubled[p + 1:p + L + 1] for p, L in zip(sites, lengths(len(raw), sites)))
    return tuple((p, w[::2].count("b") - w[1::2].count("b")) for p, w in zip(sites, gaps))


def memory(key):
    word = tuple(abs(h) for _, h in key)
    return min(w[i:] + w[:i] for w in (word, word[::-1]) for i in range(len(w)))


def multiplicity(n, key):
    sites, hs = zip(*key)
    return prod(comb(L, L // 2 + h) for L, h in zip(lengths(n, sites), hs))


def hops(n, key):
    """Existential tag hops in the connected fibre; these are not rates."""
    sites, hs = zip(*key)
    ls = lengths(n, sites)
    ks = tuple(L // 2 + h for L, h in zip(ls, hs))
    for i, (p, h) in enumerate(key):
        back = i - 1
        right_ok = ls[i] > 0 and ks[i] < ls[i]
        left_ok = ls[back] > 0 and (ks[back] < ls[back] if ls[back] % 2 else ks[back] > 0)
        for d, ok in ((1, right_ok), (-1, left_ok)):
            if ok:
                moved = list(key)
                moved[i] = ((p + d) % n, -h)
                yield tuple(sorted(moved))


def reduced_states(n, t):
    for sites in combinations(range(n), t):
        ls = lengths(n, sites)
        for ks in product(*(range(L + 1) for L in ls)):
            yield tuple((p, k - L // 2) for p, k, L in zip(sites, ks, ls))


def raw_states(n, t):
    for sites in combinations(range(n), t):
        for ordinary in product("ab", repeat=n - t):
            other = iter(ordinary)
            yield "".join("T" if i in sites else next(other) for i in range(n))


def census(n, t):
    """Compare literal and reduced partitions, not just sorted orbit sizes."""
    edges = ring_edges(n)
    if not 1 <= t <= n:
        raise ValueError("need 1 <= t <= n")
    unseen = set(reduced_states(n, t))
    owner = {}
    masses = []
    while unseen:
        start = unseen.pop()
        stack = [start]
        mass = 0
        while stack:
            key = stack.pop()
            owner[key] = len(masses)
            mass += multiplicity(n, key)
            for other in hops(n, key):
                if other in unseen:
                    unseen.remove(other)
                    stack.append(other)
        masses.append(mass)

    remaining = set(raw_states(n, t))
    raw_count = len(remaining)
    seen_components = set()
    while remaining:
        raw = remaining.pop()
        label = owner[reduce_word(raw)]
        check(label not in seen_components, "one reduced component covers separate literal orbits")
        seen_components.add(label)
        stack = [raw]
        size = 0
        while stack:
            raw = stack.pop()
            check(owner[reduce_word(raw)] == label, "literal orbit crosses reduced components")
            size += 1
            for _, other in active_moves(raw, edges):
                if other in remaining:
                    remaining.remove(other)
                    stack.append(other)
        check(size == masses[label], "raw size differs from the sum of fibre multiplicities")
    check(len(seen_components) == len(masses), "missing reduced components")
    return {"n": n, "tags": t, "raw_states": raw_count, "reduced_states": len(owner),
            "components": len(masses), "exact_partition_match": True}


def _matched_orbit(seed):
    edges = ring_edges(len(seed))
    queue = deque([(seed, 0)])
    seen = {seed}
    adjacent = 0
    first = None
    while queue:
        raw, depth = queue.popleft()
        if any(raw[i] == raw[j] == "T" for i, j in edges):
            adjacent += 1
            if first is None:
                first = depth
        for _, other in active_moves(raw, edges):
            if other not in seen:
                seen.add(other)
                queue.append((other, depth + 1))
    return {"seed": seed, "tag_sites": [i for i, x in enumerate(seed) if x == "T"],
            "initial_b_count": seed.count("b"), "initial_even_ring_K": charge(seed),
            "absolute_gap_memory": list(memory(reduce_word(seed))), "orbit_size": len(seen),
            "adjacent_states": adjacent, "min_changing_contacts": first}


def matched_pair():
    rows = [_matched_orbit(raw) for raw in ("TbabTaaa", "TbaaTbaa")]
    for field in ("tag_sites", "initial_b_count", "initial_even_ring_K"):
        check(rows[0][field] == rows[1][field], "preparations not matched on " + field)
    for row, expected in zip(rows, ((100, 48, 3), (92, 0, None))):
        check((row["orbit_size"], row["adjacent_states"], row["min_changing_contacts"]) == expected,
              "literal adjacency control failed")
    return rows


def rate_control():
    """Uniform edge offers: two members of one fibre give probabilities 1/8 vs 0."""
    raw_pair = ("TaabTaaa", "TbbbTaaa")
    target = reduce_word("aTabTaaa")
    edges = ring_edges(8)
    counts = [sum(reduce_word(other) == target for _, other in active_moves(raw, edges))
              for raw in raw_pair]
    same = reduce_word(raw_pair[0]) == reduce_word(raw_pair[1])
    check(same and counts == [1, 0], "rate control does not distinguish the two representatives")
    return {"sources": list(raw_pair), "same_reduced_source": same,
            "target": target, "offered_edges_to_same_target": counts, "total_edge_offers": len(edges)}


def verify():
    return {"census": [census(n, t) for n in range(4, 12) for t in (1, 2, 3)],
            "matched_preparations": matched_pair(), "rate_control": rate_control(),
            "scope": "Connectivity on a supplied cycle, not a rate law, attraction, Pauli "
                     "exclusion, calibrated ruler, spatial dimension, or physical measurement."}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, sort_keys=True))
        return
    print("Matched literal and reduced partitions:", len(report["census"]),
          "censuses;", sum(r["raw_states"] for r in report["census"]), "raw states")
    for row in report["matched_preparations"]:
        print(f"{row['seed']}: {row['adjacent_states']}/{row['orbit_size']} raw states adjacent; "
              f"minimum changed contacts = {row['min_changing_contacts']}")
    print("Same reduced source, counts reaching the same reduced target under one uniform offer:",
          report["rate_control"]["offered_edges_to_same_target"], "out of 8")
    print(report["scope"])


if __name__ == "__main__":
    main()
