"""Undriven reachability of the fixed CS contact on a supplied cycle with one T.

Run: python3 -m scripts.probe_undriven_ternary_ring [--json].
All edges may be offered; an event means a raw state change, never a unit
of elapsed time. Coordinates index an external exhaustive audit only.

Classification argument (not a Lean theorem). On deleting the T at p, the
ordinary sites form a path. XOR their b-indicators with alternating parity.
An ordinary CS encounter then exchanges adjacent transformed bits. These
exchanges connect every path word of the same transformed weight.

On C_(2m+1) the weight with parity 1 on even distances from p is m+h,
where h counts b at odd distances minus b at even distances, clockwise.
Hopping across an a moves the cut and negates h. For |h|<m both transformed
bits occur: path exchanges can expose an a at either end, then T can hop.
Thus T can reach any position and an odd lap interchanges the signs there.
At |h|=m the path alternates, its endpoints differ, and exactly the Ta
edge is enabled in both phases. There is one two-state orbit per ring edge.

On an even cycle use global bipartite parity instead, treating T as a for
the b-indicator. The total transformed weight K does not change on hops.
At p of parity e, the path has K-e ones. An a at either neighboring
endpoint needs transformed value 1-e: available at every placement when
0<K<n (a one for e=0, a zero for e=1). This connects the whole K-fiber;
at K=0 or n each permitted placement is a separate jammed state.

The raw census checks those predictions, not emergence of the graph, its
initial sector, a detector, a clock rate, or any physical interpretation.
"""

import argparse
import json
from collections import Counter
from itertools import product

from scripts.probe_eight_label_interferometer import check
from scripts.probe_ternary_active_readout import contact


def ring_edges(n, offset=0):
    if n < 3:
        raise ValueError("simple ring needs at least three vertices")
    return tuple((offset + i, offset + (i + 1) % n) for i in range(n))


def active_moves(raw, edges):
    """Yield every changed contact and its result; no chosen contact word."""
    for edge in edges:
        i, j = edge
        x, y = contact(raw[i], raw[j])
        if (x, y) != (raw[i], raw[j]):
            out = list(raw)
            out[i], out[j] = x, y
            yield edge, "".join(out)


def one_token_states(n):
    for ordinary in map("".join, product("ab", repeat=n - 1)):
        for p in range(n):
            yield ordinary[:p] + "T" + ordinary[p:]


def charge(raw):
    """Signed, cut-relative h for an odd ring; global K for an even ring."""
    if len(raw) % 2:
        p = raw.index("T")
        path = raw[p + 1:] + raw[:p]
        return path[::2].count("b") - path[1::2].count("b")
    return sum((x == "b") ^ (i % 2) for i, x in enumerate(raw))


def sector(raw, q):
    """Classify a raw state without consulting the active transition graph."""
    n = len(raw)
    p = raw.index("T")
    if n % 2:
        if abs(q) == n // 2:
            # Label this physical ring edge by its clockwise first endpoint.
            return ("dimer", p if raw[(p + 1) % n] == "a" else (p - 1) % n)
        return ("abs_h", abs(q))
    return ("jam", q, p) if q in (0, n) else ("K", q)


def census(n):
    edges = ring_edges(n)
    charges = {raw: charge(raw) for raw in one_token_states(n)}
    predicted = Counter(sector(raw, q) for raw, q in charges.items())
    unseen = set(charges)
    found = {}
    degrees = Counter()
    reflected = 0
    while unseen:
        seed = unseen.pop()
        key = sector(seed, charges[seed])
        stack = [seed]
        size = 0
        while stack:
            raw = stack.pop()
            size += 1
            check(sector(raw, charges[raw]) == key, "mixed predicted sectors in raw orbit")
            moves = list(active_moves(raw, edges))
            degrees[len(moves)] += 1
            if key[0] == "dimer":
                check(len(moves) == 1, "other enabled contact in dimer")
                (i, j), other = moves[0]
                check(i == key[1] and {raw[i], raw[j]} == {"T", "a"}, "wrong dimer bond")
                mirror = "".join(raw[(i + j - x) % n] for x in range(n))
                check(mirror == other, "snapshot reflection failed")
            for (i, j), other in moves:
                hop = "T" in (raw[i], raw[j])
                target_q = -charges[raw] if n % 2 and hop else charges[raw]
                check(charges[other] == target_q, "incorrect local charge transport")
                if other in unseen:
                    unseen.remove(other)
                    stack.append(other)
        check(key not in found and size == predicted[key], "disconnected predicted sector")
        found[key] = size
        if key[0] == "dimer":
            check(size == 2, "dimer not a doublet")
            reflected += 1
    check(found == predicted, "incomplete classification")
    edge_ends = sum(k * v for k, v in degrees.items())
    check(edge_ends == n * n * 2 ** (n - 2), "incorrect total active degree")
    return {"n": n, "states": len(charges), "edges": edge_ends // 2,
            "component_sizes": sorted(found.values()), "reflected_dimers": reflected,
            "jammed_states": degrees[0], "active_degree_histogram": dict(sorted(degrees.items()))}


def interface_control():
    """Two infinite alternating tails and two central sites; no closing bond."""
    def shade(i, phase):
        if i in (0, 1):
            return ("Ta", "aT")[phase][i]
        return ("ab" if i < 0 else "ba")[i % 2]

    # Bond representatives: both parities on each periodic tail, and all
    # three exceptional bonds (-1,0), (0,1), (1,2).
    for phase in (0, 1):
        for i in range(-3, 4):
            before = shade(i, phase), shade(i + 1, phase)
            after = contact(*before)
            expected = (shade(0, 1 - phase), shade(1, 1 - phase)) if i == 0 else before
            check(after == expected, "line interface leaked or stopped")
    return {"active_bond_each_phase": [0, 1], "alternating_tails": ["...ab", "ba..."]}


def bridged_control():
    """Two rings with unlike fixed bridge ends: a supplied frame, not a reader."""
    seed = "Tabab" + "Tababab"
    bridge = (2, 8)
    edges = (*ring_edges(5), *ring_edges(7, 5), bridge)
    reachable = {seed}
    stack = [seed]
    observables = set()
    while stack:
        raw = stack.pop()
        moves = list(active_moves(raw, edges))
        check({e for e, _ in moves} == {(0, 1), (5, 6)}, "clocks leaked or coupled")
        check(raw[bridge[0]] + raw[bridge[1]] == "ba", "bridge not inert")
        # Anonymous scalar per cycle: distance from its only T to the only
        # bridge endpoint in that cycle. Cycle length orders the two values.
        local = (raw[:5], raw[5:])
        deltas = [abs(word.index("T") - site) for word, site in zip(local, (2, 3), strict=True)]
        observables.add(tuple(min(d, len(w) - d) for w, d in zip(local, deltas, strict=True)))
        for _, nxt in moves:
            if nxt not in reachable:
                reachable.add(nxt)
                stack.append(nxt)
    check(len(reachable) == len(observables) == 4, "four independent framed phases not reached")
    return {"reachable_states": len(reachable), "active_edges_per_state": 2,
            "reachable_distance_pairs": sorted(map(list, observables)), "bridge_inert_throughout": True}


def verify():
    rows = [census(n) for n in range(3, 13)]
    return {"rings": rows, "line_interface": interface_control(), "bridged_pair": bridged_control(),
            "scope": "Finite reachability; disabled offers may idle. Supplied graph and preparation; "
                     "no elapsed-time law, synchronization, endogenous readout, or emergent geometry."}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = verify()
    if args.json:
        print(json.dumps(report, sort_keys=True))
        return
    for row in report["rings"]:
        print(f"C{row['n']}: {row['states']} states, {row['edges']} active edges, "
              f"{len(row['component_sizes'])} orbits, {row['reflected_dimers']} reflected dimers, "
              f"{row['jammed_states']} jammed states")
    print("Same rule on joined C5/C7:", report["bridged_pair"]["reachable_distance_pairs"])
    print(report["scope"])


if __name__ == "__main__":
    main()
