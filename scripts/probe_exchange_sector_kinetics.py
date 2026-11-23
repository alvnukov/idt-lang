"""Does equal hopping on the folded carrier energetically select odd exchange?

Supply two packets, one-at-a-time nearest-neighbor hops, no coincidence, and
real linear addition of transfers. The same ordered, off-diagonal graph has
an even and an odd sector under interchange of its two slots. Positive path
counts and signed path sums are not the same observable. Neither is an event
probability. No temperature, attraction, chosen sign defect, charge, spin,
or one-body flux is fitted. Comparing both kinetic signs does not convert
the base graph into a Hamiltonian. A passive spring Laplacian has a further
degree diagonal, which is NOT constant on this pair graph.

The small detector uses two occupied arms of a three-arm star as input. Test
the center and the remaining arm as a pair after three transfers. A tree has
no independent one-packet loop flux. The closed six-hop exchange on this star
is the Y used in probe_two_packet_exchange_topology; the comparison here
builds the actual walk operators, not that script's homology presentation.
"""

import json
from collections import Counter, deque
from itertools import combinations, pairwise

from scripts.probe_anonymous_folded_carrier import forced_completion, square_directions


def need(test, message):
    if not test:
        raise ArithmeticError(message)


def hops(graph, a, b):
    return [(v, b) for v in graph[a] if v != b] + [(a, v) for v in graph[b] if v != a]


def operators(graph):
    pairs = tuple(combinations(range(len(graph)), 2))
    ix = {pair: i for i, pair in enumerate(pairs)}
    rows = []
    for a, b in pairs:
        row = {
            ix[tuple(sorted((u, v)))]: (1 if u < v else -1)
            for u, v in hops(graph, a, b)
        }
        need(len(row) == len(hops(graph, a, b)), "different physical hops collapsed")
        rows.append(row)
    need(all(rows[j].get(i) == s for i, r in enumerate(rows) for j, s in r.items()),
         "transfer is not reciprocal")
    seen, todo = {0}, [0]
    while todo:
        i = todo.pop()
        more = rows[i].keys() - seen
        seen.update(more)
        todo.extend(more)
    need(len(seen) == len(pairs), "hard-core pair graph is disconnected")
    return pairs, rows


def act(rows, v, signed):
    return tuple(sum((s if signed else 1) * v[j] for j, s in row.items()) for row in rows)


def dot(x, y):
    return sum(a*b for a, b in zip(x, y, strict=True))


def one_packet_modes(graph):
    # Construct auxiliary sign eigenvectors from unweighted adjacency, not
    # extra edge couplings. Along one matching the sign stays, else it flips.
    _, matchings = square_directions(graph)
    low = []
    for held in sorted(matchings, key=sorted):
        f, todo = {0: 1}, deque([0])
        while todo:
            u = todo.popleft()
            for v in graph[u]:
                y = f[u] * (1 if tuple(sorted((u, v))) in held else -1)
                if v not in f:
                    f[v] = y
                    todo.append(v)
                need(f[v] == y, "inconsistent sign eigenvector construction")
        low.append(tuple(f[v] for v in range(len(graph))))
    n = len(graph)
    mixed = [tuple(a*b for a, b in zip(f, h, strict=True)) for f, h in combinations(low, 2)]
    modes = [(5, (1,)*n), *((-3, f) for f in low), *((1, f) for f in mixed)]
    need(len(modes) == n == 16, "one-body mode count")
    for i, (e, f) in enumerate(modes):
        need(all(sum(f[w] for w in graph[v]) == e*f[v] for v in range(n)), "one-body mode")
        need(dot(f, f) == n and not any(dot(f, h) for _, h in modes[:i]), "nonorthogonal modes")
    return modes, low


def spectra(graph, pairs, rows):
    modes, low = one_packet_modes(graph)
    # In the odd extension the value on a collision is identically zero.
    # The wedges of the orthogonal one-body basis are an orthogonal basis
    # on the 120 pairs. Verify their actual physical hop action independently.
    odd_spectrum = Counter()
    for (e, f), (h, g) in combinations(modes, 2):
        w = tuple(f[a]*g[b] - f[b]*g[a] for a, b in pairs)
        need(dot(w, w) == len(graph)**2 and
             act(rows, w, True) == tuple((e+h)*x for x in w), "exterior transfer")
        odd_spectrum[e+h] += 1
    need(odd_spectrum == {-6: 10, -2: 50, 2: 50, 6: 10}, "odd spectrum")

    # The Perron eigenvector can be taken positive on both pair types. For
    # [[0,8],[4,6]], its eigenvalue solves L^2 - 6 L - 32 = 0 and is > 6.
    types = [int(b not in graph[a]) for a, b in pairs]
    quotient = ((0, 8), (4, 6))
    for t, row in zip(types, rows, strict=True):
        need(tuple(sum(types[j] == u for j in row) for u in (0, 1)) == quotient[t],
             "pair types are not an equitable partition")
    need(Counter(types) == {0: 40, 1: 80}, "pair type census")

    # Compress A tensor I + I tensor A to zero diagonal, in the symmetric
    # slot sector. The uncompressed minimum is -6; equality after compression
    # requires membership in Sym^2 of the five-dimensional bottom eigenspace.
    # Its diagonal evaluations span 1 and ten distinct products f_i*f_j,
    # proven independent above. Thus the bottom nullity is 15 - 11 = 4.
    # The four exact trace-free differences below realize it, with no on-site
    # term or odd-exchange rule. Hard-core exclusion alone is not Pauli.
    witnesses = [tuple(f[a]*f[b]-low[0][a]*low[0][b] for a, b in pairs) for f in low[1:]]
    for i, w in enumerate(witnesses):
        need(act(rows, w, False) == tuple(-6*x for x in w), "unsigned bottom witness")
        need([dot(w, z) for z in witnesses] == [256 if j == i else 128 for j in range(4)],
             "bottom witnesses not independent")
    return {"one_packet": dict(Counter(e for e, _ in modes)), "odd": dict(odd_spectrum),
            "unsigned_equitable_adjacent_nonadjacent": quotient,
            "unsigned_top": "3+sqrt(41)", "unsigned_top_multiplicity": 1,
            "unsigned_bottom": -6, "unsigned_bottom_multiplicity": 4,
            "H_minus_adjacency": "even lower; odd-minus-even minimum gap sqrt(41)-3",
            "H_plus_adjacency": "even and odd tie at -6; multiplicities 4 and 10"}


def ordered_counts(graph, start, ticks, weights=None):
    """No waiting, probability normalization, pruning or postselection."""
    states = Counter({start: 1})
    for _ in range(ticks):
        new = Counter()
        for (a, b), k in states.items():
            for u, v in hops(graph, a, b):
                bond = (a, u) if a != u else (b, v)
                new[u, v] += k if weights is None else k*weights[tuple(sorted(bond))]
        states = new
    return states


def sectors(counts, target):
    retained = counts[target]
    exchanged = counts[target[::-1]]
    return retained + exchanged, retained - exchanged


def returns(graph, pairs, rows):
    expected = {True: [(1, 1), (0, 0), (8, 8), (0, 0), (208, 176), (288, 0)],
                False: [(1, 1), (0, 0), (10, 10), (0, 0), (272, 256), (384, 0)]}
    for i, (a, b) in enumerate(pairs):
        even = odd = tuple(int(j == i) for j in range(len(pairs)))
        for u, v in expected[b in graph[a]]:
            need((even[i], odd[i]) == (u, v), "diagonal transfer by pair type")
            even, odd = act(rows, even, False), act(rows, odd, True)
    # B^4-40B^2+144I=0 in the odd sector by its entire checked spectrum.
    # Zero diagonal at ticks one and three therefore forces zero at every
    # odd tick. The unsigned graph already has odd return walks at tick five.
    return {"adjacent_even_odd_ticks_0_through_5": expected[True],
            "nonadjacent_even_odd_ticks_0_through_5": expected[False],
            "all_odd_ticks_signed_diagonal": 0}


def star_test(graph, pairs, rows):
    center = 0
    a, b, c = sorted(graph[center])[:3]
    start, target = (a, b), (center, c)
    ix = {p: i for i, p in enumerate(pairs)}
    # This six-hop Y exchange traverses each base bond twice. It directly
    # obstructs gauging the odd pair signs to positive (and hence also
    # obstructs a nonzero zero mode of the connected signed spring network).
    loop = [(a, b), (center, b), (c, b), (c, center), (c, a), (center, a), (b, a)]
    s = 1
    for p, q in pairwise(loop):
        s *= rows[ix[tuple(sorted(p))]][ix[tuple(sorted(q))]]
    need(s == -1, "Y exchange lost its gauge-invariant sign")
    full_rows = [sectors(ordered_counts(graph, start, k), target) for k in range(4)]
    full = full_rows[-1]
    star = {center: {a, b, c}, a: {center}, b: {center}, c: {center}}
    cut = sectors(ordered_counts(star, start, 3), target)
    need(full_rows == [(0, 0)]*3 + [(8, 0)] and cut == (2, 0), "three-hop comparison")
    # The odd operator's checked quartic recurrence and the first four zero
    # entries imply this full-graph signed transfer is zero for every tick.
    # Exhaust the isolated first-arrival paths and inspect their actual bonds:
    # both use all three spokes once, for ANY nonzero real reciprocal weights
    # that depend only on the base edge, not on the spectator or the time.
    paths = [(start, (), ())]
    for _ in range(3):
        expanded = []
        for p, bs, es in paths:
            for q in hops(star, *p):
                bond, = (tuple(sorted((u, v))) for u, v in zip(p, q, strict=True) if u != v)
                edge = tuple(sorted((tuple(sorted(p)), tuple(sorted(q)))))
                expanded.append((q, (*bs, bond), (*es, edge)))
        paths = expanded
    hits = [(q, bs, es) for q, bs, es in paths if q in (target, target[::-1])]
    spokes = {tuple(sorted((center, v))) for v in (a, b, c)}
    need(Counter(q for q, _, _ in hits) == {target: 1, target[::-1]: 1}
         and all(len(bs) == 3 and set(bs) == spokes for _, bs, _ in hits), "spoke product changed")
    need(all(sectors(ordered_counts(star, start, k), target) == (0, 0) for k in range(3)),
         "target already reached before three hops")
    weights = {tuple(sorted((center, v))): w for v, w in zip((a, b, c), (2, -3, 5), strict=True)}
    need(sectors(ordered_counts(star, start, 3, weights), target) == (-60, 0),
         "reciprocal one-body weighting control")
    # A transfer depending on which other site is occupied is a different
    # contract: double one reciprocal pair edge of just one path. The odd
    # null disappears, although all six Y pair edges and their signs remain.
    changed_edge = hits[0][2][0]
    disturbed = Counter({q: 2**es.count(changed_edge) for q, _, es in hits})
    damaged = sectors(disturbed, target)
    need(damaged[0] == 3 and abs(damaged[1]) == 1, "spectator-sensitive control")
    return {"source": start, "target": target, "center_and_enabled_neighbors": [center, a, b, c],
            "three_hop_even_odd_full_graph": full, "three_hop_even_odd_isolated_Y": cut,
            "all_ticks_full_graph_odd_source_to_target": 0,
            "isolated_Y_symbolic_even_odd": ["2*w_a*w_b*w_c", "0"],
            "one_spectator_sensitive_pair_bond_doubled_even_and_abs_odd": [damaged[0], abs(damaged[1])],
            "Y_exchange_closed_sign": s,
            "passive_pair_stiffness_D_minus_B": "even constant zero mode; odd strictly positive"}


def probe():
    graph = forced_completion()
    pairs, rows = operators(graph)
    return {"scope": "supplied hard core and reciprocal real linear transfer; no physical statistics selection",
            "pair_vertices": len(pairs), "pair_edges": sum(map(len, rows))//2,
            "spectra": spectra(graph, pairs, rows), "diagonal_returns": returns(graph, pairs, rows),
            "short_pair_readout": star_test(graph, pairs, rows),
            "boundary": "occupancy, coherent addition, preparation and readout are supplied. "
                        "Sector-preserving dynamics cannot convert an initialized odd mode into an even mode."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
