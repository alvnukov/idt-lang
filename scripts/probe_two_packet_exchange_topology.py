"""Exact exchange-loop order on the anonymously completed sixteen-site carrier.

Two indistinguishable occupations hop on reciprocal bonds. Initially prohibit
coincidence, identify the two orderings of a move on each of TWO DISJOINT
bonds, and add closed route records commutatively. These are extra hypotheses;
in particular the word 'hard-core' already assumes an occupancy restriction.
No state vector, Pauli sign, distribution or chemistry is used to build the
integer presentation. Compare no order identifications, ordinary squares
that bound actual faces even for one moving packet, and permitted coincidence.

Independent mathematical comparator: Harrison, Keating, Robbins & Sawicki,
Commun. Math. Phys. 330 (2014), https://doi.org/10.1007/s00220-014-2091-0,
arXiv:1304.5781. Their topological scalar phase classification assumes
collision-free unordered configurations and a U(1) character of H1; it
does not force matter to occupy a fermionic sector. We calculate this
particular finite complex, not the general n-particle classification.
"""

from __future__ import annotations

from collections import Counter, deque
from itertools import combinations, combinations_with_replacement, pairwise

from scripts.probe_abelian_reunion_dimensions import smith
from scripts.probe_anonymous_folded_carrier import forced_completion


def need(test, why):
    if not test:
        raise ArithmeticError(why)


def pair(a, b):
    return (a, b) if a <= b else (b, a)


def boundary(word, chords):
    result = Counter()
    for a, b in pairwise((*word, word[0])):
        if a != b and (e := pair(a, b)) in chords:
            result[chords[e]] += 1 if a < b else -1
    return {j: value for j, value in result.items() if value}


def config(graph, *, collide=False):
    """A tree gauge: only fundamental chords carry independent loop records."""
    n = len(graph)
    verts = tuple((combinations_with_replacement if collide else combinations)(range(n), 2))
    bonds = tuple((a, b) for a in range(n) for b in sorted(graph[a]) if a < b)
    adjacency = {x: set() for x in verts}
    for a, b in bonds:
        for spectator in range(n):
            if collide or spectator not in (a, b):
                s, t = pair(a, spectator), pair(b, spectator)
                adjacency[s].add(t)
                adjacency[t].add(s)
    edges = {pair(s, t) for s in verts for t in adjacency[s]}
    root = verts[0]
    seen, tree, todo = {root}, set(), deque([root])
    while todo:
        s = todo.popleft()
        for t in sorted(adjacency[s]-seen):
            tree.add(pair(s, t))
            seen.add(t)
            todo.append(t)
    need(seen == set(verts) and len(tree) == len(verts)-1, "disconnected configuration graph")
    chords = {e: i for i, e in enumerate(sorted(edges-tree))}
    faces = []
    for (a, b), (c, d) in combinations(bonds, 2):
        if not collide and len({a, b, c, d}) != 4:
            continue
        square = (pair(a, c), pair(b, c), pair(b, d), pair(a, d))
        need(all(t in adjacency[s] for s, t in pairwise((*square, square[0]))), "bad order square")
        faces.append(boundary(square, chords))
    return bonds, verts, chords, faces


def gf2_rank(rows):
    basis = {}
    for row in rows:
        v = sum(1 << j for j, x in row.items() if x % 2)
        while v:
            j = v.bit_length()-1
            if j not in basis:
                basis[j] = v
                break
            v ^= basis[j]
    return len(basis)


def group(rows, width):
    """Integer unit-pivot substitutions followed by exact residual Smith.

    With coefficient ±1 a relator expresses its generator as an integral
    combination of the others: it and that generator may be deleted after
    substitution. Independent bit arithmetic checks the entire mod-two rank.
    """
    working = [dict(r) for r in rows if r]
    eliminated = 0
    while True:
        pivot = min(((len(r), i) for i, r in enumerate(working)
                     if any(abs(a) == 1 for a in r.values())), default=None)
        if pivot is None:
            break
        i = pivot[1]
        r = working.pop(i)
        j = min(j for j, a in r.items() if abs(a) == 1)
        sign = r.pop(j)
        for s in working:
            q = s.pop(j, 0)*sign
            if q:
                for k, a in r.items():
                    value = s.get(k, 0)-q*a
                    if value:
                        s[k] = value
                    else:
                        s.pop(k, None)
        eliminated += 1
    columns = sorted({j for r in working for j in r})
    small = [tuple(r.get(j, 0) for j in columns) for r in working if r]
    tail = smith(small, len(columns))
    free = width-eliminated-len(tail)
    torsion = tuple(v for v in tail if v != 1)
    need(width-gf2_rank(rows) == free+sum(v % 2 == 0 for v in torsion), "binary check of presentation")
    return free, torsion


def outcome(graph, *, collide=False, fill=False):
    bonds, verts, chords, rows = config(graph, collide=collide)
    width, slots = len(chords), len(rows)
    if fill:
        # Only fill actual induced base squares, with the other packet
        # held outside every vertex of that face, never hopping across it.
        n = len(graph)
        for a, c in combinations(range(n), 2):
            if c in graph[a]:
                continue
            for b, d in combinations(sorted(graph[a] & graph[c]), 2):
                if min(a, c) > min(b, d) or d in graph[b]:
                    continue
                for spectator in set(range(n))-{a, b, c, d}:
                    rows.append(boundary(tuple(pair(v, spectator) for v in (a, b, c, d)), chords))
    center = next(v for v in range(len(graph)) if len(graph[v]) >= 3)
    a, b, c = sorted(graph[center])[:3]
    # A goes a->center->c, B goes b->center->a, A returns c->center->b.
    # Ends unordered as it began. Net traversals of every base bond are zero.
    path = ((a, b), (center, b), (c, b), (c, center), (c, a), (center, a))
    y = boundary(tuple(pair(*x) for x in path), chords)
    need(y, "selected Y exchange has no cycle")
    base = group(rows, width)
    kill = group([*rows, y], width)
    twice = group([*rows, {j: 2*v for j, v in y.items()}], width)
    # A quotient of a finitely generated Abelian group by one nonzero
    # element cannot retain both rank and torsion cardinality.
    kind = ("trivial" if kill == base else "order_two" if twice == base else
            "infinite" if kill[0] == base[0]-1 else "other_finite")
    return {"vertices":len(verts), "bonds":len(bonds), "free_before_square_relations":width,
            "commuting_squares":slots, "extra_single_packet_squares":len(rows)-slots,
            "homology":base, "kill_exchange":kill, "kill_double_exchange":twice, "exchange":kind}


def graph(n, edges):
    g = [set() for _ in range(n)]
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    return g


def probe():
    folded = forced_completion()
    ytree = graph(4, ((0, i) for i in range(1, 4)))
    k4 = graph(4, combinations(range(4), 2))
    k33 = graph(6, ((i, j) for i in range(3) for j in range(3, 6)))
    got = {"folded":outcome(folded), "filled":outcome(folded, fill=True),
           "coincidence_allowed":outcome(folded, collide=True), "tree":outcome(ytree),
           "planar_K4":outcome(k4), "nonplanar_K33":outcome(k33)}
    desired = {"folded":(25,(2,),"order_two"), "filled":(0,(2,2),"order_two"),
               "coincidence_allowed":(25,(),"trivial"), "tree":(1,(),"infinite"),
               "planar_K4":(4,(),"infinite"), "nonplanar_K33":(4,(2,),"order_two")}
    for name, r in got.items():
        need((*r["homology"], r["exchange"]) == desired[name], name)
    need((got["folded"]["vertices"],got["folded"]["free_before_square_relations"],
          got["folded"]["commuting_squares"],got["filled"]["extra_single_packet_squares"])
         == (120,441,620,480), "cell census")
    return got


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), sort_keys=True))
