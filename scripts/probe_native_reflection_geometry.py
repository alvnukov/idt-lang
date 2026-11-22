"""Finite reflection geometry of the flat binary flag readings, not a gauge theory.

Read each vertex using all five anonymous port germs. Give the +/- outputs
equal coordinate weight and compare their sign vectors by the ordinary dot
product (Hamming metric). Ask which chords give orthogonal reflections
that permute *every* allowed endpoint. No root-system names or particle
charges enter this search. Compare AFTERWARD with the familiar D5 root
system, the spinor weight diagram and its A4 and A2+A1 subsystems.

This is not a demonstration of infinitesimal local gauge transformations.
If one subsequently models each oriented root by one complexified root
generator, one must also choose a Cartan space. In the derived A4 span
rank four yields one neutral Abelian axis beyond A2+A1; the full rank-five
space has two such axes. Preserving a vacuum vertex in the finite symmetry
group does *not* remove a physical U(1) gauge field. No gauge fields,
spacetime, spinors in a Hilbert space, masses or propagating particles
are assigned by this computation.
"""

from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations

from scripts.probe_anonymous_folded_carrier import forced_completion
from scripts.probe_two_turn_germ_ballots import record, votes


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b, strict=True))


def rank(rows):
    basis = {}
    for row in rows:
        v = list(map(F, row))
        for i in range(len(v)):
            x = v[i]
            if x:
                if i not in basis:
                    basis[i] = [z/x for z in v]
                    break
                v = [z-x*w for z, w in zip(v, basis[i], strict=True)]
    return len(basis)


def chord(a, b):
    return tuple((x-y)//2 for x, y in zip(a, b, strict=True))


def reflecting_chords(points):
    n, where = len(points), {p: i for i, p in enumerate(points)}
    chords = {chord(a, b) for a in points for b in points if a != b}
    actions = {}
    for h in chords:
        sq = dot(h, h)
        images = []
        for p in points:
            # R_h(p) = p - 2<p,h>h/|h|², exact divisibility only.
            z = tuple(sq*x-2*dot(p, h)*y for x, y in zip(p, h, strict=True))
            if any(x % sq for x in z):
                break
            target = tuple(x//sq for x in z)
            if target not in where:
                break
            images.append(where[target])
        if len(images) == n:
            need(len(set(images)) == n, "reflection lost injectivity")
            actions[h] = tuple(images)
    return chords, actions


def generate(gens, n):
    identity = tuple(range(n))
    reached, work = {identity}, deque([identity])
    while work:
        v = work.popleft()
        for op in gens:
            out = tuple(op[i] for i in v)
            if out not in reached:
                reached.add(out)
                work.append(out)
    return reached


def probe():
    graph, r = forced_completion(), 0
    reads = record(graph, r)
    ports = tuple(reads)
    pts = tuple(tuple(1-2*reads[p][v] for p in ports) for v in range(16))
    chords, acts = reflecting_chords(pts)
    need(Counter(dot(h, h) for h in chords) == {2: 40, 4: 80}
         and set(acts) == {h for h in chords if dot(h, h) == 2},
         "not all and only D5 short chords are reflections")
    need(all((b in graph[a]) == (dot(chord(pts[a], pts[b]), chord(pts[a], pts[b])) == 4)
             for a, b in combinations(range(16), 2)), "graph hops are the longer chords")
    need(rank(acts) == 5 and all(sorted(abs(x) for x in h) == [0, 0, 0, 1, 1] for h in acts),
         "wrong roots or rank")
    group = generate(set(acts.values()), 16)
    need(len(group) == 1920 and all(all(op[v] in graph[op[u]] for u, vs in enumerate(graph)
                                        for v in vs) for op in group),
         "chord reflections changed physical adjacency")
    vacuum = {h: op for h, op in acts.items() if op[r] == r}
    need(len(vacuum) == 20 and rank(vacuum) == 4 and all(sum(h) == 0 for h in vacuum)
         and len(generate(set(vacuum.values()), 16)) == 120, "vacuum A4 span")
    for t in set(range(16))-{r}-graph[r]:
        q = tuple(votes(reads, t, v)[0] for v in range(16))
        weights = tuple(5*reads[p][t]-2 for p in ports)
        need(all(2*q[v] == -dot(weights, pts[v]) for v in range(16)), "fixed readout contrast")
        neutral = {h: op for h, op in acts.items() if all(q[op[v]] == q[v] for v in range(16))}
        need(set(neutral) == {h for h in acts if dot(h, weights) == 0} and
             set(neutral) <= set(vacuum), "root action on all readings")
        need(len(neutral) == 8 and rank(neutral) == 3, "A2+A1 roots")
        same_q = {op for op in group if all(q[op[v]] == q[v] for v in range(16))}
        need(generate(set(neutral.values()), 16) == same_q and len(same_q) == 12,
             "finite residual operations are S3 x S2")
        need(rank([*neutral, weights]) == 4 and rank([*neutral, weights, (1,)*5]) == 5,
             "lost second Abelian axis in full ambient span")
    # The graph has another symmetric reading made only of pairwise products
    # of exactly the same flags. Its actual hop now is the shorter chord. The
    # coordinate metric/observation layer is not forced by mere automorphisms.
    products = tuple(tuple(p[i]*p[j] for i, j in combinations(range(5), 2)) for p in pts)
    other, effects = reflecting_chords(products)
    need(len(set(products)) == 16 and rank(products) == 10 and
         {dot(h, h) for h in other} == {4, 6} and not effects,
         "product-coordinate reflection countercontrol")
    return len(acts), len(vacuum), len(neutral), len(group), len(effects)


if __name__ == "__main__":
    full, vacuum, neutral, group, control = probe()
    print(f"Oriented reflection chords: {full} -> {vacuum} -> {neutral}; "
          f"generated finite group {group}. Same graph, pairwise-flag reading: {control} reflection chords.")
    print("The rank-four choice has one commuting Cartan direction beyond A2+A1, the rank-five "
          "choice two. Neither an actual gauge group nor a gauge-boson spectrum is derived.")
