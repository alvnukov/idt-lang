"""A spectral vertex contrast is not a conserved charge of the same motion.

Start from the response to a marked point on the anonymous graph, not from
assigned hypercharges. Freeze an ordered two-step frame. Test whether its
readout is unchanged along primitive graph moves, and classify the minimum
length-two routes with equal endpoint values. Equality is a test imposed on
paths; removing unequal paths is not a mechanism. The vacuum vertex can be
clamped while measuring a mode or available to a different transport probe:
we keep both virtual-path conventions explicit.

For any connected graph, [A,diag(q)]_uv=A_uv(q_v-q_u); a commuting real
diagonal observable must be constant. By contrast the rank-one *mode*
operator q q^T commutes for an eigenvector q but has only two eigenvalues.
Neither statement compares an actual gauge charge to measured interactions.
Hypercharge, electric charge and a signed response of a medium are not synonyms.

An optional integer store compensates every hop by q(u)-q(v). On a single
fixed-total correlated sector six charge levels suffice and are necessary
if all vertices remain reachable. The increments telescope on every loop:
this gadget just records an endpoint potential. A finite independent store
with a freely chosen initial level cannot allow every directed hop at every
level and preserve this absolute total (use an extremal initial level).
No physical reservoir, gauge field or coupling is derived.
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations

from scripts.probe_anonymous_folded_carrier import forced_completion
from scripts.probe_rooted_parity_walk import basis, poly40


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


def degrees(edges, vertices):
    return sorted(sum(v in e for e in edges) for v in vertices)


def connected(vertices, edges):
    reached = {next(iter(vertices))}
    while True:
        more = reached | {v for e in edges if reached.intersection(e) for v in e}
        if reached == more:
            return reached == vertices
        reached = more


def audit(g, root, mark):
    out = poly40(g, root, basis(len(g), mark))
    need(all(y % 2 == 0 for y in out), "unexpected spectral normalization")
    q = tuple(y//2 for y in out)
    edge = [(u, v) for u, nbs in enumerate(g) for v in nbs if u < v]
    delta = Counter(abs(q[u]-q[v]) for u, v in edge)
    first = [(u, v) for u, v in edge if q[u] == q[v]]
    charges = {k: {v for v in range(16) if q[v] == k} for k in set(q)}
    need(delta == {0: 6, 1: 6, 2: 3, 3: 2, 4: 6, 5: 6, 6: 6, 9: 2, 10: 3},
         "raw edge contrast census")
    need(all(q[u] == 1 for u, _ in first) and connected(charges[1], first)
         and degrees(first, charges[1]) == [2]*6, "only one same-label six-cycle")
    norm = sum(x*x for x in q)
    need(norm == 120 and 2*sum(d*d*n for d, n in delta.items()) == 1920,
         "diagonal observable commutator norm")
    aq = [sum(q[v] for v in nbs) for nbs in g]
    need(aq == [-3*x for x in q], "including the unclamped vacuum row")
    need(all(aq[u]*q[v] == q[u]*aq[v] for u in range(16) for v in range(16)),
         "rank-one mode observable does not commute")

    # Two actual routes have the same endpoints, counted as two EACH TIME;
    # the path is not interchangeable with a transposition of two particles.
    accepted = {}
    off_resonant = {False: defaultdict(Counter), True: defaultdict(Counter)}
    for value, vs in charges.items():
        accept = []
        for u, v in combinations(sorted(vs), 2):
            mid = g[u] & g[v]
            if v in g[u]:
                need(not mid, "graph has a triangle")
                continue
            need(len(mid) == 2, "missing equal-endpoint alternative")
            accept.append((u, v))
            for pinned in (False, True):
                # Illustrative second-order amplitude for a SUPPLIED linear
                # generator H0=diag(q), V=A. Intermediate nodes within the
                # degenerate subspace are *not* divided by zero. This number
                # is not the complete unitary/time evolution or a gauge action.
                h = sum((F(1, value-q[m]) for m in mid
                         if q[m] != value and (not pinned or m != root)), F(0))
                off_resonant[pinned][value][h] += 1
        accepted[value] = accept
    need({k: len(v) for k, v in accepted.items()} == {-4: 3, -3: 1, 0: 0, 1: 9, 2: 3, 6: 0},
         "length-two neutral paths")
    # Connected cubic on six vertices could also be K3,3: actually check
    # the two disjoint triangles and the matching between them.
    edges = set(accepted[1])
    triangles = [set(tri) for tri in combinations(sorted(charges[1]), 3)
                 if all(e in edges for e in combinations(tri, 2))]
    need(len(triangles) == 2 and not (triangles[0] & triangles[1])
         and degrees(edges, charges[1]) == [3]*6 and connected(charges[1], edges),
         "six-vertex neutral two-step graph is not the triangular prism")
    need(off_resonant[False][1] == {F(1, 4): 6, F(-4, 5): 3}
         and off_resonant[False][-4] == {F(-4, 15): 3}
         and off_resonant[False][2] == {F(2, 3): 3}
         and off_resonant[False][-3] == {F(-4, 9): 1},
         "models with different intermediate gaps must not be merged")
    # For a pinned root, two -3 neighbors share a path through the root,
    # and so do any two of the three +2 neighbors. Other sector pairs do not.
    need(off_resonant[True][-3] == {F(-1, 9): 1}
         and off_resonant[True][2] == {F(1, 6): 3}
         and all(off_resonant[True][k] == off_resonant[False][k] for k in (-4, 1)),
         "forgot whether original emitter/absorber remains available")

    level = {v: q[root]-q[v] for v in range(16)}
    need(len(set(level.values())) == 6, "fixed-total store size")
    high = max(level.values())
    boundary = 0
    for u in range(16):
        for v in g[u]:
            increment = q[u]-q[v]
            need(level[u]+increment == level[v] and level[v]-increment == level[u],
                 "correlated conserving store")
            boundary += high+increment > high
            for w in g[v]:
                need(increment+q[v]-q[w] == q[u]-q[w], "endpoint potential")
    need(boundary == 34, "independently prepared top level blocks upward transfers")
    return delta


def probe():
    g = forced_completion()
    tested = 0
    for r in range(len(g)):
        for t in range(len(g)):
            if r != t and t not in g[r]:
                audit(g, r, t)
                tested += 1
    need(tested == 160, "lost ordered frame")
    return tested


if __name__ == "__main__":
    print(f"{probe()} frames: 34 of 40 hops change the signed value; the other six form one cycle.")
    print("Equal-endpoint two-hop graphs: two singlets, one pair, two triangles, one triangular prism.")
    print("A six-level correlated store compensates every hop, but is only an endpoint register. "
          "Neither the mode nor postselecting equal labels establishes charge conservation.")
