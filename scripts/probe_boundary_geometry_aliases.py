"""What does the unsigned triangle's registered contact readout identify?

For a connected bipartite tagged packet choose a temporary root and let v_t
be the difference of its even and odd occurrence counts on tag t. The root
only names a sign. The frozen two-sheet contact, Cartesian product and
ordered-pair detector of probe_bipartite_triangle_origin factor through v:
the contact gives v +/- Pv since corresponding vertices in its two sheets
have equal/opposite parity; path parities in the product add mod 2, giving
v outer w. A tag relabeling permutes entries, and each terminal rail counts
v_t^2. These facts follow from the graph wirings, not a requirement that
every possible graph operation be a function of v. By induction ANY finite
circuit built from these operations, fresh fixed references and repeated
copies preserves equality of input boundaries in all raw terminal cells,
even null branches. Registered-flag feed-forward preserves it by cases.
Consequently defined normalized readings agree. No ancestry, bare occurrence
count, intermediate adjacency, or time is itself a registered stock output.

For each n>=1 take the path with tags A,C^(2n),B. Attach n disjoint all-C
squares, each by a bridge from the first C to one corner. Root at unique
A. Odd subdivision keeps B odd and adds n cancelling pairs on C; each square
has two vertices of each parity. All boundaries are EXACTLY (+1,-1,0).
The cycle rank is n (each attached square adds four vertices and five edges).
Thus even their cycle structures differ, not merely their presentations as
subdivided intervals. Both endpoint tags are unique, both endpoints are
degree one; no extra marks, coordinates or vertex numbers name the stations.
With a SUPPLIED one-edge-per-tick propagation and immediate, distinguishable
reply at B the first echo at A is 2(2n+1). The squares offer no shortcut.
This timing experiment is NOT one of the frozen stock circuits.

What can the latter reconstruct? For repeated copies of a single nonzero
real neutral triple v=(a,b,-a-b), common rail calibration and N=sum v_i^2,
the (+) branch fixing i has squared mass 6 v_i^2, out of 4N. Two registered
settings give A=2p0/3=a^2/N, B=2p1/3=b^2/N, C=1/2-A-B=ab/N.
A nonzero row of [[A,C],[C,B]] determines [a:b], including the a=0 case.
The scale, overall sign, input graph and detector histories are not recovered.
This is exact noiseless real-ray identification under the quadratic population
law, not tomography of arbitrary complex or mixed preparations. Reference
alignment and repeated preparation matter. Independent coherent addition
of a fixed-scale reference is not a homogeneous probe of the unknown ray.

The induction and infinite family above are mathematical arguments, not Lean
proofs. The finite checks below use the unsigned graph devices directly.
No physical clock, signal speed, dimension, or 3D embedding is derived.
Run: python3 -B -O -m scripts.probe_boundary_geometry_aliases
"""

from fractions import Fraction as F
from itertools import pairwise, product

from scripts.probe_bipartite_triangle_origin import (
    D, edges, graph, independent, mass, need, path_parity, reflection, rename,
    seed, split, stock,
)


def corridor(n, squares, spur=False):
    """Indices here generate edges; the clock and terminal detectors never use them."""
    need(n >= 1 and squares >= 0, "bad family parameters")
    tags = [0, *([2] * (2*n)), 1]
    links = list(pairwise(range(len(tags))))
    for _ in range(squares):
        i = len(tags)
        tags.extend([2]*4)
        links.extend(((1,i), (i,i+1), (i+1,i+2), (i+2,i+3), (i+3,i)))
    if spur:
        i = len(tags)
        tags.extend((2,2))
        links.extend(((1,i), (i,i+1)))
    return graph(tags, links)


def terminal(g, tag):
    found = [i for i, t in enumerate(g.tags) if t == tag]
    need(len(found) == 1 and len(g.adj[found[0]]) == 1, "terminal not intrinsic")
    return found[0]


def boundary(g, root):
    parity = path_parity(g, root)
    return tuple(sum((-1)**parity[i] for i, t in enumerate(g.tags) if t == k) for k in D)


def first_echo(g):
    """Broadcast one hop/tick; the unique B answers the first request once."""
    a, b = terminal(g, 0), terminal(g, 1)
    request, reply, arrival = {a}, set(), None
    for tick in range(1, 2*len(g.tags)+1):
        request = {v for u in request for v in g.adj[u]}
        reply = {v for u in reply for v in g.adj[u]}
        if arrival is None and b in request:
            arrival = tick
            reply.add(b)
        if a in reply:
            return arrival, tick
    raise AssertionError("connected stations had no echo")


def signature(g):
    """Full per-rail counts, not normalized at intermediate nodes."""
    rows = []
    def record(packet, rails):
        s = stock(packet)
        rows.append(tuple(s.get(t, 0) for t in rails))
    record(g, D)
    for k in D:
        for flag, p in enumerate(split(g, lambda t: reflection(k,t))):
            record(p, D)
            # Setting depends on the registered flag, not on hidden topology.
            for h in split(p, lambda t: reflection((k+flag+1) % 3,t)):
                record(h, D)
    refs = independent(g, seed(1))
    joint_rails = tuple(product(D, repeat=2))
    for h in split(refs, lambda t: (t[1], t[0])):
        record(h, joint_rails)
        for left in split(h, lambda t: (reflection(0,t[0]),t[1])):
            for right in split(left, lambda t: (t[0],reflection(1,t[1]))):
                record(right, joint_rails)
    return tuple(rows)


def graph_controls():
    baseline = signature(corridor(1,0))
    echoes = []
    for n in range(1, 6):
        g = corridor(n,n)
        order = tuple(reversed(range(len(g.tags))))
        for h in (g, rename(g, order)):
            need(boundary(h, terminal(h,0)) == (1,-1,0)
                 and boundary(h, terminal(h,1)) == (-1,1,0), "endpoint-root boundary")
            need(len(edges(h)) - len(h.tags) + 1 == n, "cycle rank")
            need(first_echo(h) == (2*n+1, 4*n+2), "first passage or first echo")
            need(signature(h) == baseline, "stock circuit detected topology")
        echoes.append(first_echo(g)[1])
    # Even with matched per-tag occurrence totals, V, E, and cycle rank, an
    # extra neutral pair on the corridor is different from the same pair off it.
    short, long = corridor(1,1,spur=True), corridor(2,1)
    need(sorted(short.tags) == sorted(long.tags) and len(edges(short)) == len(edges(long))
         and signature(short) == signature(long), "matched-size comparison")
    t_short, t_long = first_echo(short)[1], first_echo(long)[1]
    need((t_short, t_long) == (6,10), "placement of neutral pair")
    # Equal distances need not imply equal topology; coarse timing or an
    # uncalibrated propagation time per link can also erase the timing split.
    need(first_echo(corridor(2,0)) == first_echo(long), "extra cycles off the route")
    need(t_short//12 == t_long//12 and 5*t_short == 3*t_long,
         "coarse clock or confounded link delay")
    return echoes, len(baseline)


def prepare(v):
    """An unsigned connected path realizing v; this is a supplied preparation."""
    plus = [i for i,x in enumerate(v) for _ in range(x)]
    minus = [i for i,x in enumerate(v) for _ in range(-x)]
    tags = tuple(t for pair in zip(plus,minus,strict=True) for t in pair)
    need(tags, "zero stock has no normalized readout")
    return graph(tags, pairwise(range(len(tags))))


def reads(v):
    g = prepare(v)
    need(boundary(g,0) == v, "raw preparation")
    values = []
    for k in (0,1):
        up, down = (mass(out) for out in split(g, lambda t: reflection(k,t)))
        values.append(F(up, up+down))
    return tuple(values)


def recover(p, q):
    a, b = 2*p/3, 2*q/3
    c = F(1,2) - a - b
    if min(a,b) < 0 or a*b != c*c:
        return None
    x,y = (a,c) if a else (c,b)
    return x,y,-x-y


def ray(v):
    norm = next(x for x in v if x)
    return tuple(F(x)/norm for x in v)


def tomography_controls():
    count = 0
    for a,b in product(range(-6,7), repeat=2):
        if a == b == 0:
            continue
        v = (a,b,-a-b)
        p,q = reads(v)
        need(ray(recover(p,q)) == ray(v), "two-setting pure-ray reconstruction")
        count += 1
    v, permuted = (1,-1,0), (1,0,-1)
    p, q = reads(v)
    need(reads(permuted)[0] == p and reads(permuted)[1] != q, "one-setting ambiguity")
    twice = tuple(2*x for x in v)
    ref = (0,1,-1)
    add = lambda a,b: tuple(x+y for x,y in zip(a,b))
    need(reads(v) == reads(twice) and
         (reads(add(v,ref))[0], reads(add(twice,ref))[0]) == (F(3,4),1),
         "coherent fixed reference breaks scale homogeneity")
    # Setting 0 on one median, setting 1 on a different median: the
    # two valid numbers 1,1 cannot belong to one neutral pure ray.
    need(reads((2,-1,-1))[0] == reads((-1,2,-1))[1] == 1 and recover(F(1),F(1)) is None,
         "repetitions must refer to the same source and frame")
    def orbit_mean(w):
        pairs = [reads(w[i:] + w[:i]) for i in D]
        return tuple(sum(z)/3 for z in zip(*pairs))
    avg = orbit_mean(v)
    need(avg == orbit_mean((2,-1,-1)) == (F(1,2),F(1,2)) and recover(*avg) is None,
         "a drifting frame or mixture is not a single ray")
    return count


def main():
    echoes, cells = graph_controls()
    count = tomography_controls()
    print(f"One exact boundary (+1,-1,0); 1..5 independent cycles, {cells} identical raw"
          f" branch/rail tables on every tested graph; first echo ticks {echoes}.")
    print("Matched vertex, tag and edge counts: 6 vs 10 ticks. Same 10 ticks with different"
          " cycle rank. A calibrated clock and labelled reply are extra operational resources.")
    print(f"Two squared-stock contacts recover the pure boundary ray on {count} nonzero"
          " test preparations, not scale, graph or mixture composition.")


if __name__ == "__main__":
    main()
