"""A minimal ANONYMOUS finite graph under explicit, global reconstruction axioms.

Assume simple, nonempty, triangle-free, with exactly two common neighbors
for EVERY distinct nonadjacent pair, and an odd cycle. Minimize vertex
count. No dimension, directions, regularity, distance labels, coordinates
or node count are inputs. This is a conditional combinatorial selector,
not an origin for these axioms or a derivation of particles, gauging or space.

The global common-neighbor condition already implies connectedness and
diameter <=2. Along any edge u-v, a neighbor x of u other than v is
nonadjacent to v and has exactly one other common neighbor y with v.
The reverse construction from y recovers x, so the endpoint degrees agree.
Write the common degree as k. At a root, each pair of distinct neighbors
has exactly one common vertex other than the root; conversely each vertex
at distance two touches exactly two root neighbors. Hence v=1+k+C(k,2).

The adjacency matrix obeys A^2=(k-2)I-2A+2J. On the constant-vector
complement its possible eigenvalues are -1 +/- sqrt(k-1), with integer
multiplicities f,h. Trace zero gives (f-h)*sqrt(k-1)=v-1-k. For k>1
the RHS is positive, so k-1 must be square. k=3,4 are impossible. The
bipartite cases are only a single vertex, an edge, and a four-cycle:
diameter<=2 makes a connected bipartite graph complete bipartite, then
the same-side common-neighbor rule applies. Thus here oddness is equivalent
to >4 vertices; do not silently replace the global law by the local
two-path/unique-square rule. The latter only gives v>=1+k+C(k,2).

At k=5, label the five neighbors of a temporarily chosen root. Each of the
ten distance-two vertices is now labelled by its pair of neighbors. It
needs three more neighbors; triangle-freeness allows only disjoint pairs,
of which there are exactly three. This forces every edge up to relabeling.
Existence and oddness are checked on that forced completion, not inferred
just from its feasible spectrum. Larger admissible graphs exist separately.

Decoder below receives only adjacency. It recovers five matchings from
opposite edges of observed squares, composes their operations, reconstructs
even masks up to naming and root, and verifies the whole automorphism group.
An ordered second mark at distance two supplies a 2+3 split, an adjacent
one a 1+4 split. The anonymous unmarked graph picks neither mark nor
individual labels. Its automorphisms are graph symmetries, not gauge fields.
Run: python3 -B -m scripts.probe_anonymous_folded_carrier
"""

import json
from collections import Counter, deque
from itertools import combinations, permutations
from math import comb, factorial, isqrt
from random import Random


def need(condition, reason):
    if not condition:
        raise AssertionError(reason)


def edge(u, v):
    return (u, v) if u < v else (v, u)


def graph(rows):
    return tuple(frozenset(row) for row in rows)


def distances(a, root):
    dist, todo = {root: 0}, deque([root])
    while todo:
        v = todo.popleft()
        for w in a[v]:
            if w not in dist:
                dist[w] = 1+dist[v]
                todo.append(w)
    return dist


def audit(a):
    n = len(a)
    need(n and all(v not in a[v] and all(0 <= w < n and v in a[w] for w in a[v]) for v in range(n)),
         "not a nonempty simple undirected graph")
    dist = distances(a, 0)
    need(len(dist) == n, "disconnected input")
    adj, non = Counter(), Counter()
    for i, j in combinations(range(n), 2):
        (adj if j in a[i] else non)[len(a[i] & a[j])] += 1
    return {"vertices": n, "degrees": sorted(set(map(len, a))), "edge_common_counts": dict(sorted(adj.items())),
            "nonedge_common_counts": dict(sorted(non.items())), "triangle_free": not (set(adj)-{0}),
            "every_two_path_has_unique_square": not (set(adj)-{0}) and not (set(non)-{0, 2}),
            "global_two_common": not (set(non)-{2}),
            "odd_cycle": any(dist[u]%2 == dist[v]%2 for u, vs in enumerate(a) for v in vs)}


def degree_filter(k):
    v = 1+k+comb(k, 2)
    if k <= 2:
        return k, v, "no_odd_cycle"
    r = isqrt(k-1)
    if r*r != k-1:
        return k, v, "irrational_trace_obstruction"
    delta, rem = divmod(v-1-k, r)
    if rem or (v-1+delta)%2 or delta > v-1:
        return k, v, "nonintegral_or_negative_spectral_multiplicity"
    return k, v, "passes_arithmetic_only"


def forced_completion():
    """Build the neighborhood completion justified above; separate from the decoder."""
    shell = [frozenset(), *(frozenset([x]) for x in range(5)),
             *(frozenset(p) for p in combinations(range(5), 2))]
    def linked(x, y):
        if len(x) == len(y) == 2:
            return x.isdisjoint(y)
        return len(x ^ y) == 1
    return graph({j for j, y in enumerate(shell) if linked(x, y)} for x in shell)


def relabel(a, rename):
    out = [set() for _ in a]
    for x, ys in enumerate(a):
        out[rename[x]] = {rename[y] for y in ys}
    return graph(out)


def square_directions(a):
    edges = {edge(i, j) for i, ys in enumerate(a) for j in ys}
    parent = {e: e for e in edges}
    def find(e):
        while parent[e] != e:
            parent[e] = parent[parent[e]]
            e = parent[e]
        return e
    def union(e, f):
        parent[find(e)] = find(f)
    diagonals = 0
    for i, j in combinations(range(len(a)), 2):
        if j not in a[i]:
            common = a[i] & a[j]
            need(len(common) == 2, "not a global two-common-neighbor graph")
            x, y = common
            union(edge(i, x), edge(j, y))
            union(edge(i, y), edge(j, x))
            diagonals += 1
    groups = {}
    for e in edges:
        groups.setdefault(find(e), set()).add(e)
    need(diagonals%2 == 0, "unpaired opposite diagonals")
    return diagonals//2, frozenset(frozenset(group) for group in groups.values())


def compose(f, g):
    return tuple(f[j] for j in g)


def is_automorphism(a, f):
    return sorted(f) == list(range(len(a))) and all({f[j] for j in vs} == a[f[i]] for i, vs in enumerate(a))


def decode(a, root):
    stats = audit(a)
    # Degree is inspected, not supplied. The spectral argument rules out
    # every smaller odd candidate; existence is tested by this graph itself.
    degrees = stats["degrees"]
    minimum_feasible = next((k for k in range(len(a)) if degree_filter(k)[2] == "passes_arithmetic_only"), None)
    need(stats["triangle_free"] and stats["global_two_common"] and stats["odd_cycle"] and
         degrees == [minimum_feasible], "not the minimal admissible degree")
    squares, classes = square_directions(a)
    identity = tuple(range(len(a)))
    ops = []
    for cls in classes:
        f = {}
        for u, v in cls:
            need(u not in f and v not in f, "direction is not a matching")
            f[u], f[v] = v, u
        need(len(f) == len(a), "matching misses a vertex")
        op = tuple(f[i] for i in identity)
        need(is_automorphism(a, op) and compose(op, op) == identity, "direction is not a reversible rewire")
        ops.append(op)
    ops.sort(key=lambda f: f[root])  # names chosen ONLY for comparison, not intrinsic
    k = len(ops)
    need(k == 5 and all(compose(f, g) == compose(g, f) for f, g in combinations(ops, 2)), "direction algebra")
    translations, even = set(), {}
    for bits in range(1 << k):
        f = identity
        for j, g in enumerate(ops):
            if bits >> j & 1:
                f = compose(g, f)
        need((f == identity) == (bits in (0, (1<<k)-1)), "unexpected short relation")
        translations.add(f)
        mask = bits ^ (((1<<k)-1) if bits.bit_count()%2 else 0)
        need(even.setdefault(f[root], mask) == mask, "coordinate depends on the chosen path")
    need(len(translations) == len(a) == len(even) == len(set(even.values())) and
         all(not mask.bit_count()%2 for mask in even.values()), "not regular on the even masks")
    need(all(even[f[v]] == even[v]^(((1<<k)-1)^(1<<j)) for j, f in enumerate(ops) for v in identity),
         "reconstructed direction does not flip the other four bits")
    slots = [f[root] for f in ops]
    index = {v: i for i, v in enumerate(slots)}
    pair = {v: (frozenset() if v == root else frozenset([index[v]]) if v in index else
                frozenset(index[w] for w in a[v] if w in index)) for v in identity}
    inv = {s: v for v, s in pair.items()}
    need(len(inv) == len(a) and Counter(map(len, pair.values())) == {0:1, 1:5, 2:10}, "bad rooted shells")
    stabilizer = []
    for p in permutations(range(k)):
        f = tuple(inv[frozenset(p[j] for j in pair[v])] for v in identity)
        need(is_automorphism(a, f), "neighbor permutation did not extend")
        need(all(compose(f, ops[j]) == compose(ops[p[j]], f) for j in range(k)),
             "root stabilizer does not permute the recovered translation generators")
        stabilizer.append(f)
    all_aut = {compose(t, f) for t in translations for f in stabilizer}
    # An automorphism is determined by root image and its neighbor images:
    # each remaining vertex is the unique nonroot common neighbor of a pair.
    need(len(all_aut) == len(a)*factorial(k), "automorphism count does not reach proved upper bound")
    by_shell = {}
    for v in identity:
        if v == root:
            continue
        fixed = [f for f in stabilizer if f[v] == v]
        parts = {frozenset(f[w] for f in fixed) for w in slots}
        signature = (sorted(map(len, parts)), len(fixed))
        need(by_shell.setdefault(len(pair[v]), signature) == signature, "inequivalent marks in one shell")
    need(by_shell == {1:([1, 4], 24), 2:([2, 3], 12)}, "wrong residual direction orbits")
    return classes, {"squares": squares, "direction_matching_sizes": sorted(map(len, classes)),
                     "translation_order": len(translations), "root_stabilizer_order": len(stabilizer),
                     "full_automorphism_order": len(all_aut), "marked_shell_stabilizers": by_shell}


def cube(k, fold=False):
    top = (1<<k)-1
    def canonical(x):
        return min(x, x^top) if fold else x
    vertices = sorted({canonical(i) for i in range(top+1)})
    idx = {x: i for i, x in enumerate(vertices)}
    return graph({idx[canonical(x^(1<<j))] for j in range(k)} for x in vertices)


def larger_control():
    # Pure finite witness: generate explicit six-subsets after requiring two
    # fixed bits in weight-eight binary words and excluding a third. No code
    # classification theorem or physical interpretation is needed for the audit.
    polynomial = sum(1<<j for j in (0,1,5,6,7,9,11))
    blocks = []
    for message in range(4096):
        w = 0
        for i in range(12):
            if message >> i & 1:
                w ^= polynomial << i
        w |= (w.bit_count()%2) << 23
        if w.bit_count() == 8 and w & 3 == 3 and not w & 4:
            blocks.append(w >> 3)
    need(len(set(blocks)) == len(blocks) == 56 and all(w.bit_count() == 6 for w in blocks), "large witness")
    return graph({j for j,y in enumerate(blocks) if not (x & y)} for x in blocks)


def probe():
    a = forced_completion()
    classes, report = decode(a, 0)
    for seed in (7, 41, 2026):
        rename = list(range(len(a)))
        Random(seed).shuffle(rename)
        b = relabel(a, rename)
        expected = frozenset(frozenset(edge(rename[u], rename[v]) for u, v in cls) for cls in classes)
        for anchor in (0, 1, 9):
            recovered, again = decode(b, rename[anchor])
            need(expected == recovered and report == again, "anonymous decoder depended on names/root")
    need(decode(cube(5, fold=True), 0)[1] == report, "independent folded cube construction disagrees")
    rook = graph({v for v in range(9) if u != v and (u//3 == v//3 or u%3 == v%3)} for u in range(9))
    controls = {"ordinary_5_cube": audit(cube(5)), "folded_7_cube": audit(cube(7, True)),
                "triangle_rich_three_by_three_rook": audit(rook),
                "larger_disjoint_sixsets": audit(larger_control())}
    for label, odd in (("ordinary_5_cube", False), ("folded_7_cube", True)):
        r = controls[label]
        need(r["every_two_path_has_unique_square"] and not r["global_two_common"] and r["odd_cycle"] == odd,
             "local and global laws conflated")
    big = controls["larger_disjoint_sixsets"]
    need(big["triangle_free"] and big["global_two_common"] and big["odd_cycle"] and big["degrees"] == [10],
         "minimum-size assumption lost its countercontrol")
    need(not controls["triangle_rich_three_by_three_rook"]["triangle_free"] and
         controls["triangle_rich_three_by_three_rook"]["global_two_common"], "triangle exclusion control")
    return {"scope": "anonymous graph under explicit global axioms and size minimization; no physical derivation",
            "degree_filter": [degree_filter(k) for k in range(6)], "minimal_graph": audit(a),
            "reconstruction": report, "renaming_root_checks": 9, "controls": controls}


if __name__ == "__main__":
    print(json.dumps(probe(), separators=(",", ":")))
