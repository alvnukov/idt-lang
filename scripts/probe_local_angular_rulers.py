"""One conditional *active* angular ruler, distinct from passive pulse sampling.

At even-role stations request all distinct two-link receivers, excluding self;
for each pair ask whether they can reach each other in two links. Stable
reciprocal station IDs, complete discovery, controllable and noiseless queries,
the least retrace/abc=cba endpoint equality, and persistent records are inputs.
We do not derive those abilities from opposition or convert a query into a
number of elementary random trials. The generator's word keys are private to
the simulator. The reader is handed opaque names and just the two operations.

Choose the smoothest nonconstant *linear* angular modes on the unweighted
regular neighbor graph, with the usual Euclidean norm on real functions on
its vertices. This metric prescription and the unit neighbor length are
supplied. Its rank, pairwise inner products, affine overlap compatibility,
and continuation forecasts are checked outputs, not an assumed dimension.
No Euclidean embedding of the simulator is used by the chart reader.

Post hoc explanation on the least unwrapped quotient: label a neighbor by
its ordered pair i,j. Two such pairs are adjacent if they share their
first or their second index. For any zero-sum z, the function z_i-z_j
has adjacency eigenvalue p-2: each third index k contributes
(z_i-z_k)+(z_k-z_j). These contrast functions form a (p-1)-dimensional
space; the measured spectrum checks they exhaust the chosen eigenspace
for p=4 and 5. It is the relation on port histories, not a supplied 3D
chart, doing the dimension-specific work. It does not select four ports.
"""

from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import prod


def need(test, why):
    if not test:
        raise ValueError(why)


class World:
    """Two port traversals per move; no geometry or distance in the oracle."""

    def __init__(self, ports, salt, mod=0, tree=False):
        self.ports, self.salt, self.mod, self.tree = ports, salt, mod, tree
        self.keys = {}
        self.cached = {}
        self.queries = 0
        self.origin = self.tag(() if tree else (0,) * ports)

    def tag(self, key):
        name = sha256(f"{self.salt}:{key}".encode()).hexdigest()[:24]
        need(self.keys.setdefault(name, key) == key, "ID collision")
        return name

    def step(self, source, i, j):
        key = list(self.keys[source])
        if self.tree:
            for p in (i, j):
                if key and key[-1] == p:
                    key.pop()
                else:
                    key.append(p)
        else:
            key[i] += 1
            key[j] -= 1
            if self.mod:
                key = [v % self.mod for v in key]
        return self.tag(tuple(key))

    def neighbors(self, tag):
        if tag not in self.cached:
            self.cached[tag] = frozenset(
                self.step(tag, i, j)
                for i in range(self.ports)
                for j in range(self.ports)
                if i != j
            ) - {tag}
        return self.cached[tag]

    def adjacent(self, a, b):
        self.queries += 1
        return b in self.neighbors(a)


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def mv(m, x):
    return tuple(dot(row, x) for row in m)


def mm(a, b):
    cols = list(zip(*b, strict=True))
    return [[dot(row, col) for col in cols] for row in a]


def minus(x, y):
    return tuple(a - b for a, b in zip(x, y, strict=True))


def plus(x, y):
    return tuple(a + b for a, b in zip(x, y, strict=True))


def inverse(a):
    n = len(a)
    rows = [[F(x) for x in r] + i for r, i in zip(a, eye(n), strict=True)]
    for j in range(n):
        k = next(k for k in range(j, n) if rows[k][j])
        rows[j], rows[k] = rows[k], rows[j]
        factor = rows[j][j]
        rows[j] = [x / factor for x in rows[j]]
        for k in range(n):
            if k != j:
                factor = rows[k][j]
                rows[k] = [
                    x - factor * y for x, y in zip(rows[k], rows[j], strict=True)
                ]
    return [r[n:] for r in rows]


def independent(vectors):
    """Return original row indices; no requested dimension or tolerance."""
    basis, picked = [], []
    for i, v in enumerate(vectors):
        row = [F(x) for x in v]
        for j, r in basis:
            row = [x - row[j] * y for x, y in zip(row, r, strict=True)]
        j = next((j for j, x in enumerate(row) if x), None)
        if j is not None:
            basis.append((j, [x / row[j] for x in row]))
            picked.append(i)
    return picked


def components(edges):
    rest, sizes = set(range(len(edges))), []
    while rest:
        queue = [rest.pop()]
        size = 0
        while queue:
            i = queue.pop()
            size += 1
            new = rest.intersection(edges[i])
            rest.difference_update(new)
            queue.extend(new)
        sizes.append(size)
    return sorted(sizes)


def shell_graph(station, neighbors, adjacent):
    names = sorted(neighbors(station))
    edges = [[] for _ in names]
    for i, j in combinations(range(len(names)), 2):
        if adjacent(names[i], names[j]):
            edges[i].append(j)
            edges[j].append(i)
    return names, edges


def act(edges, m):
    return [[sum(m[k][j] for k in row) for j in range(len(m))] for row in edges]


def spectrum(edges):
    """Characteristic polynomial by traces, then certify ALL roots on these fixtures.

    This compact checker abstains if the integral roots do not exhaust the
    polynomial; it never rounds a nonintegral eigenvalue to an integer.
    """
    n = len(edges)
    a, tr, coeffs = eye(n), [n], [1]
    for k in range(1, n + 1):
        a = act(edges, a)
        tr.append(sum(a[i][i] for i in range(n)))
        v = -sum(coeffs[k - j] * tr[j] for j in range(1, k + 1))
        need(v % k == 0, "Newton trace identity")
        coeffs.append(v // k)
    degree = max(map(len, edges))
    roots = []
    for r in range(-degree, degree + 1):
        while len(coeffs) > 1:
            q = [coeffs[0]]
            for c in coeffs[1:]:
                q.append(c + r * q[-1])
            if q[-1]:
                break
            roots.append(r)
            coeffs = q[:-1]
    need(coeffs == [1] and len(roots) == n, "unresolved nonintegral spectrum")
    return Counter(roots)


def chart(station, neighbors, adjacent):
    names, edges = shell_graph(station, neighbors, adjacent)
    need(
        len(components(edges)) == 1 and len(set(map(len, edges))) == 1,
        "need a connected regular angular graph",
    )
    spec = spectrum(edges)
    ordered = sorted(spec, reverse=True)
    top, mode = ordered[:2]
    need(spec[top] == 1 and top == len(edges[0]), "unique constant top mode")
    n, a = len(names), eye(len(names))
    for r in ordered:
        if r != mode:
            am = act(edges, a)
            a = [
                [v - r * w for v, w in zip(ar, br, strict=True)]
                for ar, br in zip(am, a, strict=True)
            ]
    scale = prod(mode - r for r in ordered if r != mode)
    need(sum(a[i][i] for i in range(n)) == scale * spec[mode], "projector trace")
    need(a[0][0] and all(a[i][i] == a[0][0] for i in range(n)), "no common local rod")
    g = [[F(v, a[0][0]) for v in row] for row in a]
    ix = independent(g)
    need(len(ix) == spec[mode], "projector rank")
    h = [[g[i][j] for j in ix] for i in ix]
    hi = inverse(h)
    pts = {
        name: mv(hi, [row[j] for j in ix]) for name, row in zip(names, g, strict=True)
    }
    pts[station] = (F(0),) * len(ix)
    # Verify every Gram entry, not just the chosen basis.
    need(
        all(
            dot(pts[x], mv(h, pts[y])) == g[i][j]
            for i, x in enumerate(names)
            for j, y in enumerate(names)
        ),
        "local factorization",
    )
    return pts, h, spec


def align(previous, local, local_metric, common_metric):
    """Affine isometry from coincident station IDs in the two closed stars."""
    shared = sorted(previous.keys() & local.keys())
    origin = shared[0]
    dx = [minus(local[t], local[origin]) for t in shared]
    dy = [minus(previous[t], previous[origin]) for t in shared]
    chosen = independent(dx)
    dim = len(local_metric)
    need(len(chosen) == dim, "overlap cannot fix the frame")
    src = list(zip(*(dx[i] for i in chosen), strict=True))
    dst = list(zip(*(dy[i] for i in chosen), strict=True))
    m = mm(dst, inverse(src))
    need(
        mm(mm(list(zip(*m, strict=True)), common_metric), m) == local_metric,
        "rulers disagree",
    )
    mapped = {
        s: plus(previous[origin], mv(m, minus(v, local[origin])))
        for s, v in local.items()
    }
    need(all(mapped[t] == previous[t] for t in shared), "overlap IDs disagree")
    return mapped, len(shared) - 1 - dim


def local_patch(world):
    root = world.origin
    pts, h, spec = chart(root, world.neighbors, world.adjacent)
    center_queries = world.queries
    atlas = dict(pts)
    rechecked = set()
    for tag in sorted(world.neighbors(root)):
        local, metric, _ = chart(tag, world.neighbors, world.adjacent)
        mapped, extra = align(pts, local, metric, h)
        need(extra > 0, "check points unused in the transition")
        for s, v in mapped.items():
            # Each alignment saw ONLY the root star. A second sighting of
            # an outer tag tests its position without using it to fit frames.
            if s in atlas and s not in pts:
                rechecked.add(s)
            need(atlas.setdefault(s, v) == v, "path-dependent patch")
    need(len(set(atlas.values())) == len(atlas), "collapsed distinct patch tags")
    need(rechecked, "no independently placed outer tag")
    return pts, h, spec, center_queries, atlas, len(rechecked)


def squared(x, y, h):
    d = minus(x, y)
    return dot(d, mv(h, d))


def motion_and_radar(w, pts, h, atlas):
    # Only the simulator chooses ground-truth paths. A charted orbit predicts
    # a unique tag from two fixes before either next observation is revealed.
    root = w.origin
    one = w.step(root, 0, 1)
    expected = plus(pts[one], minus(pts[one], pts[root]))
    possible = [tag for tag, v in atlas.items() if v == expected]
    need(len(possible) == 1 and possible[0] not in pts, "held-out extrapolation")
    straight, turn = w.step(one, 0, 1), w.step(one, 0, 2)
    need(possible == [straight] and turn not in pts and turn != straight, "two futures")
    miss = squared(atlas[turn], expected, h)
    # An independently measured two-link-per-step clock on a four-station
    # rectangle: opposite differences are NOT single-step reachable.
    u, v = one, w.step(root, 2, 3)
    uv = w.step(u, 2, 3)
    square = (root, u, uv, v)
    need(
        all(w.adjacent(s, t) for s, t in zip(square, (*square[1:], root), strict=True)),
        "clock sides",
    )
    need(not w.adjacent(root, uv) and not w.adjacent(u, v), "clock diagonals")
    need(
        squared(pts[root], atlas[uv], h) == squared(pts[u], pts[v], h) == 2,
        "angular squared diagonals",
    )
    return miss


def wrap_control(modulus):
    cover = World(4, "cover witness")
    w = World(4, "wrap witness", modulus)
    # Explicit isomorphism on root plus shell, not just equal spectra.
    words = [(i, j) for i in range(4) for j in range(4)]
    pairs = {(cover.step(cover.origin, i, j), w.step(w.origin, i, j)) for i, j in words}
    need(
        len(pairs) == len({a for a, _ in pairs}) == len({b for _, b in pairs}) == 13,
        "local bijection",
    )
    need(
        all(
            cover.adjacent(a, c) == w.adjacent(b, d)
            for (a, b), (c, d) in combinations(pairs, 2)
        ),
        "wrap distinguishable locally",
    )
    old, h, _ = chart(w.origin, w.neighbors, w.adjacent)
    first = min(w.neighbors(w.origin))
    direction = minus(old[first], old[w.origin])
    source, step = w.origin, first
    for tick in range(1, modulus + 1):
        local, metric, _ = chart(step, w.neighbors, w.adjacent)
        # Carry the latest chart only. Forcing a globally single-valued atlas
        # before testing the seam would assume away the very obstruction.
        old, _ = align(old, local, metric, h)
        target = plus(old[step], direction)
        nxt = [s for s, x in old.items() if x == target]
        need(len(nxt) == 1 and source != nxt[0], "unique straight continuation")
        source, step = step, nxt[0]
        need((source == w.origin) == (tick == modulus), "periodic first return")
    norm2 = squared(old[w.origin], (F(0),) * len(h), h)
    need(
        norm2 == modulus**2 and old[w.origin] == tuple(modulus * x for x in direction),
        "translation after closed route",
    )
    return norm2


def main():
    for ports in (4, 5):
        summaries = []
        for salt in ("first labels", "unrelated labels"):
            w = World(ports, salt)
            pts, h, spec, n, atlas, rechecked = local_patch(w)
            all_queries = w.queries
            miss = motion_and_radar(w, pts, h, atlas)
            need(miss == 1, "turn residual in squared unit rods")
            expected = (12, 66, 3, 55) if ports == 4 else (20, 190, 4, 131)
            need(
                (len(pts) - 1, n, len(h), len(atlas)) == expected,
                "independent fixture controls",
            )
            summaries.append(
                (
                    dict(sorted(spec.items(), reverse=True)),
                    len(h),
                    len(atlas),
                    miss,
                    rechecked,
                    all_queries,
                )
            )
        need(summaries[0] == summaries[1], "anonymization changed result")
        eig, dim, size, miss, checked, total = summaries[0]
        print(
            f"{ports}-port: {n} shell edge queries; eigenvalue:multiplicity {eig}; "
            f"{dim} angular axes. Whole patch: {total} pair queries plus shell discovery, "
            f"{size} consistently charted tags; {checked} outer tags independently placed twice or more. "
            f"Straight next tag exact; turn squared miss {miss}."
        )
    tree = World(4, "tree", tree=True)
    _, edges = shell_graph(tree.origin, tree.neighbors, tree.adjacent)
    need(
        components(edges) == [3] * 4 and all(len(x) == 2 for x in edges), "tree control"
    )
    print(
        "Tree: same 12 neighbors/66 queries, four disjoint triangles; no connected angular ruler."
    )
    print(
        f"Mod-7: root and shell identical under a bijection, but straight transport "
        f"returns to the same tag at squared frame displacement {wrap_control(7)}."
    )
    print(
        "Shortest two-link clock: four unit sides, both diagonals two (Ptolemy 4 > 2); "
        "angular squared diagonals two. Euclidean mode metric is a prescription, not elapsed time."
    )
    print(
        "Complete active two-link discovery, stable IDs and a normalization are supplied; "
        "no passive-trial savings claim, physical dimension selection, inertial law or gravity."
    )


if __name__ == "__main__":
    main()
