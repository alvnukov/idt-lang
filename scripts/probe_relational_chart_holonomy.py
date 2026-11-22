"""Can anonymous overlapping rulers detect a twist after a reunion?

The source of data is an expressly constructed quotient of four-port ordered
two-link differences. Only the fixture knows the covering words and seam.
The reader gets a starting ID, complete two-link neighbor discovery and
reciprocal adjacency. It reuses the supplied angular-mode ruler prescription
of probe_local_angular_rulers (including its Euclidean normalization).
Stable reunion IDs, noiseless active queries and records are assumptions.

Predeclared discriminator: identity linear return in translation control;
in a glide or half-turn screw exactly five direction pairs exchange, but the
reconstructed linear maps have opposite determinant. All elementary root
triangles must close without displacement or frame change. Independent
station-by-station changes of chart ordering must leave the readout intact.
This measures a conditional affine connection. It does not derive four ports,
universal dimension, physical rods, curvature, gravity or particle dynamics.
"""

from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import sys

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_local_angular_rulers as rulers

need = rulers.need


def digest(text):
    return sha256(text.encode()).hexdigest()[:24]


class Fixture:
    """Private deck group: one axial generator and two transverse periods.

    A3 consists of integer four-tuples of sum zero. Each rod is e_i-e_j.
    The axial generator is x -> R(x) + L*(1,-1,0,0). R fixes this axis
    and preserves the root set. The transverse generators M*(-1,-1,2,0)
    and M*(-1,-1,0,2) are preserved as a lattice by each R.
    A nonzero axial winding changes x0-x1 by at least 2L; a pure nonzero
    transverse period changes x2 or x3 by at least 2M. Thus all nontrivial
    deck maps move any station by at least min(L,2M) root steps. The
    quotients are locally unmodified, not locally curved fixtures.
    """

    def __init__(self, seam, length=6, transverse=7):
        self.seam, self.length, self.transverse = seam, length, transverse
        self.keys, self.stars = {}, {}
        self.origin = self.tag((0, 0, 0, 0))

    def canonical(self, x):
        a, b, c, d = x
        k = (a - b) // (2 * self.length)
        a, b = a - k * self.length, b + k * self.length
        if k % 2:
            if self.seam == "glide":
                c, d = d, c
            elif self.seam == "screw":
                a, b, c, d = -b, -a, -c, -d
            else:
                need(self.seam == "translation", "unknown seam")
        m = self.transverse
        u, c = divmod(c, 2 * m)
        v, d = divmod(d, 2 * m)
        return a + m * (u + v), b + m * (u + v), c, d

    def tag(self, x):
        key = self.canonical(x)
        name = digest(f"station:{key}")
        need(self.keys.setdefault(name, key) == key, "ID collision")
        return name

    def word_neighbors(self, station):
        x = self.keys[station]
        for i in range(4):
            for j in range(4):
                if i != j:
                    y = list(x)
                    y[i] += 1
                    y[j] -= 1
                    yield self.tag(y)

    def neighbors(self, station):
        if station not in self.stars:
            self.stars[station] = frozenset(self.word_neighbors(station))
        return self.stars[station]

    def adjacent(self, left, right):
        return right in self.neighbors(left) and left in self.neighbors(right)

    def witness_star(self):
        """Fixture-side bijection witness; its port ordering is never exposed."""
        tags = [self.origin, *self.word_neighbors(self.origin)]
        need(len(set(tags)) == len(tags), "shell collapsed")
        return tuple(self.adjacent(s, t) for s, t in combinations(tags, 2))


def measure(root, neighbors, adjacent, gauge, horizon):
    """Reader: no fixture object, word, orientation, seam or winding length."""
    cache = {}
    pair_queries = 0

    def local(s):
        nonlocal pair_queries
        if s not in cache:
            # Local slot order is independent at every center. Recover stable
            # IDs only AFTER constructing a chart in these temporary names.
            ids = {digest(f"{gauge}/{s}/{tag}"): tag for tag in neighbors(s)}
            need(len(ids) == len(neighbors(s)), "local ID collision")

            def ask(i, j):
                nonlocal pair_queries
                pair_queries += 1
                return adjacent(ids[i], ids[j])

            pts, h, _ = rulers.chart("center", lambda _: ids, ask)
            ids["center"] = s
            cache[s] = {ids[k]: x for k, x in pts.items()}, h
        return cache[s]

    initial, metric = local(root)
    zero = initial[root]
    rank = len(metric)
    directions = {x: s for s, x in initial.items() if s != root}

    def advance(frame, next_tag):
        points, h = local(next_tag)
        mapped, extra = rulers.align(frame, points, h, metric)
        need(extra > 0, "no redundant landmark")
        return mapped

    def replay(path):
        frame = initial
        for s in path:
            frame = advance(frame, s)
        return frame

    def linear_return(frame):
        # The same initial station IDs supply all columns of the return
        # map. Verify the fit on all the others and its isometry exactly.
        rays = sorted(directions)
        chosen = rulers.independent(rays)
        new = [rulers.minus(frame[directions[v]], frame[root]) for v in rays]
        matrix = rulers.mm(
            list(zip(*(new[i] for i in chosen), strict=True)),
            rulers.inverse(list(zip(*(rays[i] for i in chosen), strict=True))),
        )
        need(all(rulers.mv(matrix, v) == w for v, w in zip(rays, new, strict=True)),
             "return map does not fit the whole star")
        mt = list(zip(*matrix, strict=True))
        need(rulers.mm(rulers.mm(mt, metric), matrix) == metric, "nonisometric return")
        need(set(new) == set(rays), "rays did not return as a permutation")
        return matrix, sum(v != w for v, w in zip(rays, new, strict=True))

    # Every unoriented triangle in this root star, including crossings of
    # any arbitrary fundamental-domain cut used by the simulator.
    triangles = 0
    for a, b in combinations(sorted(directions.values()), 2):
        if b in local(a)[0]:  # observed complete closed star of a
            need(replay((a, b, root)) == initial, "contractible triangle failed")
            triangles += 1
    need(triangles > 0, "no triangle control")

    # Advance ALL initial choices synchronously; stop only on first reunion
    # or the supplied resource budget. Each continuation is predicted by
    # the currently transported chart, not by a port or hidden atlas.
    walkers = [(v, (tag,), initial) for v, tag in sorted(directions.items())]
    for tick in range(1, horizon + 1):
        updates, closed = [], []
        for v, path, old in walkers:
            tip = path[-1]
            frame = advance(old, tip)
            if tip == root:
                m, moved = linear_return(frame)
                need(rulers.squared(frame[root], zero, metric) == tick**2,
                     "return has wrong developed length")
                twice = replay(path + path)
                need(linear_return(twice) == (rulers.eye(rank), 0), "two circuits twist")
                need(twice[root] == rulers.plus(frame[root], frame[root]),
                     "double-circuit displacement")
                closed.append((sum(m[i][i] for i in range(rank)), det(m), moved))
            else:
                predicted = rulers.plus(frame[tip], v)
                next_tags = [s for s, x in frame.items() if x == predicted]
                need(len(next_tags) == 1, "straight continuation is not unique")
                updates.append((v, path + (next_tags[0],), frame))
        if closed:
            return (rank, triangles, tick, Counter(closed)), (len(cache), pair_queries)
        walkers = updates
    raise ValueError("no straight return within budget (not a global exclusion)")


def det(m):
    # No dimension assumed. Matrices are tiny and exact.
    if not m:
        return 1
    return sum((-1)**j * x * det([r[:j] + r[j + 1:] for r in m[1:]])
               for j, x in enumerate(m[0]) if x)


def main():
    # Expected fixture answers are used ONLY after the blinded measurement.
    controls = {"translation": (3, 1, 0), "glide": (1, -1, 10), "screw": (-1, 1, 10)}
    witness = None
    for seam, expected in controls.items():
        world = Fixture(seam)
        star = world.witness_star()
        if witness is None:
            witness = star
        need(star == witness, "fixture root-and-shell incidence differs")
        outcomes = [
            measure(world.origin, world.neighbors, world.adjacent, gauge, horizon=10)
            for gauge in ("chart A", "fresh chart B")
        ]
        need(outcomes[0] == outcomes[1], "local chart relabeling changed readout")
        (rank, triangles, tick, measured), (stations, pairs) = outcomes[0]
        need((rank, triangles, tick, measured) == (3, 24, 6, Counter({expected: 2})),
             "unmatched returned-loop control")
        print(f"{seam}: rank {rank}; {triangles} elementary triangles close exactly; "
              f"2 first-return rays at {tick} steps, squared developed displacement {tick**2}; "
              f"trace/determinant/moved rays = {tuple(map(int, next(iter(measured))))}; "
              f"two circuits restore frame. {stations} local charts, {pairs} shell-pair "
              "queries per gauge, plus complete neighbor discovery.")
    print("Same root-and-shell incidence, two independent station-local gauges. "
          "A winding twist need not be curvature; local closure at sampled triangles "
          "alone certifies neither global flatness nor physical dimension.")


if __name__ == "__main__":
    main()
