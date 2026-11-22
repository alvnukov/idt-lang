"""Can the three-rail median-dark stock extend to a connected fourth rail?

On L_n={integer vectors with zero sum}, assume one nonnegative nonzero W
with W(0)=0, and on every tested swap P assume W(v+Pv)+W(v-Pv)=g_P W(v)
with its own positive input-independent scalar, on ALL of L_n. The maps
in this probe are canonical swaps, not arbitrary high-dimensional
repeatable instruments. No absolute calibration, bounded continuum, rail
additivity, complex amplitudes or physical spatial dimension is inferred.

With all swaps available, consider each three-rail support separately. The
three-rail stock dichotomy applies to any nonzero restriction; it makes
each of its edge curves E(t) identical, quadratic or mod three. If every
edge were dark, replace coordinates (a,b) by (a+b,0): the two inputs have
the same plus output, both minus outputs are edges, so W is unchanged.
Repeated merging would give W identically zero. Therefore some restriction
is nonzero and its common edge scale propagates through overlapping triples
to every pair. Doubling gives the same positive g for all tested settings.

A median-dark triple cannot extend even once: swap a unit component of
the median with an idle fourth rail. The minus output is a bright unit edge
from a zero-stock input. This contradicts positivity and any finite gain.
Thus g=4 and E(t)=c t². The merge identity gives
    W(v)-W(v with a,b merged)=[E(a-b)-E(a+b)]/4 = -c a b.
This is the decrement of c sum(v_i²)/2, so merging down to zero proves the
formula for every n>=4. No infinite averaging schedule or continuity axiom.
The checked examples are finite evidence for this conditional argument.

If W is reversal-even, a connected set of available swap contacts suffices:
their split equations imply W(Pv)=W(v). The edge permutations generate all
relabelings, extending one fixed equation by conjugation. This argument
does not add the conjugate operations to the physical apparatus. Unoriented
graph readout is even. The all-swaps result above does not assume evenness.
"""

from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_bipartite_triangle_origin import graph, mass, need, split


def branches(v, i, j):
    p = list(v)
    p[i], p[j] = p[j], p[i]
    return tuple(tuple(a + s * b for a, b in zip(v, p, strict=True)) for s in (1, -1))


def energy(v):
    need(sum(v) == 0, "not a neutral input")
    return sum(x * x for x in v) // 2


def residue(t):
    return int(t % 3 != 0)


def merged(v, i, j):
    w = list(v)
    w[i] += w[j]
    w[j] = 0
    return tuple(w)


def merge_delta(v, i, j, E, g):
    w = merged(v, i, j)
    plus, minus = branches(v, i, j)
    otherplus, otherminus = branches(w, i, j)
    need(
        plus == otherplus and minus[i] == v[i] - v[j] and otherminus[i] == v[i] + v[j],
        "shared branch",
    )
    return w, F(E(minus[i]) - E(otherminus[i]), g)


def direct_path(tree):
    # Source, first swap, second swap chosen along *actual* adjacent edges.
    # The intermediate plus port is left undetected. There is no herald cut
    # on a click of a port an alternative model calls dark.
    first, second = ((1, 2), (2, 3)) if tree == "path" else ((0, 2), (0, 3))
    z = (1, -1, 0, 0)
    y, _ = branches(z, *first)
    _, out = branches(y, *second)
    need(
        sorted(y) in ([-1, -1, 0, 2], [-2, 0, 1, 1]) and sorted(out) == [-1, 0, 0, 1],
        "median-to-edge",
    )

    def tap(g, ij):
        i, j = ij
        return split(g, lambda x: j if x == i else i if x == j else x)

    start = graph((0, 1), ((0, 1),))
    before = tap(start, first)
    cells = tuple(tuple(mass(h) for h in tap(g, second)) for g in before)
    need(
        tuple(map(mass, before)) == (6, 2) and cells == ((22, 2), (6, 2)),
        "unsigned four-rail stock",
    )
    return y, out


def main():
    for tree in ("path", "claw"):
        direct_path(tree)
    start = (1, 1, -1, -1)
    totals = []
    for order in (((0, 1), (0, 2), (0, 3)), ((0, 2), (1, 3), (0, 1))):
        v = start
        total = 0
        for i, j in order:
            v, d = merge_delta(v, i, j, residue, 1)
            total += d
        need(not any(v), "did not reduce")
        totals.append(total)
    need(totals == [-1, 2], "incompatible modulo-three merge paths")
    trials = 0
    for n in (4, 5, 6):
        for raw in product((-2, -1, 0, 1, 2), repeat=n - 1):
            v = (*raw, -sum(raw))
            for i, j in combinations(range(n), 2):
                w, d = merge_delta(v, i, j, lambda t: t * t, 4)
                need(d == energy(v) - energy(w) == -v[i] * v[j], "pairwise telescope")
                trials += 1
    # On any chain, keep merging leaves into their parent. Works even when
    # n isn't a power of two. A disconnected instrument changes the problem.
    for n in range(4, 32):
        v = tuple((7 * i % 9) - 3 for i in range(n - 1))
        v = (*v, -sum(v))
        orig = v
        acc = 0
        for i in range(n - 1, 0, -1):
            v, d = merge_delta(v, i - 1, i, lambda t: t * t, 4)
            acc += d
        need(not any(v) and acc == energy(orig), "spanning-tree merge")

    def isolated(v):
        return energy(v) + v[-1] ** 2

    v = (2, -1, -1, 0)
    need(
        all(
            sum(isolated(z) for z in branches(v, i, j)) == 4 * isolated(v)
            for i, j in combinations(range(3), 2)
        ),
        "isolated spectator",
    )
    need(
        sum(isolated(z) for z in branches(v, 0, 3)) != 4 * isolated(v),
        "contact failed to see spectator",
    )
    print(
        "Fourth empty rail: an unmeasured median port followed by a physical swap "
        "gives a unit edge, incompatible with positive constant-gain median-dark stock."
    )
    print(
        "Raw graph edge on path and claw: old split 6/2; final rows (22,2)/(6,2), no lost branches."
    )
    print(
        "Competing dark extension assigns −1 vs 2 to the same four-component input; "
        "quadratic merge identities checked:",
        trials,
    )
    print(
        "Conditional n>=4 extension uses all neutral inputs and canonical tested swaps. "
        "Disconnected contacts admit anisotropic stocks; n counts rail labels, not space dimensions."
    )


if __name__ == "__main__":
    main()
