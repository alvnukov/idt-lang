"""Conditional stock rigidity for TWO neutral three-tag factors.

The carrier is the group of integer 3x3 arrays with every row and column
sum zero. Both factors' tag addresses, signed coherent addition, and all
six setting devices are supplied. Each transposes only rows or only columns.
A common, otherwise arbitrary nonnegative real W on this entire group,
W(0)=0, is assumed to obey for each device P

    W(X+PX) + W(X-PX) = g_P W(X),     g_P > 0 independent of X.

Here PX denotes the action on the chosen index. The sum refers to separately
readable outputs, not to a coherent sum of their currents. In particular the
law also applies to nonproduct parents, scaled inputs, and every spectator
context. Paired addresses do NOT by themselves imply these assumptions.
No arbitrary joint-cell transpositions, factorization of W, metric, or
anonymity/evenness of W are assumed. If W=0 the gains are unconstrained.

Conditional all-integer argument (not a Lean proof):

1. Each output Y=X+PX or X-PX satisfies PY=+Y or -Y. A second use of the
   same law yields W(2Y)=g_P W(Y). Apply the equation to 2X, substitute this
   fact on its two outputs, and divide by g_P: W(2X)=g_P W(X). For any one
   lit X all six gains must therefore coincide, g.
2. Let j=i+1, k=i+2 cyclically and r_i denote row i. The row split fixing
   i yields exactly m_i (outer) r_i and e_i (outer) (r_j-r_k), where
   m_i has 2 at i, -1 elsewhere and e_i has +1 at j, -1 at k. Each second
   factor is a neutral integer triple: there is no denominator or primitivity
   condition. Thus a lit parent has a lit product child. For fixed neutral
   v the restriction u -> W(u outer v) obeys the one-triangle hypotheses,
   including zero at the origin; analogously with u fixed. Apply the
   all-integer dichotomy in probe_triangle_stock_rigidity to one nonzero
   restriction. Then g=1 or 4.
3. Write e=(1,-1,0). The one-triangle stock normalized at e is uniquely
   q4(u)=sum(u_i^2)/2 or q1(u)=1[(u_0-u_1) mod 3 != 0]. The latter is
   equivalent to not all currents being congruent, by neutrality. Zero
   restrictions satisfy the same formula with coefficient zero. Applying
   uniqueness first in u, then in v at e, gives
       W(u outer v)=W(e outer e) q_g(u) q_g(v).
   This product rule is a conclusion; its positive scale is not fixed.
4. For ALL parents the row split now fixes W(X) uniquely from products.
   At g=4 the matching extension is C sum(X_ij^2) with C=W(e outer e)/4:
   each cell pair obeys (x+y)^2+(x-y)^2=2x^2+2y^2 and P permutes cells.
   At g=1 it is D 1[e^T X e != 0 mod 3], D=W(e outer e). On a neutral
   triple e^T(Pu)=-e^T u mod 3 for any transposition. Applying this to
   the neutral vector Xe or X^T e shows that the plus output has zero class
   and the minus output has twice the initial class. These extensions have the
   stated restrictions and hence are the only ones. A lit nonzero product
   with a median factor selects g=4; so does a lit antisymmetric circulation.

For a lit parent define population fractions from normalized stocks. With
both outcomes retained on each side the joint raw cell is W(A_s B_t X).
The currents commute; sum over t to obtain g W(A_s X), or sum over s to
obtain g W(B_t X). Division by g^2 W(X) gives the solo fractions, independent
of the remote setting. A dark parent has no population to normalize. This
is not an assignment of Bell-local outcomes to individual tickets.

The finite checks below are distinct from the conditional classification.
They do not derive paired addresses, free preparation, a physical matched
bypass, the stock-to-frequency rule, complex amplitudes, general composites,
or spacelike detector dynamics. Run: python3 -B -O -m scripts.probe_local_composite_stock
"""

from fractions import Fraction as F
from itertools import product

from scripts.probe_heralded_triangle_factory import factory
from scripts.probe_triangle_exchange_source import (
    edge, local_swap, median, outer, route_block, signed_split, signed_vector,
)


PORTS = range(3)
BITS = range(2)
E = (1, -1, 0)


def need(condition, what):
    if not condition:
        raise AssertionError(what)


def complete(a, b, c, d):
    """Independent four-entry chart: integral and bijective, no inner product."""
    return (a, b, -a-b, c, d, -c-d, -a-c, -b-d, a+b+c+d)


def transpose(x):
    return tuple(x[3*j+i] for i in PORTS for j in PORTS)


def split(x, side, i):
    """Compute from a tag permutation, independently of the product formula."""
    j, k = (i+1) % 3, (i+2) % 3
    perm = list(PORTS)
    perm[j], perm[k] = k, j
    px = tuple(x[3*perm[a]+b] if side == 0 else x[3*a+perm[b]]
               for a in PORTS for b in PORTS)
    return tuple(tuple(t + sign*s for t, s in zip(x, px)) for sign in (1, -1))


def product_children(x, side, i):
    if side:
        return tuple(map(transpose, product_children(transpose(x), 0, i)))
    rows = [x[3*k:3*k+3] for k in PORTS]
    j, k = (i+1) % 3, (i+2) % 3
    return outer(median(i), rows[i]), outer(edge(i), tuple(a-b for a, b in zip(rows[j], rows[k])))


def squares(x):
    return sum(t*t for t in x)


def residue(x):
    return int((x[0] - x[1] - x[3] + x[4]) % 3 != 0)


def minor(x):
    # Other 2x2 cofactors have the same magnitude by zero row/column sums.
    return x[0]*x[4] - x[1]*x[3]


def rival(x):
    # lambda=1 suffices: a positive nonquadratic stock with no zero anomalies.
    return squares(x) + minor(x)**2


def fractions(weights):
    n = sum(weights)
    return tuple(F(k, n) for k in weights) if n else None


def meter(w, x, side, k):
    return fractions((w(x), *(w(y) for y in split(x, side, k))))


def cells(x, k, l):
    return tuple(z for y in split(x, 0, k) for z in split(y, 1, l))


def finite_box():
    """All 5^4 labelled charts, no projective or sign identifications."""
    ranks = [0, 0, 0]
    for abcd in product(range(-2, 3), repeat=4):
        x = complete(*abcd)
        rank = 2 if minor(x) else int(any(x))
        ranks[rank] += 1
        left = [split(x, 0, i) for i in PORTS]
        right = [split(x, 1, i) for i in PORTS]
        for side, branches in enumerate((left, right)):
            for i, ys in enumerate(branches):
                need(ys == product_children(x, side, i) and all(not minor(y) for y in ys),
                     "local child factorization")
                need(tuple(map(squares, ys)) == tuple(map(rival, ys)), "ordinary read sees rival")
                need(sum(map(squares, ys)) == 4*squares(x), "gain four")
                need(tuple(map(residue, ys)) == (0, residue(x)), "gain one, modulo three")
        for k, l in product(PORTS, repeat=2):
            ab = tuple(z for y in left[k] for z in split(y, 1, l))
            ba = [split(y, 0, k) for y in right[l]]
            need(ab == tuple(ba[b][a] for a, b in product(BITS, repeat=2)), "order dependence")
            for w, g in ((squares, 4), (residue, 1)):
                p, q, r, s = map(w, ab)
                need((p+q, r+s) == tuple(g*w(y) for y in left[k]) and
                     (p+r, q+s) == tuple(g*w(y) for y in right[l]), "marginal or denominator")
                need(p+q+r+s == g*g*w(x), "dark/null population or total")
    need(ranks[0] == 1 and ranks[1] and ranks[2] and sum(ranks) == 625, "box coverage")
    return ranks


def addressed_bypass(src, side, k):
    """Keep both factory heralds; route every incoming address to five seeds."""
    n = 18
    ident = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
    matrix = ident + signed_split(local_swap(k, side, 2))
    cloud, routes, gain, _ = route_block(src.cloud, matrix, False)
    need(gain == 5, "three-port routed gain")
    bins = [[0, 0, 0] for _ in BITS]
    for pair in src.tickets.values():
        h = src.cloud[pair[0]][0] // 9
        for seed in range(gain):
            i, j = routes[pair, seed]
            rail = cloud[i][0]
            need(rail == cloud[j][0] and rail % n // 9 == h, "bypass changed herald")
            bins[h][rail // n] += 1
    need(sum(map(sum, bins)) == 5 * len(src.tickets), "incomplete bypass histories")
    return tuple(map(tuple, bins))


def source_controls():
    bright = outer(median(0), E)
    need(squares(bright) > 0 and not residue(bright), "lit-median discriminator")
    for x in (outer(edge(0), edge(1)), bright, outer(E, median(1)), outer(median(0), median(1))):
        need(all(meter(squares, x, side, k) == meter(rival, x, side, k)
                 for side, k in product(BITS, PORTS)), "product calibration mismatch")
    for i, j in product(PORTS, repeat=2):
        # Source preparation only: co-located whole-factor exchange. It is
        # NOT a seventh device in the local stock equation. Both flags retained.
        src = factory(edge(i), edge(j))
        raw = signed_vector(src, 18)
        plus, minus = raw[:9], raw[9:]
        need(tuple(map(squares, (plus, minus))) == ((16, 0) if i == j else (10, 6)),
             "actual herald stock")
        for side, k in product(BITS, PORTS):
            bins = addressed_bypass(src, side, k)
            for h, x in enumerate((plus, minus)):
                ys = split(x, side, k)
                need(bins[h] == (squares(x), *map(squares, ys)), "routed bypass vs stock")
                need(tuple(map(squares, ys)) == tuple(map(rival, ys)),
                     "two-output detector separated the rivals")
                if i == j:
                    need(meter(squares, x, side, k) == meter(rival, x, side, k),
                         "rank-zero/one inputs should not separate")
                else:
                    need(abs(minor(x)) == 1, "reachable rank-two witness")
                    baseline, changed = meter(squares, x, side, k), meter(rival, x, side, k)
                    need(baseline[0] == F(1, 5) and changed[0] == (F(11, 51), F(7, 31))[h],
                         "untouched joint bypass discriminator")
        if i == j:
            continue
        need(residue(minus) == 0, "mod-three circulation is not lit")
        score = 0
        for k, l in product(PORTS, repeat=2):
            raw_cells = tuple(map(squares, cells(minus, k, l)))
            need(raw_cells == ((0, 48, 48, 0) if k == l else (36, 12, 12, 36)),
                 "circulation trine population")
            agree = F(raw_cells[0]+raw_cells[3], sum(raw_cells))
            score += (int(l == (k+1) % 3) - int(l == k)) * agree
        need(score == F(9, 4), "conditional, not pooled, cycle score")
    bound = max(sum((a[k] == b[(k+1) % 3]) - (a[k] == b[k]) for k in PORTS)
                for a in product(BITS, repeat=3) for b in product(BITS, repeat=3))
    need(bound == 2, "deterministic local assignments")


def main():
    ranks = finite_box()
    source_controls()
    print("Two all-lattice branches conditional on six local laws: Frobenius squared / gain 4,"
          " or joint residue mod 3 / gain 1. A lit median product or circulation selects 4.")
    print("625 labelled arrays (ranks 0,1,2):", tuple(ranks),
          "; both gains, both split orders, full marginal sums.")
    print("Nine ordered source settings, both heralds. Six unequal-edge antisymmetric branches:"
          " same=(0,48,48,0), different=(36,12,12,36), cycle 9/4 vs local 2.")
    print("Minor-squared rival matches all products and all ordinary local output stocks."
          " Matched untouched joint bypass: squared 1/5; rival 11/51 on symmetric,"
          " 7/31 on antisymmetric unequal-edge herald. No physical calibration inferred.")


if __name__ == "__main__":
    main()
