"""When does a whole-packet stock have to be quadratic on the neutral triangle?

Conditional integer-lattice argument, with independent finite controls below.
Let W be any nonnegative real function on all integer triples v with sum zero,
W(0)=0. For each transposition P suppose, for every v,

    W(v+Pv) + W(v-Pv) = g_P W(v),     g_P > 0 independent of v.

No label symmetry, global sign symmetry, rail additivity, pair enumeration,
fixed common gain or ticket identities are assumed. The SUM across two
separately readable output branches IS assumed. A common function of the
boundary current, the three available exchanges, and all-scale applicability
are physical inputs, not results. Nonzero W gives the following dichotomy.

1. Set u=v+Pv or v-Pv. Each is a P-eigenvector, so W(2u)=g_P W(u).
   Apply the split law at 2v; cancel g_P to get W(2v)=g_P W(v) for *all* v.
   Thus a single nonzero stock makes the three gains equal, say g.
2. Average W over label permutations. Nonnegativity preserves nonzeroness;
   conjugation preserves the split law. For this symmetric average, let
   E(t)=W(0,t,-t) (automatically even), M(t)=W(2t,-t,-t). Splitting the
   edge gives E(2t)=g E(t), M(t)=(g-1)E(t). Splitting (a,b,-a-b) at its
   first and second ports gives

      E(2a+b)-E(a+2b) = (g-1)(E(a)-E(b)).

   Some E(t)>0: otherwise all medians and hence all inputs would be dark.
   Divide by E(t) at that scale. The substitutions (a,b)=(2t,-t),
   (2t,t),(3t,-t) give e3=(g-1)^2, e5=g^2+(g-1)^2 and
   e5-1=(g-1)(e3-1), where ek=E(kt)/E(t). Equivalently
   g(g-1)(g-4)=0. Since g>0, only 1 and 4 survive.
3. Now use the ORIGINAL labelled W. Write Eij=W(t(e_i-e_j)), with distinct
   i,j,k; subtract the splits of Eij and Eik fixing i: their plus branches
   coincide, hence g(Eij-Eik)=Ekj-Ejk. Apply this linear equation to the
   even and odd parts under t -> -t. Even directed edges are all equal.
   For the odd cyclic edges f=(E12,E23,E31) the equations read
   g(f_j+f_k)=-2 f_i. Their sum gives (2g+2)sum(f)=0; subtraction gives
   (g-2)(f_i-f_j)=0. Neither surviving g is 2, so the odd parts vanish.
   Thus the original edges are anonymous and even. Their splits force
   M_i(t)=(g-1)E(t) at every port; a split at any port determines W on
   every triple. Step 2's scalar recurrence holds for this original W.
4. At g=4 choose v in {-1,0,1} congruent to -n mod 3. For n>=2,
   a=(2n-v)/3, b=(2v-n)/3 satisfy |a|,|b|,|v|<n. Then the recurrence
   gives E(n)=3(E(a)-E(b))+E(v)=n^2 E(1) by induction and evenness.
   Substitution yields W(a,b,c)=E(1)(a^2+b^2+c^2)/2.
   At g=1 it gives E(n)=E(v) for n+v divisible by 3 (use the same inverse
   substitution). E(3k)=0; E(3k+/-1)=E(1). Thus W is E(1) times the
   indicator that not all labels have congruent currents mod 3. This law
   darkens every median. One lit median, at any scale/port/sign, is enough
   to select 4: no independent unit-edge positivity assumption is needed.

The proof concerns magnitudes on *three* ports; it neither mints tickets nor
derives their probabilities, physical detector dynamics or a composite law.
Run: python3 -B -O -m scripts.probe_triangle_stock_rigidity
"""

from fractions import Fraction
from itertools import product

from scripts.probe_unsigned_transfer_triangle import boundary, refl, split


PORTS = range(3)
ZERO = (0, 0, 0)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def inputs(radius):
    for a, b in product(range(-radius, radius + 1), repeat=2):
        if abs(a + b) <= radius:
            yield a, b, -a - b


def branches(v, fixed):
    p = refl(fixed)
    return tuple(tuple(x + sign * v[p[i]] for i, x in enumerate(v)) for sign in (1, -1))


def concentrated(v):
    """Construct from a freely pooled multiset of unit directed arcs; no signs on arcs."""
    starts = [i for i, n in enumerate(v) for _ in range(-n)]
    ends = [i for i, n in enumerate(v) for _ in range(n)]
    return tuple(zip(starts, ends, strict=True))


def quadratic(v):
    a, b, c = v
    return (a * a + b * b + c * c) // 2


def dark(v):
    return int(len({x % 3 for x in v}) != 1)


def outputs(w, v, i):
    return tuple(map(w, branches(v, i)))


def ray(v):
    if v == ZERO:
        return "zero", 0
    if 0 in v:
        return "edge", max(v)
    if len(set(v)) == 2:
        return "median", abs(next(x for x in v if v.count(x) == 2))
    return "off", None


def ray_rival(v):
    """Gain 2 on ALL integer edge/median rays; not a solution on general inputs."""
    kind, n = ray(v)
    if kind == "zero":
        return 0
    need(kind != "off", "ray countermodel is not an off-ray stock")
    return n & -n  # 2^nu_2(n): doubling scales by 2, tripling preserves stock.


def native_controls():
    # Arbitrarily pooled unit transfers span the *entire* neutral integer
    # lattice by matching negative to positive multiplicities. This preparation
    # privilege is separate from iterating single-edge exchanges.
    for v in inputs(4):
        raw = concentrated(v)
        need(boundary(raw, 3) == v, "free pooled preparation")
        for i, reverse in product(PORTS, (False, True)):
            observed = tuple(boundary(g, 3) for g in split(raw, refl(i), reverse))
            need(observed == branches(v, i), "native branch boundary")

    # Each child of an edge of scale t is 0, edge(t or 2t), or median(t);
    # from a median it is 0, median(t or 2t), or edge(3t). Linear integer
    # branch maps imply the scale rule on every ray from its unit instance.
    allowed = {"edge": {("zero", 0), ("edge", 1), ("edge", 2), ("median", 1)},
               "median": {("zero", 0), ("median", 1), ("median", 2), ("edge", 3)}}
    for origin, expected in allowed.items():
        found = {ray(u) for v in inputs(2) if ray(v) == (origin, 1)
                 for i in PORTS for u in branches(v, i)}
        need(found == expected, "single-motif branch closure")
    for v in inputs(16):
        if ray(v)[0] != "off":
            need(all(sum(outputs(ray_rival, v, i)) == 2 * ray_rival(v) for i in PORTS),
                 "gain-two single-motif control")

    # The minimal off-ray preparation (2,1,-3) needs three arrows. Comparing
    # fixed 0 vs fixed 2 shares no E(5): sums must be equal across settings.
    v = (2, 1, -3)
    need(all(ray(u)[0] != "off" for u in inputs(2)), "smaller off-ray input")
    raw = ((2, 0), (2, 0), (2, 1))
    native = [tuple(boundary(g, 3) for g in split(raw, refl(i), False)) for i in PORTS]
    tables = [tuple(tuple(map(w, out)) for out in native) for w in (quadratic, dark, ray_rival)]
    need(tables == [((12, 16), (3, 25), (27, 1)), ((0, 1), (0, 1), (0, 1)),
                    ((2, 4), (1, 1), (1, 1))], "three-transfer predictions")
    # A named setting alone admits W depending on its port, with a different
    # parent-to-children ratio on other settings; positivity alone is no cure.
    preferred = lambda u: abs(u[0]) + abs(u[1] - u[2])
    need(all(sum(outputs(preferred, u, 0)) == 2 * preferred(u) for u in inputs(5))
         and {sum(outputs(preferred, v, i)) for i in PORTS} != {2 * preferred(v)},
         "single-setting anisotropy")
    return tables


def independent_rank(radius, gains, anonymous=False):
    """Exact homogeneous elimination on free values W(v), no candidate formula.

    Default keeps ordered triples and their negatives independent unknowns.
    Return (#unknowns, nullity, whether six directed unit edges can sum != 0).
    Only incident input/output variables enter, plus the equation W(0)=0.
    """
    names, pivots = {}, {}

    def index(v):
        key = tuple(sorted(v)) if anonymous else v
        return names.setdefault(key, len(names))

    def row(terms):
        r = {}
        for v, coeff in terms:
            j = index(v)
            r[j] = r.get(j, 0) + Fraction(coeff)
            if not r[j]:
                del r[j]
        return r

    def insert(r):
        while r:
            k = min(r)
            c = r[k]
            if k not in pivots:
                pivots[k] = {j: x / c for j, x in r.items()}
                return True
            for j, x in pivots[k].items():
                r[j] = r.get(j, 0) - c * x
                if not r[j]:
                    del r[j]
        return False

    insert(row(((ZERO, 1),)))
    for v in inputs(radius):
        for i in PORTS:
            u, z = branches(v, i)
            insert(row(((u, 1), (z, 1), (v, -gains[i]))))
    nullity = len(names) - len(pivots)
    edges = row((v, 1) for v in inputs(1) if v != ZERO)
    return len(names), nullity, insert(edges)


def arithmetic_controls():
    for v in inputs(11):
        for i in PORTS:
            for w, g in ((quadratic, 4), (dark, 1), (lambda u: u[0], 2)):
                need(sum(outputs(w, v, i)) == g * w(v), "whole-lattice witness check")
    for n in range(2, 301):
        tiny = (0, -1, 1)[n % 3]
        a, b = (2 * n - tiny) // 3, (2 * tiny - n) // 3
        need((2 * a + b, a + 2 * b) == (n, tiny)
             and max(abs(a), abs(b), abs(tiny)) < n
             and 3 * (a * a - b * b) + tiny * tiny == n * n, "inductive descent")
    # Show exactly what a finite input horizon fails to constrain.
    r = 5
    tail = lambda v: quadratic(v) + int(max(map(abs, v)) == 2 * r + 1)
    need(all(sum(outputs(tail, v, i)) == 4 * tail(v) for v in inputs(r) for i in PORTS),
         "in-window indistinguishability")
    outside = (0, 2 * r + 1, -2 * r - 1)
    need(sum(outputs(tail, outside, 0)) != 4 * tail(outside), "outside-window separation")
    # Numbers for error localization, not the universal proof in the docstring.
    data = {g: independent_rank(5, (g,) * 3) for g in (1, 2, 4)}
    need(data[1][1:] == data[4][1:] == (1, True), "labelled rank at surviving gains")
    need(data[2][1] >= 2 and not data[2][2], "signed linear controls at gain two")
    need(independent_rank(2, (2,) * 3, True)[2] and not independent_rank(3, (2,) * 3, True)[2],
         "first anonymous radius separating gain two")
    need(not independent_rank(5, (1, 2, 4))[2], "unequal gains and unit stock")
    return data


def main():
    tables = native_controls()
    data = arithmetic_controls()
    print("Conditional whole-triangle dichotomy: quadratic/gain 4 or mod-3-dark/gain 1;"
          " one lit median selects the first. No scale fixed.")
    print("Three pooled unit transfers -> (2,1,-3), fixed ports 0/1/2, stock in unit-edge units:"
          f" quadratic {tables[0]}; dark {tables[1]}; gain-2 ray rival {tables[2]}.")
    print("Exact freely labelled finite rank, radius 5, gain: (variables, nullity, unit-edge sum can be nonzero):",
          data)
    print("Supplied: boundary-only stock, independently readable branch sum, positive state-independent"
          " gain per setting and all required preparations. Single-edge splits alone and finite"
          " horizon do not imply the universal law. Counts are not ticket identities or probabilities.")


if __name__ == "__main__":
    main()
