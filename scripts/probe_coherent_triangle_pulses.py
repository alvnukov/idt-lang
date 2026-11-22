"""Co-located, reusable pulse on neutral data x neutral triangle reference.

Route signs/children, an undetected path, its controlled reference cycle,
coherent reunification and two selectable data exchanges are SUPPLIED. The
splitter is a reversible *ray* map; the integer matrix squares to 4I, not I.
No numerical rotation, complex scalar, analyzer frequency or Bloch coordinate
enters the event router. Existing cancellation, uniform seeds, ordered pairs
and a common reference orientation remain assumptions, not detector dynamics.

Closure argument (mathematical, not an enumerated or Lean result): on the
four-real-dimensional neutral product, C on the reference acts as a complex
scalar omega, since C²+C+I=0. Choose the complex orientation with
omega=exp(2 pi i/3); changing it conjugates the description. The *normalized*
pulse U is identity on the P+ line and omega on the P- line. Its projective
adjoint is a 120-degree rotation. Each pulse has complex determinant omega.
Consequently omega^-1 U1 U0 has determinant one; multiplying by this common
scalar is diagnostic, not a new routed gate. Its real trace 5/2 gives complex
trace 5/4 (the eigenvalues of a determinant-one unitary pair are conjugate),
hence scalar part 5/8. Independently, the actual adjoint product has trace
9/16. It cannot have finite order: a sum of roots of unity is an algebraic
integer, and a rational algebraic integer is an integer.

In the usual real rotation-group topology its powers are dense on a rotation
circle. If both order-three generators preserved this circle's axis line,
they would each fix the axis pointwise (odd order), so both would have the
same axis, contrary to their measured Gram product -1/2. Conjugation therefore
supplies a second nonparallel rotation circle. The closed subgroup they
generate is SO(3): its Lie algebra contains both axial directions and their
nonzero perpendicular bracket. This uses ordinary group topology, the closed
subgroup theorem and unbounded finite words. It does not construct a physical
time parameter/generator, continuum apparatus or efficient compilation, and
does not imply exact access to arbitrary rotations. The complete two-split
pulse has gain 16; the compressed four-child rule has gain 4. Neither gain
can be dropped when counting descendants. No remote-party, full QM or 3D
space result. Earlier probe_native_mixer_sector_density uses *different*,
already complex ports/mixers; the group-density reasoning is not a new theorem.

The undetected path is essential. If its distinguishable record survives,
each conditional output is still on its original one-dimensional complex
P eigenspace: the reference turn on the minus line is just a common phase
there. Ignoring that record mixes two old trine eigenpreparations; checking
only the blank output port cannot distinguish this from coherent uncomputing.

Run: python3 -B -O -m scripts.probe_coherent_triangle_pulses
"""

from fractions import Fraction as F
from functools import cache
from itertools import product

from scripts.probe_heralded_triangle_factory import independent, outcome
from scripts.probe_triangle_cycle_phase_axis import (
    BITS,
    LABELS,
    D,
    K,
    Stock,
    act,
    cycle_paths,
    edge,
    extend,
    need,
    observed_table,
    outer,
    pairs,
    route_block,
    transposition,
)
from scripts.probe_triangle_exchange_source import signed_vector


def tr(a):
    return tuple(zip(*a, strict=True))


def mul(a, b):
    return tr(tuple(act(a, c) for c in tr(b)))


def scale(s, a):
    return tuple(tuple(s * x for x in r) for r in a)


def eye(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def trace(a):
    return sum(row[i] for i, row in enumerate(a))


def columns(n, out, children):
    """Sum signed endpoint addresses of one parent's raw paths."""
    cols = []
    for i in range(n):
        v = [0] * out
        for j, s in children(i):
            v[j] += s
        cols.append(v)
    return tr(cols)


@cache
def splitter(k, histories=1):
    p = transposition(k)

    def branches(i):
        h, j = divmod(i, 18)
        path, ab = divmod(j, 9)
        a, b = divmod(ab, 3)
        for dest in BITS:
            same = dest == path
            start = h * 18 + dest * 9
            yield start + ab, 1
            yield start + 3 * p[a] + b, 1 if same else -1

    return columns(18 * histories, 18 * histories, branches)


def twist(i, wind):
    path, ab = divmod(i, 9)
    a, b = divmod(ab, 3)
    return 9 * path + 3 * a + (b + path * wind) % 3


def compact(k, wind):
    """Four children: stay and exchange, plus their relatively signed turns."""
    p = transposition(k)

    def branches(i):
        a, b = divmod(i, 3)
        for dest, s in ((a, 1), (p[a], -1)):
            yield 3 * dest + b, 1
            yield 3 * dest + (b + wind) % 3, s

    return columns(9, 9, branches)


def exact_pulse(k, wind):
    b = splitter(k)
    need(mul(b, b) == scale(4, eye(18)), "splitter is not its own ray inverse")
    c = columns(18, 18, lambda i: ((twist(i, wind), 1),))
    m = mul(b, mul(c, b))
    u = tuple(row[:9] for row in m[:9])
    g = compact(k, wind)
    need(u == scale(2, g) and all(not any(r[:9]) for r in m[9:]), "pulse/uncompute")
    need(mul(tr(g), g) == scale(4, eye(9)), "wrong compact gain")
    return scale(F(1, 4), u)


def addressed(s, m, g, reverse):
    cloud, routes, gain, _ = route_block(s.cloud, m, reverse)
    need(gain == g, "wrong seed multiplicity")
    tickets = {
        (*t, seed): routes[addr, seed]
        for t, addr in s.tickets.items()
        for seed in range(gain)
    }
    need(
        len(tickets) == gain * len(s.tickets) == len(set(tickets.values()))
        and set(tickets.values()) == pairs(cloud),
        "lost or double-counted a descendant",
    )
    return Stock(cloud, tickets)


def relabel(s, f):
    cloud = tuple((f(i), z) for i, z in s.cloud)
    need(pairs(cloud) == pairs(s.cloud), "relabeling merged independent paths")
    return Stock(cloud, s.tickets)


def pulse(s, k, wind, reverse, record=False):
    need(all(i in range(9) for i, _ in s.cloud), "second input path was not blank")
    middle = addressed(s, splitter(k), 4, reverse)
    middle = relabel(
        middle, lambda i: twist(i, wind) + (18 * (i // 9) if record else 0)
    )
    histories = 2 if record else 1
    result = addressed(middle, splitter(k, histories), 4, reverse)
    need(all(i % 18 < 9 for i, _ in result.cloud), "lower output was not empty")
    out = relabel(result, lambda i: 9 * (i // 18) + i % 18)
    if record:
        for t, addr in out.tickets.items():
            need(
                outcome(out, addr) // 9
                == outcome(middle, middle.tickets[t[:-1]]) // 18,
                "old which-branch tag changed",
            )
    return out


def operational():
    # Before pulsing: one of the old trine eigenstates, with no selected branch.
    source = independent(edge(1), edge(0))
    need(len(source.tickets) == 4, "not two independent two-ticket edges")
    old = observed_table()
    for k, a in LABELS:
        need(
            sum(abs(2 * old[k, a, l, 0] - 1) for l in (0, K)) <= 1,
            "old convex hull bound failed at a vertex",
        )
    for rev in (False, True):
        for wind, plus in ((1, 504), (-1, 72), (0, 288)):
            s = pulse(source, 0, wind, rev)
            g = addressed(source, compact(0, wind), 4, rev)
            need(
                signed_vector(s, 9) == tuple(2 * x for x in signed_vector(g, 9)),
                "compact circuit is not the same ray; seed counts must still differ",
            )
            _, counts = extend(s, K, 1, reverse=rev)
            need((counts[0, 0], counts[0, 1]) == (plus, 576 - plus), "K holdout")
            _, p = extend(s, 0, 1, reverse=rev)
            need((p[0, 0], p[0, 1]) == (192, 64), "data-axis expectation changed")
            witness = abs(F(2 * p[0, 0], 256) - 1) + abs(F(2 * plus, 576) - 1)
            need(witness == (F(5, 4) if wind else F(1, 2)), "convex hull witness")
        s = pulse(source, 0, 1, rev, record=True)
        _, recorded = extend(s, K, 2, reverse=rev)
        need(
            tuple(recorded[h, b] for h, b in product(BITS, repeat=2))
            == (216, 216, 72, 72),
            "keeping the branch must erase the K interference",
        )
        # No fresh stock, compression, postselection or address resets between pulses.
        s = pulse(pulse(source, 0, 1, rev), 1, 1, rev)
        _, compound = extend(s, K, 1, reverse=rev)
        two = tuple(compound[0, b] for b in BITS)
        need(
            two == (5472, 3744) and sum(two) == 4 * 16**2 * 9,
            "compound circuit K holdout/count",
        )
        if not rev:
            first = two
        else:
            need(two == first, "reversed matching changed compound result")
    return first


def neutral(m):
    """Restrict a rail map to W; rows/columns sum to zero, top 2x2 determine it."""
    basis = ((1, 0, -1), (0, 1, -1))
    cols = []
    for x, y in product(basis, repeat=2):
        v = act(m, outer(x, y))
        need(all(sum(v[3 * j : 3 * j + 3]) == sum(v[j::3]) == 0 for j in D), "left W")
        cols.append(tuple(v[j] for j in (0, 1, 3, 4)))
    return tr(cols)


def algebra():
    i4 = eye(4)
    c = neutral(columns(9, 9, lambda i: ((3 * (i // 3) + (i + 1) % 3, 1),)))
    c2 = mul(c, c)
    refl = transposition(0)
    flip = neutral(columns(9, 9, lambda i: ((3 * (i // 3) + refl[i % 3], 1),)))
    need(
        all(c2[i][j] + c[i][j] + i4[i][j] == 0 for i, j in product(range(4), repeat=2)),
        "reference did not induce the quadratic scalar",
    )
    cyc = cycle_paths(1, (1, 1))
    pole = neutral(
        tuple(
            tuple(F(x - y, 3) for x, y in zip(a, b, strict=True))
            for a, b in zip(cyc[:9], cyc[9:], strict=True)
        )
    )
    need(
        mul(flip, mul(c, flip)) == c2 and mul(flip, mul(pole, flip)) == scale(-1, pole),
        "reference reflection must conjugate the winding and exchange pole readings",
    )
    axes = []
    for k in D:
        b = splitter(k)
        axes.append(
            neutral(
                tuple(
                    tuple(F(x - y, 2) for x, y in zip(a[:9], d[:9], strict=True))
                    for a, d in zip(b[:9], b[9:], strict=True)
                )
            )
        )
    # (I+P)-(I-P)=2P from the split currents. Check independent calibration.
    geom = (*axes[:2], pole)

    def inner(a, b):
        return F(trace(mul(a, b)), 4)

    gram = tuple(tuple(inner(a, b) for b in geom) for a in geom)
    need(gram == ((1, F(-1, 2), 0), (F(-1, 2), 1, 0), (0, 0, 1)), "trine/pole metric")

    def coordinates(x):
        h, j, k = (inner(a, x) for a in geom)
        v = ((4 * h + 2 * j) / 3, (2 * h + 4 * j) / 3, k)
        need(
            all(
                sum(v[g] * geom[g][i][j] for g in range(3)) == x[i][j]
                for i, j in product(range(4), repeat=2)
            ),
            "observable not in chart",
        )
        return v

    rotations, pulses = [], []
    for k in (0, 1):
        u = neutral(exact_pulse(k, 1))
        inverse = neutral(exact_pulse(k, -1))
        need(
            inverse == mul(u, u) and mul(u, inverse) == i4 and mul(c, u) == mul(u, c),
            "order/inversion/reference scalar",
        )
        need(
            mul(flip, mul(u, flip)) == inverse
            and mul(flip, mul(axes[k], flip)) == axes[k],
            "winding reversal was not common conjugation with trine fixed",
        )
        # Check the + and - eigenspaces directly, without supplying U to the router.
        for sign, op in ((1, i4), (-1, c)):
            plane = tuple(
                tuple(i4[i][j] + sign * axes[k][i][j] for j in range(4))
                for i in range(4)
            )
            need(mul(u, plane) == mul(op, plane) and trace(plane) == 4, "phase action")
        r = tr(tuple(coordinates(mul(u, mul(a, inverse))) for a in geom))
        need(
            mul(tr(r), mul(gram, r)) == gram
            and mul(r, mul(r, r)) == eye(3)
            and trace(r) == 0
            and tr(r)[k] == eye(3)[k],
            "order-three axial rotation",
        )
        rotations.append(r)
        pulses.append(u)
    raw = mul(pulses[1], pulses[0])
    lift = mul(c2, raw)
    need(
        trace(lift) == F(5, 2) and trace(mul(rotations[1], rotations[0])) == F(9, 16),
        "product traces do not yield the advertised infinite-order witness",
    )


def main():
    algebra()
    two = operational()
    print("edge(1) x edge(0), P0 pulse: 4 source tickets -> 16 split -> 64 uncomputed.")
    print("K+ 504/576 forward, 72/576 reversed, 288/576 bypass; P0+ 192/256.")
    print("Old convex hull |E(P0)|+|E(K)| <= 1; one pulsed preparation: 5/4.")
    print("Recorded arms: K(+,-)=(216,216),(72,72); lower output still blank.")
    print(f"Two uncompressed pulses P0,P1, K(+,-)={two}; both matchings agree.")
    print("Exact axes dot -1/2; product SO(3) trace 9/16, SU(2) scalar 5/8.")
    print(
        "Conditional dense projective rotations in supplied topology; not physical continuity."
    )
    print(
        "Gain per pulse: 16 sequential or 4 compiled; no efficient-resource or QM claim."
    )


if __name__ == "__main__":
    main()
