"""A causal dyadic four-port with one reflected port emulates a tritter at DC.

Use signed coherent real incident signals, the dyadic four-port S4=J/2-I,
a positive mirror and one tick of flight back to the fourth port. These are
supplied resources, not a microscopic unsigned preparation or detector.
An initially dyadic history stays dyadic at every finite tick. For a constant
external input x, the internal incidence t tends to sum(x)/3; the outgoing
signals tend to S3*x. Limit or precharging is essential. Time-resolved
mechanical/signal energy (squared amplitude in the supplied unit-power
leads) and the square of a sum of signed samples are different observables.

The static tree construction below establishes existence of a stationary
solution, not preparation, dynamical convergence, or frequency-independent
scattering. No QM, Born selection, particle interaction or physical
identification of different clocks is asserted.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product


def need(ok, reason):
    if not ok:
        raise ArithmeticError(reason)


def star(x):
    uniform = 2 * sum(x, F(0)) / len(x)
    return tuple(uniform - a for a in x)


def energy(x):
    return sum(a * a for a in x)


def tick(x, t):
    need(len(x) == 3, "three exterior ports")
    result = star((*x, t))
    y, following = result[:3], result[3]
    need(
        following == (sum(x) - t) / 2 and energy(x) + t * t == energy(y) + following**2,
        "mirror recurrence or local energy balance",
    )
    return y, following


ZERO = (F(0),) * 3
UNIT = (F(1), F(0), F(0))


def causal_controls():
    cases = 0
    for x in product(map(F, (-1, 0, 1)), repeat=3):
        ideal, s, t = star(x), sum(x), F(0)
        for n in range(12):
            y, following = tick(x, t)
            error = -s * F(-1, 2) ** n / 6
            need(
                all(v - w == error for v, w in zip(y, ideal, strict=True)),
                "finite transient",
            )
            need(
                all(v.denominator.bit_count() == 1 for v in (*y, following)),
                "non-dyadic tick",
            )
            t = following
            cases += 1
        need(tick(x, s / 3) == (ideal, s / 3), "precharged signed steady solution")
    # Cascading two separate uncharged devices on a single impulse is not an
    # exact instantaneous echo. Conversely, zero-sum inputs excite no internal mode.
    first, _ = tick(UNIT, F(0))
    second, _ = tick(first, F(0))
    need(
        star(star(UNIT)) == UNIT and second == (F(3, 4), F(-1, 4), F(-1, 4)),
        "steady echo mistaken for causal echo",
    )
    # Restrict the very same S4 to exactly two occupied, distinct legs:
    # it complements the four bits. A positive one-tick mirror therefore
    # requires successive exterior populations to alternate between 2 and 1.
    # No prescribed constant exterior bit triple is a valid two-tick drive.
    raw = [z for z in product((0, 1), repeat=4) if sum(z) == 2]
    for z in raw:
        out = star(z)
        need(out == tuple(1 - a for a in z), "single raw packet complement")
        need((*z[:3], out[3]) not in raw, "constant exterior raw packet survived")
        next_populations = {sum(w[:3]) for w in raw if w[3] == out[3]}
        need(next_populations == {3 - sum(z[:3])}, "wrong next raw drive sector")
    return {
        "single_two_mark_packets": len(raw),
        "raw_mirror_drive": "legal successive exterior populations alternate between 1 and 2; the steady signal drive is not a repeatable single raw packet",
        "checked_ticks": cases,
        "two_empty_devices_first_output": list(map(str, second)),
    }


def pulse_energy():
    rows = {}
    for L in (1, 2, 3, 4, 7, 16, 32):
        t, squares, signed = F(0), list(ZERO), list(ZERO)
        for _ in range(L):
            y, t = tick(UNIT, t)
            for i, b in enumerate(y):
                squares[i] += b * b
                signed[i] += b
        # Free evolution multiplies t by -1/2 and emits t/2 on every port.
        # Sum the tails as two DISTINCT geometric series.
        first_tail, t1 = tick(ZERO, t)
        need(t1 == -t / 2 and first_tail == (t / 2,) * 3, "free tail")
        extra_square, extra_signed = (
            (t / 2) ** 2 / (1 - F(1, 4)),
            (t / 2) / (1 + F(1, 2)),
        )
        need(
            extra_square == t * t / 3 and extra_signed == t / 3,
            "stored tail allocation",
        )
        squares = tuple(v + extra_square for v in squares)
        signed = tuple(v + extra_signed for v in signed)
        residue = 1 - F(-1, 2) ** L
        expect = (
            F(L, 9) + F(4, 27) * residue,
            *([F(4 * L, 9) - F(2, 27) * residue] * 2),
        )
        need(
            squares == expect and sum(squares) == L,
            "all-time energy of a rectangular drive",
        )
        need(
            signed == tuple(L * b for b in star(UNIT)), "all-time signed amplitude sum"
        )
        if L == 1:
            need(squares == (F(1, 3),) * 3, "impulse energy is not steady weights")
        rows[L] = {
            "total_energy_shares": [str(v / L) for v in squares],
            "energy_per_port_after_source_stops": str(extra_square),
        }
    return rows


# Gaussian rational pairs are only calculators for harmonic data.
def cmul(z, w):
    return (z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0])


def cdiv(z, w):
    n = w[0] ** 2 + w[1] ** 2
    a, b = cmul(z, (w[0], -w[1]))
    return (F(a) / n, F(b) / n)


def harmonic():
    # z is a unit delay multiplier: t=z*(sum(x)-t)/2.
    # b_i=-a_i+C*sum(a); C=(1+z)/(2+z). The common-mode eigenvalue
    # is 3C-1=(1+2z)/(2+z): all-pass does not mean zero delay.
    for v in map(F, ("0", "1/5", "1/2", "1", "2", "7")):
        z = ((1 - v * v) / (1 + v * v), -2 * v / (1 + v * v))
        C = cdiv((1 + z[0], z[1]), (2 + z[0], z[1]))
        need(
            C == cdiv((2, 0), (3, v)),
            "formal equal-site spring coefficient, v=tan(q/2)",
        )
        eigen = (3 * C[0] - 1, 3 * C[1])
        need(eigen[0] ** 2 + eigen[1] ** 2 == 1, "propagating loss")
        need((cmul(eigen, eigen) == (1, 0)) == (v == 0), "harmonic echo")
    # z=-1: the steady alternating common mode has t=-sum(x), b=-x.
    y, t = tick(UNIT, F(-1))
    need(y == tuple(-a for a in UNIT) and t == 1, "alternating-drive phase")
    need(tick(tuple(-a for a in UNIT), t) == (UNIT, F(-1)), "alternating drive return")
    return {
        "zero_frequency": "S3",
        "alternating_drive": "-I",
        "formal_identity": "z=exp(-iq): C=2/(3+i*tan(q/2)); the delay phase and elastic lattice wavenumber are not the same physical frequency. Fourier sign and clock must be specified separately; free evolution is not identical.",
    }


def static_tree(parents, drives):
    """Parents precede children; unused physical ports get stationary positive mirrors."""
    n, d = len(parents), len(drives)
    need(
        n and d and parents[0] == -1 and all(0 <= parents[j] < j for j in range(1, n)),
        "rooted tree with parent-before-child numbering",
    )
    degrees = [0] * n
    for j in range(1, n):
        degrees[j] += 1
        degrees[parents[j]] += 1
    need(max(degrees) <= 4, "overfilled four port")
    slots = [i for i, deg in enumerate(degrees) for _ in range(4 - deg)]
    need(d <= len(slots), "too many exterior names")
    phi = 2 * sum(drives, F(0)) / d
    # At each port a+b=phi and current into vertex = a-b. Internal
    # endpoints have opposite currents; a stationary positive cap has zero.
    ports, subtotal = [[] for _ in parents], [F(0)] * n
    for k, node in enumerate(slots):
        a = drives[k] if k < d else phi / 2
        ports[node].append((a, phi - a))
        subtotal[node] += 2 * a - phi
    for j in reversed(range(1, n)):
        p, flow = parents[j], subtotal[j]
        a, b = (phi - flow) / 2, (phi + flow) / 2
        ports[j].append((a, b))
        ports[p].append((b, a))
        subtotal[p] += flow
    need(subtotal[0] == 0, "static boundary flux")
    for pairs in ports:
        ins, outs = zip(*pairs, strict=True)
        need(
            len(pairs) == 4 and star(ins) == outs,
            "constructed flows do not solve local S4",
        )
    return tuple(phi - a for a in drives)


def static_controls():
    cases = 0
    for p in ([-1], [-1, 0], [-1, 0, 1], [-1, 0, 0, 0, 0], [-1, 0, 0, 1, 1, 2]):
        for d in range(1, 2 * len(p) + 3):
            for i in range(d):
                x = tuple(F(k == i) for k in range(d))
                need(static_tree(p, x) == star(x), "external static map")
                cases += 1
    # A path of n four-ports has 2n+2 exterior sockets: any fixed finite
    # arity can be made by increasing n and capping the spare sockets.
    # Complementary cap states at a single four-port need not decay at all.
    a = (F(0), F(0), F(1), F(-1))
    need(
        star(a) == tuple(-v for v in a) and star(star(a)) == a,
        "hidden alternating caps",
    )
    return {
        "static_basis_tests": cases,
        "countercontrol": "two positive unit-delay caps circulate opposite signs forever with no outgoing signal; existence of a steady state does not prepare every internal state",
    }


def probe():
    return {
        "causal": causal_controls(),
        "finite_rectangles": pulse_energy(),
        "harmonic": harmonic(),
        "static_trees": static_controls(),
        "boundary": "signed coherent dyadic contact plus feedback, flight time, mirror, and specified readout; no finite-time general division by three or unforced physical event mechanism",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
