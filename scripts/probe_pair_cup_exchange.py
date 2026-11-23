"""Pair creation, port-index interchange and exchange holonomy are different operations.

Finite comparator, not a model of spacetime. Supply two ordered internal
complex modules, diagonal binary tetrahedral rotations, a coherent source
cup and its matched cap. Designate the binary center as the record of a
full frame turn (not a derived geometric 2pi). The putative identical-leg
exchange is eta times the tensor-index swap, eta=+1 or -1. Neutrality means
invariance under the supplied diagonal action; no electric charge is used.
Gaussian rational arithmetic is integer-pair arithmetic on doubled matrices.

Unlike a hard-core Y-loop, kinetic path sum or collective Pauli test, this
compares a returning pair to the SAME vacuum channel. The internal swap
eigenvalue tau of an invariant cup is observable in this model only combined
with a specified implementation of exchange. A closed-loop phase needs a
coherent reference arm; the bare return intensity loses its sign. An
unoriented, same-complete-mode local source unchanged by physically
interchanging its legs is an ADDITIONAL sewing relation, not a consequence
of the group, a vacuum label, charge neutrality, or cup/cap adjointness.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import product


def need(ok, why):
    if not ok:
        raise ArithmeticError(why)


# Unit quaternions, encoded as twice their four real components.
ONE = (2, 0, 0, 0)
CENTER = (-2, 0, 0, 0)
AXES = tuple(tuple(2*int(i == j) for i in range(4)) for j in range(1, 4))
GROUP = (*[tuple(s*2*int(i == j) for i in range(4)) for s, j in product((-1, 1), range(4))],
         *product((-1, 1), repeat=4))


def mul(q, p):
    a, b, c, d = q
    e, f, g, h = p
    double = (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g, a*g+c*e+d*f-b*h, a*h+d*e+b*g-c*f)
    need(all(v % 2 == 0 for v in double), "lost quaternion group lattice")
    return tuple(v//2 for v in double)


def conjugate(q):
    return q[0], -q[1], -q[2], -q[3]


def doublet(q):
    a, b, c, d = q
    return (((a, b), (c, d)), ((-c, d), (a, -b)))


def vector(q):
    images = [mul(mul(q, t), conjugate(q)) for t in AXES]
    return tuple(tuple((v[i], 0) for v in images) for i in range(1, 4))


def scalar(_q):
    return (((2, 0),),)


def realified_doublet(q):
    # Different tensor product: regard the same transformations as acting
    # on four real coordinates. A complex entry a+ib acts by [[a,-b],[b,a]].
    u = doublet(q)
    def entry(i, j):
        a, b = u[i//2][j//2]
        return (a if i % 2 == j % 2 else b if i % 2 else -b), 0
    return tuple(tuple(entry(i, j) for j in range(4)) for i in range(4))


def gm(z, w):
    a, b = z
    c, d = w
    return a*c-b*d, a*d+b*c


def gsum(zs):
    real = imag = 0
    for a, b in zs:
        real += a
        imag += b
    return real, imag


def tensor_dims(rep):
    # Averaging U tensor U projects onto invariant cups. That projector
    # commutes with swap P; trace and swap-trace give +/- dimensions. Compute
    # both traces directly from actual doubled matrix entries, not spin labels.
    tr, ps = [], []
    for q in GROUP:
        u = rep(q)
        n = len(u)
        tr.extend(gm(u[i][i], u[j][j]) for i, j in product(range(n), repeat=2))
        ps.extend(gm(u[i][j], u[j][i]) for i, j in product(range(n), repeat=2))
    (a, b), (c, d) = gsum(tr), gsum(ps)
    den = 8*len(GROUP)
    need(b == d == 0 and (a+c) % den == (a-c) % den == 0, "nonintegral invariant multiplicities")
    return (a+c)//den, (a-c)//den


def copies(rep, m):
    def result(q):
        u = rep(q)
        return tuple(tuple(u[i//m][j//m] if i % m == j % m else (0, 0) for j in range(m*len(u)))
                     for i in range(m*len(u)))
    return result


def kron(a, b):
    return tuple(tuple(x*y for x in ar for y in br) for ar in a for br in b)


def flip(cup):
    return tuple(zip(*cup, strict=True))


def scale(s, x):
    return tuple(tuple(s*v for v in row) for row in x)


def dot(x, y):
    return sum(a*b for u, v in zip(x, y, strict=True) for a, b in zip(u, v, strict=True))


def invariant(u, cup):
    n = len(u)
    return all(gsum(gm(gm(u[i][a], u[j][b]), (cup[a][b], 0)) for a, b in product(range(n), repeat=2))
               == (4*cup[i][j], 0) for i, j in product(range(n), repeat=2))


def framed_characters():
    # Two independent order-two frame-turn records and a port swap which
    # interchanges them. No braid topology or locality relation is assumed.
    states = tuple(product(range(2), repeat=3))
    def compose(s, t):
        a, b, sw = s
        c, d, u = t
        return (a ^ (d if sw else c), b ^ (c if sw else d), sw ^ u)
    signs = set()
    for choice in product((-1, 1), repeat=7):
        chi = dict(zip(states, (1, *choice), strict=True))
        if all(chi[compose(s, t)] == chi[s]*chi[t] for s, t in product(states, repeat=2)):
            need(chi[1, 0, 0] == chi[0, 1, 0], "single-leg rotations must be conjugate")
            signs.add((chi[1, 0, 0], chi[0, 0, 1]))
    need(signs == set(product((-1, 1), repeat=2)), "exchange and turn were tied without a relator")
    return sorted(signs)


def probe():
    need(len(set(GROUP)) == 24 and all(mul(q, conjugate(q)) == ONE for q in GROUP), "invalid rotation group")
    for q, p in product(GROUP, repeat=2):
        z = mul(q, p)
        need(z in GROUP, "group not closed")
        for rep in (doublet, vector):
            a, b, c = rep(q), rep(p), rep(z)
            for i, j in product(range(len(a)), repeat=2):
                need(gsum(gm(a[i][k], b[k][j]) for k in range(len(a))) == gm((2, 0), c[i][j]),
                     "matrix representation failed")
    eps = ((0, 1), (-1, 0))
    ident = ((1, 0), (0, 1))
    vec = tuple(tuple(int(i == j) for j in range(3)) for i in range(3))
    need(all(mul(a, a) == CENTER for a in AXES), "half-turn lifts")
    models = (
        ("single_complex_doublet", doublet, eps, -1, -1, (0, 1)),
        ("single_vector", vector, vec, 1, 1, (1, 0)),
        ("single_scalar", scalar, ((1,),), 1, 1, (1, 0)),
        ("doublet_two_flavors_antisymmetric_flavor", copies(doublet, 2), kron(eps, eps), -1, 1, (1, 3)),
        ("doublet_two_flavors_symmetric_flavor", copies(doublet, 2), kron(eps, ident), -1, -1, (1, 3)),
        ("scalar_two_flavors", copies(scalar, 2), eps, 1, -1, (3, 1)),
        ("same_doublet_as_four_real_coordinates", realified_doublet, kron(ident, ident), -1, 1, (1, 3)),
    )
    rows = []
    for name, rep, cup, turn, tau, expected_dims in models:
        n = len(cup)
        need(rep(CENTER) == tuple(tuple((2*turn*int(i == j), 0) for j in range(n)) for i in range(n)), "center")
        need(tensor_dims(rep) == expected_dims and all(invariant(rep(q), cup) for q in GROUP), "invariant spaces")
        need(flip(cup) == scale(tau, cup) and dot(cup, cup) > 0, "cup exchange parity")
        returns = []
        for eta in (-1, 1):
            exchanged = scale(eta, flip(cup))
            need(scale(eta, flip(exchanged)) == cup, "exchange must square to one")
            ratio = Fraction(dot(cup, exchanged), dot(cup, cup))
            need(ratio == eta*tau and ratio**2 == 1, "normalized cap-after-exchange")
            # Changing the source orientation/sign with a matched cap cannot
            # change the ratio. Equal coherent reference vs inserted operation
            # gives zero or twice the baseline amplitude (not a detector law).
            reversed_cup = flip(cup)
            need(dot(reversed_cup, scale(eta, flip(reversed_cup))) == dot(cup, exchanged), "orientation leakage")
            returns.append({"eta": eta, "exchange_path_ratio": int(ratio), "single_turn_ratio": turn,
                            "reference_plus_exchange_amplitude": 1+int(ratio),
                            "invariant_under_physical_leg_interchange": exchanged == cup})
        rows.append({"model": name, "turn": turn, "internal_swap": tau, "symmetric_and_antisymmetric_cup_dimensions":
                     expected_dims, "returns": returns})
    # V tensor V* also has a neutral identity cup, but swapping its two
    # unlike leg orientations is NOT automatically an endomorphism. Complex
    # tensor neutrality tests U C U^T, not the adjoint/real scalar product.
    need(not invariant(doublet(AXES[0]), ident), "wrongly admitted Hermitian identity in V tensor V")
    for q in GROUP:
        u = doublet(q)
        need(all(gsum(gm(u[i][k], (u[j][k][0], -u[j][k][1])) for k in range(2)) == (4*int(i == j), 0)
                 for i, j in product(range(2), repeat=2)), "identity did not survive in V tensor dual")
    # The rotation-invariant source need not even have a swap parity:
    # independent ordered flavor slots go to an orthogonal flavor ordering.
    tagged = kron(eps, ((0, 1), (0, 0)))
    need(all(invariant(copies(doublet, 2)(q), tagged) for q in GROUP)
         and dot(tagged, flip(tagged)) == 0 and dot(tagged, tagged) > 0, "orthogonally tagged pair control")
    return {"status": "conditional_finite_bilinear_source_and_cap_comparison",
            "framed_turn_exchange_character_pairs": framed_characters(), "models": rows,
            "ordered_flavors_control": {"single_turn_ratio": -1, "return_after_swap_for_either_eta": 0},
            "operational_boundary": "With a calibrated cup parity tau and coherent same-vacuum reference, "
            "the exchange-arm relative sign is eta*tau. A bare squared return cannot distinguish eta. "
            "Any other arm-dependent path phase must be independently controlled.",
            "missing_constraint": "A nonzero co-spatial even-orbital source unchanged under physical interchange "
            "would require eta*tau=+1. In the multiplicity-one examples tau equals the center sign; hidden "
            "flavors defeat the implication. Neither the local-source identity nor complete modes follow here. "
            "No continuum spin-statistics theorem, pair creation in nature or anomaly-free field locality is derived."}


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True))
