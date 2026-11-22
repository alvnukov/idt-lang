"""Conditional exact reachability of an ideal measure-and-repeat architecture.

From paired-rail T/i, blank coordinate ancillas, coherent path control and
fine computational ancilla readout, unnormalized finite branch operators
are Gaussian dyadic. A protocol realizing a unitary channel must give that
same unitary up to a scalar at every refined nonzero terminal leaf (Kraus
rank one). Thus one such leaf requires entry ratios in Q(i), even for
almost-sure finite termination with no bound on termination time.

Clear a projectively Gaussian-rational unitary's denominators and cancel the
Gaussian gcd of ALL entries. The primitive integer representative B obeys
B*B=m I (here * means adjoint), with integer m>0. A dyadic leaf proportional
to B is cB with c in R=Z[i,1/2], by the Bezout identity for its entries.
A finite complete tree would give m sum |c|^2=1, so m must be a power of
two. Conversely B/(1+i)^k is a native unitary if m=2^k.

With possible repetition, pad the isometry [B; u I; v I]/(1+i)^k
using |u|^2+|v|^2=2^k-m from a four-square certificate, k=ceil(log2 m).
The success probability m/2^k is >1/2; all nonzero failures act as the
identity on data up to a scalar. Thus finite expected attempts <2 suffice
for every projectively Gaussian-rational unitary, not a finite worst case.
These are statements inside a *supplied* exact instrument model.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.gaussian_dyadic_words import (
    ONE,
    PI,
    ZERO,
    Gaussian,
    Matrix,
    eye,
    g,
    run,
    synthesize_isometry,
)
from scripts.probe_exact_charge_sector_wall import four_squares, unit_power


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def quotient(a: Gaussian, b: Gaussian) -> Gaussian:
    if b == ZERO:
        raise ZeroDivisionError
    t = a * b.star()
    return g(t.re / b.norm2(), t.im / b.norm2())


def primitive(a: Matrix) -> tuple[Matrix, int]:
    """One primitive integral presentation; its positive norm ignores units."""
    n = len(a)
    if not n or any(len(row) != n for row in a):
        raise ValueError("expected a nonempty square presentation")
    d = lcm(
        *(x for row in a for z in row for x in (z.re.denominator, z.im.denominator))
    )
    b = tuple(tuple(g(d) * z for z in row) for row in a)
    gcd = ZERO
    for row in b:
        for z in row:
            while z != ZERO:
                q = quotient(gcd, z)
                gcd, z = z, gcd - g(round(q.re), round(q.im)) * z
    if gcd == ZERO:
        raise ValueError("zero presentation")
    b = tuple(tuple(quotient(z, gcd) for z in row) for row in b)
    if not all(z.integral() for row in b for z in row):
        raise ArithmeticError("bad Gaussian gcd")
    m = sum((row[0].norm2() for row in b), F(0))
    if (
        not m
        or m.denominator != 1
        or any(
            sum((row[j].star() * row[k] for row in b), ZERO) != g(m if j == k else 0)
            for j, k in product(range(n), repeat=2)
        )
    ):
        raise ValueError("not projectively unitary")
    return b, int(m)


def instrument(a: Matrix) -> tuple[Matrix, tuple[F, F, F], int]:
    """Rows grouped by ancilla outcome, columns span the arbitrary data input."""
    b, m = primitive(a)
    k = (m - 1).bit_length()
    l, s, t, w = four_squares((1 << k) - m)
    u, v = g(l, s), g(t, w)
    denom = ONE
    for _ in range(k):
        denom = denom * PI
    im = eye(len(b))
    rows = (
        b
        + tuple(tuple(u * x for x in row) for row in im)
        + tuple(tuple(v * x for x in row) for row in im)
    )
    a0 = tuple(tuple(quotient(x, denom) for x in row) for row in rows)
    scale = 1 << k
    probs = F(m, scale), u.norm2() / scale, v.norm2() / scale
    need(sum(probs) == 1 and probs[0] > F(1, 2), "branch completeness or efficiency")
    return a0, probs, m


def diag(entries: tuple[Gaussian, ...]) -> Matrix:
    return tuple(
        tuple(x if j == k else ZERO for k in range(len(entries)))
        for j, x in enumerate(entries)
    )


def spinor(a: Gaussian, b: Gaussian) -> Matrix:
    return ((a, b), (ZERO - b.star(), a.star()))


def check_case(name: str, a: Matrix, expected_m: int) -> None:
    columns, probs, m = instrument(a)
    need(m == expected_m, "primitive norm: " + name)
    word = synthesize_isometry(columns)
    d = len(a)
    seed = tuple(row[:d] for row in eye(3 * d))
    need(run(seed, word) == columns, "native isometry mismatch: " + name)
    for t in (1, 2):
        block = columns[d * t : d * (t + 1)]
        c = block[0][0]
        need(
            block == diag((c,) * d) and c.norm2() == probs[t],
            "disturbing failure: " + name,
        )
    if all(a[j][k] == ZERO for j, k in product(range(d), repeat=2) if j != k):
        need(
            all(j % d == k % d for _, j, k in word),
            "charged instruction crossed data slots",
        )
    bounded = m & (m - 1) == 0
    need(bounded == (probs[0] == 1), "finite vs retry classification")
    print(
        f"{name}: primitive norm {m}; bounded={'yes' if bounded else 'no'}, "
        f"p={probs[0]}, mean trials={1 / probs[0]}, compiled moves={len(word)}"
    )


def main() -> None:
    h = ((ONE, ONE), (ONE, g(-1)))
    m5 = diag((g(2, 1), g(2, -1)))
    z5 = unit_power(g(2, 1), 5)
    charge = diag((z5.star(),) * 3 + (z5,) * 2)
    cases = (
        ("Hadamard ray (no supplied real sqrt(2))", h, 2),
        ("complex mixing norm 3", spinor(g(1, 1), ONE), 3),
        ("diagonal charge relay", m5, 5),
        (
            "same ray after common complex rescaling",
            tuple(tuple(x * g(F(2, 7), F(1, 7)) for x in row) for row in m5),
            5,
        ),
        ("mixing norm 7", spinor(g(2, 1), g(1, 1)), 7),
        (
            "three-slot real reflection",
            tuple(tuple(g(-1 if j == k else 2) for k in range(3)) for j in range(3)),
            9,
        ),
        ("mixing norm 13", spinor(g(3), g(2)), 13),
        ("mixing norm 25", spinor(g(3), g(4)), 25),
        ("five-slot common-phase equivalent to (-2,-2,-2,3,3) action", charge, 3125),
    )
    for name, a, m in cases:
        check_case(name, a, m)
    # For a nonzero Q(i) candidate x=a+ib solving x^2=2, 2ab=0;
    # a=0 is impossible over reals, b=0 would require rational sqrt(2).
    # The real orthogonal rotation with entry ratio sqrt(2) is therefore
    # not exactly reachable by ANY nonzero finite dyadic herald branch.
    print(
        "Outside exact projective class: [[1,-sqrt(2)],[sqrt(2),1]]/sqrt(3). "
        "No finite heralded leaf; this does not rule out approximation."
    )
    print(
        "Ideal ancilla-only readout, coherence, reset, and branch control are inputs. "
        "Mean attempts do not bound worst-case time or native gates per attempt."
    )


if __name__ == "__main__":
    main()
