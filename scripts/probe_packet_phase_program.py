"""Heralded charge-preserving phase program for the six-packet candidate.

This addresses the missing continuous *control*, not the origin of charge or
of quantum mechanics. The data carry six packet amplitudes indexed by C3 x C2.
Only controlled permutations preserving their complement act on the data.
Grouped projective instruments, a neutral coherent program, tensor addresses,
paired-rail logical instructions and classical retry/reset are supplied.
The finite matrices below use Gaussian rationals only. No continuously
variable phase or irrational Fourier gate is provided to the compiler.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import ONE, ZERO, Gaussian, Matrix, eye, g, unitary
from scripts.probe_native_rational_pentagon import Retry, add, multiply, retry, scale

Z = g(F(3, 5), F(4, 5))
LABELS = range(6)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def translate(h: int, x: int) -> int:
    return 2 * ((h // 2 + x // 2) % 3) + ((h ^ x) & 1)


def inverse(h: int) -> int:
    return 2 * ((-(h // 2)) % 3) + (h & 1)


def projectors() -> tuple[Matrix, Matrix, Matrix]:
    identity = eye(6)
    flip = tuple(identity[i ^ 1] for i in LABELS)
    uniform = tuple((g(F(1, 6)),) * 6 for _ in LABELS)
    minus = scale(add(identity, scale(flip, g(-1))), g(F(1, 2)))
    plus = add(scale(add(identity, flip), g(F(1, 2))), scale(uniform, g(-1)))
    return uniform, minus, plus


def from_phases(a: Gaussian, b: Gaussian) -> Matrix:
    uniform, minus, plus = projectors()
    return add(uniform, add(scale(minus, a), scale(plus, b)))


def sandwich(w: Matrix, coefficients: tuple[Gaussian, ...]) -> tuple[Matrix, ...]:
    """Each final program row is a data map; omit shared input normalization."""
    # SELECT, W on the program alone, then the inverse SELECT. For input port
    # x/output y and program row h, the unique old address is l = h+y-x.
    return tuple(
        tuple(
            tuple(
                w[h][ell] * coefficients[ell]
                for x in LABELS
                for ell in (translate(translate(h, y), inverse(x)),)
            )
            for y in LABELS
        )
        for h in LABELS
    )


def phase_action() -> tuple[Matrix, Matrix, Matrix]:
    wm, wp = from_phases(Z.star(), ONE), from_phases(ONE, Z)
    y = from_phases(Z.star() * Z.star(), Z * Z * Z)
    need(all(unitary(w) for w in (wm, wp, y)), "nonunitary phase")
    word = eye(6)
    for w in (wm, wm, wp, wp, wp):
        word = multiply(w, word)
    need(word == y, "wrong phase exponents")
    for w in (wm, wp, y):
        need(sandwich(w, (ONE,) * 6) == (w,) * 6, "program did not return unchanged")
    for h, x in product(LABELS, repeat=2):
        need(translate(h, x ^ 1) == translate(h, x) ^ 1, "charge leakage")
    return wm, wp, y


def verify_failures(instrument: Retry) -> None:
    for j, scalar in enumerate(instrument.failures, 1):
        block = instrument.columns[6 * j : 6 * (j + 1)]
        unchanged = scale(eye(6), scalar)
        need(block == unchanged, "program-address-dependent failure")
        # Scalar I tensor I commutes through both SELECT maps: this is an
        # operator identity on entangled inputs, not a marginal probability.
        need(sandwich(block, (ONE,) * 6) == (unchanged,) * 6, "reset leaked charge")


def controls(y: Matrix) -> None:
    need(Z.norm2() == 1 and (Z + Z.star()).re.denominator != 1, "torsion test")
    need(any(not v.dyadic() for row in y for v in row), "finite dyadic word escape")
    wrong = sandwich(y, (ONE,) + (ZERO,) * 5)
    need(wrong != (y,) + (scale(eye(6), ZERO),) * 5, "which-address preparation")
    # Reading the initial path and forgetting the answer produces a mixture of
    # single translations at the data output. The off-diagonal of an axis
    # preparation is then zero, whereas the ideal phase has a coherent column.
    for h, row in enumerate(wrong):
        need(sum(row[j][0] != ZERO for j in LABELS) <= 1, f"nonclassical branch {h}")
    need(y[0][0] * y[1][0].star() != ZERO, "no distinguishing off-diagonal")
    # Hypercharge is NOT selected by this programming trick. One freely chosen
    # sector phase leaves the other unchanged and generally rotates volume.
    rival = from_phases(ONE, Z)
    need(sandwich(rival, (ONE,) * 6) == (rival,) * 6 and Z * Z != ONE, "overselection")


def main() -> None:
    wm, wp, y = phase_action()
    controls(y)
    rm, rp = retry((wm,)), retry((wp,))
    for instrument in (rm, rp):
        verify_failures(instrument)
    need((rm.success, rp.success) == (F(25, 32), F(225, 256)), "retry fractions")
    print(
        "Six-packet phase: SELECT / program / inverse SELECT returns the uniform program on all 36 data matrix entries per output branch; translations preserve complement."
    )
    print(
        f"Finite compiled program factors: probabilities {rm.success}, {rp.success}; paired-rail mixer counts {rm.physical_mixers}, {rp.physical_mixers} per isolated program attempt."
    )
    print(
        f"Two minus and three plus successful factors: mean {2 / rm.success + 3 / rp.success} program attempts after offline preparation (six of eight coherent paths accepted with p=3/4)."
    )
    print(
        "z=(3+4i)/5 has infinite order; the ideal retry semantics generates a dense circle, not every point at finite depth. Incorrect/read program controls fail. Independent sector phases also work."
    )
    print(
        "Grouped readout, neutral resettable tensor register, control/addressing, complex amplitudes, and the traceless choice are supplied. No local gauge law or physical charges derived."
    )


if __name__ == "__main__":
    main()
