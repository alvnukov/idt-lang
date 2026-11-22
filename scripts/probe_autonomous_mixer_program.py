"""A fixed-law no-go/positive pair, not a physical autonomous-QCA derivation.

ADDITIVE WALL. Independent direct-sum input (x,p), fixed linear propagation,
time and output give y_p(x)=A*x+b_p. Its odd response is always A*x.
Uniform errors epsilon_p on unit x and -x imply ||A-U_p||<=epsilon_p,
hence ||U_p-U_q||<=epsilon_p+epsilon_q. The midpoint A=(U_p+U_q)/2,
b=0 attains this bound: common error 1 for I/X, 1/sqrt(2) for I/T.
Writing eta_p=||y_p(0)||, the sharp vacuum-controlled inequality is
||U_p*x-U_q*x|| <= epsilon_p(x)+epsilon_q(x)+eta_p+eta_q.
The one-input counterfeit saturates it but fails on -x. This uses a supplied
common amplitude frame, not normalized click tables. Program-dependent
time/readout, postselection or premixing unknown x changes the contract.

ORTHOGONAL PROGRAMS. A fixed isometry implementing U_p with data-independent
output program r_p gives <p|q>I=<r_p|r_q> U_p^dagger U_q. Unitaries not
equivalent up to phase therefore require orthogonal programs. Uniform JOINT
vector errors give operator residual <=epsilon_p+epsilon_q. For I/T,
|<p|q>|<=sqrt(2)*(epsilon_p+epsilon_q), since min_d ||I-d*T||=1/sqrt(2).
This is not an unqualified marginal-channel bound. Superposed enable bits
generally entangle data rather than select a deterministic analog program.

CONDITIONAL POSITIVE RULE. On orthogonal clock/tape configurations use ONE
fixed update, with a binary enable and the same translated native collision:

  |c,p> tensor x -> |c+1, rotate(p)> tensor T_(c,c+1)^(p[0]) x.

Unknown x enters as a product, not a pilot or premixed state. The control
update is a permutation and each data block is unitary: one reversible law,
not a table of desired words. Gates wait for scanned edges; zero bits idle.
At most n ticks per neighboring gate plus cycle padding suffice. T^2 swaps
can first route nonneighboring addresses on a connected graph.

Six ticks give T12*T01 from 110000 and T01*T12 from 010100, with identical
clock/tape return and no postselection. Full matrices for all 64 tapes and
three clock positions cover unknown x. Six orthogonal classical bits are
supplied; general words require growing memory/time and prepared programs.

LOCALITY/STOPPING WALL. Tape rotation is nearest-neighbor in tape geometry.
The indexed data collision and tape registration are NOT automatically a
homogeneous local 1d QCA. Translation covariance is weaker than a spatial
implementation. Joint conditional collision and clock/tape origin remain
supplied; additive pilots cannot build them. Cycles repeat, not halt: a
stable latch/marker/halting history is extra structure. Readout timing,
nonidentity padding, discarded memory and mismatched periods cannot hide.

Finite exact checks and analytic bounds only; no Lean proof, physical
controller, Born rule, tensor origin, or universal-QM claim is made.
Run: python3 -B -O -m scripts.probe_autonomous_mixer_program
"""

import sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    CROSS,
    DIAG,
    ONE,
    ZERO,
    Gaussian,
    Matrix,
    eye,
    g,
    run,
    unitary,
)

Vector = tuple[Gaussian, ...]
Tape = tuple[int, ...]
T: Matrix = ((DIAG, CROSS), (CROSS, DIAG))
X: Matrix = ((ZERO, ONE), (ONE, ZERO))


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), ZERO)
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(value.star() for value in col) for col in zip(*a, strict=True))


def plus(a: Matrix, b: Matrix, factor: Gaussian = ONE) -> Matrix:
    return tuple(
        tuple(x + factor * y for x, y in zip(row, other, strict=True))
        for row, other in zip(a, b, strict=True)
    )


def scaled(factor: Gaussian, a: Matrix) -> Matrix:
    return tuple(tuple(factor * value for value in row) for row in a)


def apply(a: Matrix, x: Vector) -> Vector:
    return tuple(sum((u * v for u, v in zip(row, x, strict=True)), ZERO) for row in a)


def norm2(x: Vector) -> F:
    return sum((value.norm2() for value in x), F(0))


def affine_controls() -> None:
    ident = eye(2)
    minus = scaled(g(F(1, 2)), plus(ident, X, g(-1)))
    for target, square_error in ((X, F(1)), (T, F(1, 2))):
        midpoint = scaled(g(F(1, 2)), plus(ident, target))
        for endpoint in (ident, target):
            residual = plus(midpoint, endpoint, g(-1))
            need(
                mul(adjoint(residual), residual) == scaled(g(square_error), minus),
                "sharp midpoint operator-error Gram",
            )
    midpoint = scaled(g(F(1, 2)), plus(ident, X))
    offsets = ((g(F(1, 2)), g(F(-1, 2))), (g(F(-1, 2)), g(F(1, 2))))
    source = (ONE, ZERO)
    for offset, target in zip(offsets, (ident, X), strict=True):
        output = tuple(
            x + b for x, b in zip(apply(midpoint, source), offset, strict=True)
        )
        need(output == apply(target, source), "single-input affine counterfeit")
        need(norm2(offset) == F(1, 2), "program-only vacuum leakage")
        negative = tuple(g(-1) * value for value in source)
        out_negative = tuple(
            x + b for x, b in zip(apply(midpoint, negative), offset, strict=True)
        )
        need(
            norm2(
                tuple(
                    x - y
                    for x, y in zip(out_negative, apply(target, negative), strict=True)
                )
            )
            == 2,
            "unknown signed input defeats counterfeit",
        )
        need(
            tuple(x - y for x, y in zip(output, out_negative, strict=True))
            == tuple(g(2) * x for x in apply(midpoint, source)),
            "program-independent odd response",
        )
    residual = plus(ident, T, g(F(-1, 2), F(1, 2)))
    need(
        mul(adjoint(residual), residual) == scaled(g(F(1, 2)), ident),
        "I/T no-programming residual minimum attained",
    )
    overlap = apply(T, source)[0]
    need(
        (1 + overlap.norm2()) / 2 == F(3, 4),
        "superposed enable yields a mixed data output, not a chosen pure unitary",
    )


def rotate(tape: Tape) -> Tape:
    return tape[1:] + tape[:1]


def execute(n: int, tape: Tape, ticks: int, start: int = 0) -> tuple[int, Tape, Matrix]:
    need(bool(tape) and all(bit in (0, 1) for bit in tape), "binary nonempty program")
    clock, data = start, eye(n)
    for _ in range(ticks):
        if tape[0]:
            data = run(data, (("T", clock, (clock + 1) % n),))
        clock, tape = (clock + 1) % n, rotate(tape)
    return clock, tape, data


def fixed_rule_controls() -> int:
    tapes = tuple(product((0, 1), repeat=6))
    controls = tuple(product(range(3), tapes))
    images = {((clock + 1) % 3, rotate(tape)) for clock, tape in controls}
    need(len(images) == len(controls), "one fixed reversible control-label permutation")
    for clock, tape in controls:
        final_clock, final_tape, data = execute(3, tape, 6, clock)
        need(
            (final_clock, final_tape) == (clock, tape) and unitary(data),
            "all six-tick programs return independent memory and act unitarily",
        )
    ab, ba = (1, 1, 0, 0, 0, 0), (0, 1, 0, 1, 0, 0)
    out_ab, out_ba = execute(3, ab, 6)[2], execute(3, ba, 6)[2]
    need(out_ab == run(eye(3), (("T", 0, 1), ("T", 1, 2))), "unknown-input AB word")
    need(out_ba == run(eye(3), (("T", 1, 2), ("T", 0, 1))), "unknown-input BA word")
    need(
        out_ab != out_ba and execute(3, (0,) * 6, 6)[2] == eye(3),
        "distinct programs and true idle padding",
    )
    need(
        execute(3, ab, 12)[2] == mul(out_ab, out_ab),
        "cycle repeats the word instead of halting",
    )
    short = (1, 0, 0, 0)
    need(
        execute(3, short, 4)[:2] == (1, short),
        "tape return alone does not return the scanner",
    )
    need(
        execute(3, (1, 1, 1, 0, 0, 0), 6)[2] != out_ab,
        "nonidentity padding changes the data word",
    )
    return len(controls)


def locality_controls() -> None:
    for position in range(6):
        tape = tuple(int(i == position) for i in range(6))
        shifted = rotate(tape)
        need(
            shifted == tuple(int(i == (position - 1) % 6) for i in range(6)),
            "tape permutation moves each bit one local step",
        )
        need(shifted[-1:] + shifted[:-1] == tape, "local inverse tape permutation")
    translation = tuple(
        tuple(ONE if i == (j + 1) % 3 else ZERO for j in range(3)) for i in range(3)
    )
    for clock in range(3):
        here = run(eye(3), (("T", clock, (clock + 1) % 3),))
        there = run(eye(3), (("T", (clock + 1) % 3, (clock + 2) % 3),))
        need(
            mul(translation, here) == mul(there, translation),
            "clock/data translation covariance, not a full spatial-QCA proof",
        )


def main() -> None:
    affine_controls()
    count = fixed_rule_controls()
    locality_controls()
    print(
        "Additive pilot wall: program-independent odd response; sharp I/X error 1 and I/T error 1/sqrt(2); exact one-input counterfeit leaks squared vacuum norm 1/2."
    )
    print(
        f"Fixed binary scanner: {count} exact six-tick programs checked; 110000 gives T12*T01, 010100 gives T01*T12, clock and tape returned."
    )
    print(
        "Orthogonal joint configurations, not additive pilot amplitudes; superposed enable gives data purity 3/4 on the control input."
    )
    print(
        "Tape shift is a local reversible permutation; translation covariance is checked, but a complete homogeneous spatial QCA is NOT supplied."
    )
    print(
        "Program preparation, joint conditional collision, growing memory/time, and common-cycle readout remain assumptions; cycles repeat rather than halt."
    )


if __name__ == "__main__":
    main()
