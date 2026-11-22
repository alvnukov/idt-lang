"""Exact calibration and repeated-path holdout for two supplied readouts.

Independently openable labels contribute by coherent group addition before a
single unnormalized readout. A copied path has the same value but a separate
shutter. The gain 1/4 is fixed for the two bounded trials only; it is not a
normalization rule. Neither addition nor the detector is derived here.
"""

from collections.abc import Callable, Sequence
from fractions import Fraction
from itertools import product
from math import gcd
from typing import TypeVar

State = TypeVar("State")
Vector = tuple[int, int]
ZERO: Vector = (0, 0)
A: Vector = (1, 0)
B: Vector = (0, 1)
C: Vector = (-1, -1)
GAIN = Fraction(1, 4)
TORUS_MODULUS = 17
TORUS_MAX_LENGTH = 6


def check(condition: bool, message: str) -> None:
    """Keep the probe's checks active under python -O."""
    if not condition:
        raise AssertionError(message)


def add(left: Vector, right: Vector) -> Vector:
    return left[0] + right[0], left[1] + right[1]


def residue(vector: Vector, modulus: int) -> Vector:
    return vector[0] % modulus, vector[1] % modulus


def add_mod2(left: Vector, right: Vector) -> Vector:
    return residue(add(left, right), 2)


def rotate(vector: Vector) -> Vector:
    """The lattice 120-degree map: a -> b -> c -> a."""
    x, y = vector
    return -y, x - y


def lattice_weight(vector: Vector) -> int:
    x, y = vector
    return x * x - x * y + y * y


def modular_weight(vector: Vector) -> int:
    return int(residue(vector, 2) != ZERO)


def shutter_table(
    paths: Sequence[State],
    combine: Callable[[State, State], State],
    readout: Callable[[State], int],
    zero: State,
) -> tuple[int, ...]:
    """Bit i opens label i; repeated contributions retain separate bits."""
    sums = [zero]
    for path in paths:
        sums += [combine(total, path) for total in sums]
    return tuple(readout(total) for total in sums)


def i2(weights: Sequence[int]) -> int:
    return weights[3] - weights[1] - weights[2] + weights[0]


def i3(weights: Sequence[int]) -> int:
    return (
        weights[7]
        - weights[3]
        - weights[5]
        - weights[6]
        + weights[1]
        + weights[2]
        + weights[4]
        - weights[0]
    )


def check_trial(
    label: str,
    paths: tuple[Vector, Vector, Vector],
    expected_lattice: tuple[int, ...],
    expected_modular: tuple[int, ...],
    expected_i3: tuple[int, int],
) -> None:
    lattice = shutter_table(paths, add, lattice_weight, ZERO)
    modular = shutter_table(paths, add_mod2, modular_weight, ZERO)
    check(lattice == expected_lattice and modular == expected_modular, label)
    for table in (lattice, modular):
        check(all(0 <= GAIN * weight <= 1 for weight in table), "gain outside bounds")
        check(i2(table) == -1, "unexpected I2(a,b)")
    raw_i3 = i3(lattice), i3(modular)
    check(raw_i3 == expected_i3, "unexpected third-order difference")
    print(f"{label}, masks 0..7: lattice {list(lattice)}; modular {list(modular)}")
    print(
        f"  I2(a,b) raw = -1 in both; I3 raw = {raw_i3}; "
        f"I3 at gain {GAIN} = ({GAIN * raw_i3[0]}, {GAIN * raw_i3[1]})"
    )


def check_cyclic_group(modulus: int) -> int:
    """Check every ternary readout, including nonzero baseline values."""

    def cyclic_add(left: int, right: int) -> int:
        return (left + right) % modulus

    setups: list[tuple[int, tuple[tuple[int, ...], ...]]] = []
    for a, b in product(range(modulus), repeat=2):
        order = modulus // gcd(a, modulus)
        masks = tuple(
            shutter_table((a, b, k * a % modulus), cyclic_add, int, 0)
            for k in range(order)
        )
        setups.append((order, masks))

    count = 0
    for weights in product(range(3), repeat=modulus):
        for order, masks in setups:
            first = tuple(weights[index] for index in masks[0])
            second = i2(first)
            thirds = [i3(tuple(weights[index] for index in table)) for table in masks]
            check(thirds[0] == 0, "zero third path failed to cancel")
            check(sum(thirds) == -order * second, "telescoping identity failed")
            check(
                (order - 1) * max(map(abs, thirds)) >= order * abs(second),
                "finite-order lower bound failed",
            )
        count += 1
    return count


def check_cyclic_weights() -> int:
    """Let F(t)=W(t+b)-W(t) and D(t)=F(t+a)-F(t).

    I2(a,b)=D(0), and I3(a,b,t)=D(t)-D(0). Summing over t=k*a
    telescopes for any finite order n since n*a=0. The k=0 term of I3
    vanishes, which gives the bound with n-1, not n. The census below
    is a replay of this algebra, not evidence about an unknown order.
    """
    base = shutter_table((1, 1, 1), lambda x, y: (x + y) % 2, int, 0)
    offset = 2
    shifted = tuple(weight + offset for weight in base)
    check(shifted[0] == offset, "missing nonzero baseline control")
    check(i2(shifted) == i2(base) == -2, "I2 lost baseline cancellation")
    check(i3(shifted) == i3(base) == 4, "I3 lost baseline cancellation")
    return sum(check_cyclic_group(modulus) for modulus in range(1, 7))


def torus_weight(vector: Vector, modulus: int = TORUS_MODULUS) -> int:
    """Minimum of Q over lattice lifts of this residue, with an exact cutoff.

    A centered lift has max coordinate magnitude <= M/2, hence Q <= 3M²/4.
    For every lift Q >= (3/4) max(|x|,|y|)^2, by completing the square in
    either coordinate. Thus every candidate outside [-M,M]^2 is worse.
    """
    if modulus < 1:
        raise ValueError("modulus must be positive")
    x, y = residue(vector, modulus)
    return min(
        lattice_weight((u, v))
        for u in range(x - modulus, modulus + 1, modulus)
        for v in range(y - modulus, modulus + 1, modulus)
    )


def check_torus() -> int:
    """Check every sum of up to K signed unit steps and all C3 residue orbits.

    The norm sqrt(Q) obeys the triangle inequality. Distinct lifts differ by
    a nonzero M-multiple, which has norm at least M because Q is positive
    integral on nonzero integer vectors. If two lifts have norm <= K, their
    distance is <= 2K < M, impossible. Thus a reachable lift is the unique
    minimum, even against candidates that are not reachable by K steps.
    """
    modulus, steps = TORUS_MODULUS, TORUS_MAX_LENGTH
    check(2 * steps < modulus, "the no-wrap window is not certified")
    directions = (A, B, C, (-1, 0), (0, -1), (1, 1))
    check(all(lattice_weight(unit) == 1 for unit in directions), "not unit steps")
    for vector in product(range(modulus), range(modulus)):
        rotated = rotate(vector)
        check(rotate(rotate(rotated)) == vector, "rotation is not C3")
        check(torus_weight(vector) == torus_weight(rotated), "torus lost C3 symmetry")

    reachable = frontier = {ZERO}
    for _ in range(steps):
        frontier = {add(vector, unit) for vector in frontier for unit in directions}
        reachable |= frontier
    check(len(reachable) == 1 + 3 * steps * (steps + 1), "missing window sums")
    check(
        len({residue(vector, modulus) for vector in reachable}) == len(reachable),
        "residue collision within the window",
    )
    for vector in reachable:
        weight = lattice_weight(vector)
        check(weight <= steps**2, "reachable lift exceeds the norm bound")
        check(weight == lattice_weight(rotate(vector)), "lattice lost C3 symmetry")
        check(torus_weight(vector) == weight, "torus and lattice differ in the window")
    wrap = (modulus, 0)
    check(torus_weight(wrap) == 0 and lattice_weight(wrap) == modulus**2, "no wrap")
    return len(reachable)


def main() -> None:
    check((rotate(A), rotate(B), rotate(C)) == (B, C, A), "wrong generator cycle")
    check(
        all(
            modular_weight(vector) == modular_weight(rotate(vector))
            for vector in product(range(2), range(2))
        ),
        "modular readout lost C3 symmetry",
    )
    print("Supplied coherent addition and a single unnormalized readout.")
    check_trial(
        "calibration (a,b,c)",
        (A, B, C),
        (0, 1, 1, 1, 1, 1, 1, 0),
        (0, 1, 1, 1, 1, 1, 1, 0),
        (0, 0),
    )
    check_trial(
        "holdout (a,b,a')",
        (A, B, A),
        (0, 1, 1, 1, 1, 4, 1, 3),
        (0, 1, 1, 1, 1, 0, 1, 1),
        (0, 2),
    )
    count = check_cyclic_weights()
    print(
        "finite-order identity: sum_k I3(a,b,k*a) = -n I2(a,b); "
        "(n-1) max_k |I3| >= n |I2|."
    )
    print(f"  Checked {count} ternary readouts on C_1..C_6, with W(0) fixed per map.")
    reachable = check_torus()
    print(
        f"finite torus control: modulo {TORUS_MODULUS}, C3-invariant and agrees on "
        f"all {reachable} sums of up to {TORUS_MAX_LENGTH} signed unit steps."
    )
    print(
        f"  At {TORUS_MODULUS} copies of a, raw lattice weight "
        f"{TORUS_MODULUS**2} vs torus weight 0."
    )
    print("The holdout separates these two readouts, not finite carriers in general.")


if __name__ == "__main__":
    main()
