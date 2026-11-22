"""Exact addressed word synthesis in paired-port logical coordinates.

The two instructions are the native two-slot mixer T and the local phase i.
On supplied antisymmetric logical rail pairs these use, respectively, two
parallel addressed physical mixers and one within-pair physical mixer.
No acceptance of a preparation, readout, or local gauge principle is implied.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from typing import Literal


@dataclass(frozen=True, slots=True)
class Gaussian:
    re: F
    im: F

    def __add__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.re + other.re, self.im + other.im)

    def __sub__(self, other: Gaussian) -> Gaussian:
        return Gaussian(self.re - other.re, self.im - other.im)

    def __mul__(self, other: Gaussian) -> Gaussian:
        return Gaussian(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def star(self) -> Gaussian:
        return Gaussian(self.re, -self.im)

    def norm2(self) -> F:
        return self.re**2 + self.im**2

    def integral(self) -> bool:
        return self.re.denominator == self.im.denominator == 1

    def dyadic(self) -> bool:
        return all(d & (d - 1) == 0 for d in (self.re.denominator, self.im.denominator))


def g(re: int | F = 0, im: int | F = 0) -> Gaussian:
    return Gaussian(F(re), F(im))


ZERO, ONE, I, PI = g(), g(1), g(0, 1), g(1, 1)
DIAG, CROSS = g(F(1, 2), F(1, 2)), g(F(1, 2), -F(1, 2))
Matrix = tuple[tuple[Gaussian, ...], ...]
Move = tuple[Literal["i", "T"], int, int]


def eye(n: int) -> Matrix:
    return tuple(tuple(ONE if j == k else ZERO for k in range(n)) for j in range(n))


def isometry(a: Matrix) -> bool:
    n = len(a[0]) if a else 0
    return (
        0 < n <= len(a)
        and all(len(row) == n for row in a)
        and all(
            sum((row[j].star() * row[k] for row in a), ZERO)
            == (ONE if j == k else ZERO)
            for j, k in product(range(n), repeat=2)
        )
    )


def unitary(a: Matrix) -> bool:
    return bool(a) and len(a) == len(a[0]) and isometry(a)


def apply(a: Matrix, op: Move) -> Matrix:
    tag, j, k = op
    if not (0 <= j < len(a) and 0 <= k < len(a)):
        raise ValueError("slot outside carrier")
    rows = list(a)
    if tag == "i" and j == k:
        rows[j] = tuple(I * v for v in a[j])
    elif tag == "T" and j != k:
        pairs = tuple(zip(a[j], a[k], strict=True))
        rows[j] = tuple(DIAG * x + CROSS * y for x, y in pairs)
        rows[k] = tuple(CROSS * x + DIAG * y for x, y in pairs)
    else:
        raise ValueError("invalid move")
    return tuple(rows)


def run(a: Matrix, moves: tuple[Move, ...]) -> Matrix:
    for op in moves:
        a = apply(a, op)
    return a


def integral_lift(column: tuple[Gaussian, ...]) -> tuple[int, tuple[Gaussian, ...]]:
    if not all(x.dyadic() for x in column):
        raise ValueError("not a Gaussian-dyadic column")
    power = 0
    while not all(x.integral() for x in column):
        power += 1
        column = tuple(PI * x for x in column)
    return power, column


def synthesize(target: Matrix) -> tuple[Move, ...]:
    """Specialization to a completely specified square transformation."""
    if not target or len(target[0]) != len(target):
        raise ValueError("expected a square Gaussian-dyadic unitary")
    return synthesize_isometry(target)


def synthesize_isometry(target: Matrix) -> tuple[Move, ...]:
    """Synthesize specified first columns; unused input columns are free.

    For a unit column scaled to integral entries by pi**k, k>0, its
    integral squared norm is 2**k. An even number of entries have odd norm.
    Match them in pairs; a phase i if needed gives y = i*x modulo 2.
    Both mixer numerators i*x+y, x+i*y then vanish modulo pi**2.
    Hence one layer lowers k. Integral unit columns are signed unit axes.
    Repeat on the orthogonal remaining coordinate slots.
    """
    if not isometry(target) or not all(v.dyadic() for row in target for v in row):
        raise ValueError("expected Gaussian-dyadic orthonormal columns")
    n, width, current = len(target), len(target[0]), target
    reduction: list[Move] = []

    def move(op: Move) -> None:
        nonlocal current
        current = apply(current, op)
        reduction.append(op)

    for col in range(width):
        while True:
            power, nums = integral_lift(tuple(row[col] for row in current))
            if not power:
                break
            odd = [r for r in range(col, n) if int(nums[r].re + nums[r].im) % 2]
            if not odd or len(odd) % 2:
                raise ArithmeticError("unit-column parity")
            for j, k in zip(odd[::2], odd[1::2], strict=True):
                d = nums[k] - I * nums[j]
                if int(d.re) % 2 or int(d.im) % 2:
                    move(("i", k, k))
                move(("T", j, k))
            if integral_lift(tuple(row[col] for row in current))[0] >= power:
                raise ArithmeticError("denominator failed to descend")
        axes = [r for r in range(col, n) if current[r][col] != ZERO]
        if len(axes) != 1:
            raise ArithmeticError("integral unit axis")
        axis = axes[0]
        if axis != col:
            move(("T", col, axis))
            move(("T", col, axis))
        for _ in range(3):
            if current[col][col] == ONE:
                break
            move(("i", col, col))
    if current != tuple(row[:width] for row in eye(n)):
        raise ArithmeticError("word did not reduce target to identity")
    # Both logical moves have order four. Cancel adjacent equal powers only.
    powers: list[tuple[Move, int]] = []
    for op in reversed(reduction):
        count = (powers.pop()[1] + 3) % 4 if powers and powers[-1][0] == op else 3
        if count:
            powers.append((op, count))
    return tuple(op for op, count in powers for _ in range(count))
