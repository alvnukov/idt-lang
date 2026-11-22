"""Uniform return-metric wall and a killed-walk preparation holdout.

For a reversible permutation P and uniform start on a bright set S, the
dark rate after k shifts is |S symmetric-difference P^k S|/(2|S|). The
triangle inequality through P S gives d_2 <= 2*d_1. Errors of at most e
against the six-state target force 3/4-e <= 2*(1/4+e), so e >= 1/12.
This wall assumes uniform preparation, not an arbitrary classical mixture.

The walk starts uniformly on odd sites and is killed at either interval
endpoint at every microstep. The index j=(x-1)/2 embeds surviving sites as
a contiguous bright block in a ring of 2*d bins. Cyclic phase shifts and
the bright/dark partition are supplied readout rules, not the walk itself.

For d>=2, the two-step kernel is symmetric and primitive (self-loops and
nearest-neighbor links). The sine vector v_j=sin((j+1/2)*theta), theta=pi/d,
has ghosts v_-1=-v_0 and v_d=-v_(d-1). Thus the interior recurrence with
these ghosts gives K v=(2+2*cos(theta))/4*v, including the end rows. Its
positive eigenvector controls the limiting survivor endpoint law q=v/sum(v).
For 0<=k<=d, shifting the bright block by k sends its last k bins dark;
by reflection their q mass is the first k entries. Summing the half-step
sines gives (1-cos(k*theta))/2=sin^2(k*theta/2), with the return half of
the cycle given by reflection. This is a limiting conditional readout, not
the finite preparation data, and entails no quantum or general reset law.
"""

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from itertools import accumulate, permutations, product
from math import cos, isclose, pi, sin

Counts = tuple[int, ...]
Kernel = tuple[Counts, ...]
SIX_TARGET = tuple(Fraction(n, 4) for n in (0, 1, 3, 4, 3, 1))


def check(condition: bool, message: str) -> None:
    """Keep every check active under python -O."""
    if not condition:
        raise AssertionError(message)


def image(bright: set[int], permutation: Sequence[int]) -> set[int]:
    return {permutation[j] for j in bright}


def check_uniform_wall() -> int:
    checked = 0
    for size in range(2, 9):
        cycle = tuple((j + 1) % size for j in range(size))
        shuffles = permutations(range(size)) if size <= 5 else iter((cycle,))
        for permutation in shuffles:
            for mask in range(1, (1 << size) - 1):
                bright = {j for j in range(size) if mask & (1 << j)}
                once = image(bright, permutation)
                twice = image(once, permutation)
                d1 = len(once - bright)
                d2 = len(twice - bright)
                check(len(bright ^ once) == 2 * d1, "one-shift return metric")
                check(len(bright ^ twice) == 2 * d2, "two-shift return metric")
                check(d2 <= 2 * d1, "permutation triangle violation")
                checked += 1
    return checked


def dark_count(masses: Sequence[int], shift: int) -> int:
    """Mass shifted out of the initial contiguous bright block."""
    d = len(masses)
    return sum(m for j, m in enumerate(masses) if (j + shift) % (2 * d) >= d)


def conditional_curve(masses: Counts) -> tuple[Fraction, ...]:
    return tuple(
        Fraction(dark_count(masses, k), sum(masses)) for k in range(2 * len(masses))
    )


def check_six_state_wall() -> None:
    uniform = conditional_curve((1, 1, 1))
    nonuniform = conditional_curve((1, 2, 1))
    check(uniform == tuple(Fraction(n, 3) for n in (0, 1, 2, 3, 2, 1)), "uniform pin")
    lower_bound = (SIX_TARGET[2] - 2 * SIX_TARGET[1]) / 3
    gap = max(abs(a - b) for a, b in zip(uniform, SIX_TARGET, strict=True))
    check(
        gap == lower_bound == Fraction(1, 12),
        "uniform Chebyshev lower bound/attainment",
    )
    check(nonuniform == SIX_TARGET, "nonuniform six-state control")
    print(
        f"Six-state uniform dark rates: {', '.join(map(str, uniform))}; optimal gap {gap}"
    )
    print(
        f"Six-state nonuniform dark rates: {', '.join(map(str, nonuniform))}; exact target"
    )


def killed_endpoint(d: int, start: int, moves: Sequence[int]) -> int | None:
    """Return a live endpoint, or None as soon as a wall is reached."""
    x = start
    for move in moves:
        x += move
        if not 0 < x < 2 * d:
            return None
    return x


def two_step_counts(d: int) -> Kernel:
    """One row per odd start, with denominator four; missing paths were killed."""
    if d < 1:
        raise ValueError("need at least one odd site")
    matrix: list[Counts] = []
    for start in range(1, 2 * d, 2):
        row = [0] * d
        for moves in product((-1, 1), repeat=2):
            end = killed_endpoint(d, start, moves)
            if end is not None:
                row[(end - 1) // 2] += 1
        matrix.append(tuple(row))
    return tuple(matrix)


def preparation_counts(d: int, blocks: int) -> Counts:
    """Unnormalized survivor counts with denominator d*4**blocks."""
    if blocks < 0:
        raise ValueError("blocks must be nonnegative")
    matrix = two_step_counts(d)
    counts = (1,) * d
    for _ in range(blocks):
        counts = tuple(
            sum(mass * row[j] for mass, row in zip(counts, matrix, strict=True))
            for j in range(d)
        )
    return counts


def brute_walk_counts(d: int, blocks: int) -> Counts:
    """Independent complete paths oracle, checking the whole microstep trace."""
    counts = [0] * d
    for start in range(1, 2 * d, 2):
        for moves in product((-1, 1), repeat=2 * blocks):
            trace = tuple(accumulate(moves, initial=start))
            if min(trace) > 0 and max(trace) < 2 * d:
                counts[(trace[-1] - 1) // 2] += 1
    return tuple(counts)


@dataclass(frozen=True)
class Readout:
    survival: Fraction
    bright_all: Fraction
    dark_all: Fraction
    loss: Fraction
    dark_given_survival: Fraction | None


def finite_readout(counts: Counts, blocks: int, shift: int) -> Readout:
    total = len(counts) * 4**blocks
    survivors = sum(counts)
    dark = dark_count(counts, shift)
    return Readout(
        Fraction(survivors, total),
        Fraction(survivors - dark, total),
        Fraction(dark, total),
        Fraction(total - survivors, total),
        Fraction(dark, survivors) if survivors else None,
    )


def check_kernel() -> None:
    check(1 + sum((-1, +1)) == 1, "exit-and-return control did not return")
    check(killed_endpoint(3, 1, (-1, +1)) is None, "a wall hit was undone at block end")
    check(two_step_counts(1) == ((0,),), "one-site kernel")
    for d in range(1, 9):
        if d >= 2:
            expected = tuple(
                tuple(
                    (2 if 0 < i < d - 1 else 1) if i == j else int(abs(i - j) == 1)
                    for j in range(d)
                )
                for i in range(d)
            )
            check(two_step_counts(d) == expected, f"two-step kernel d={d}")
        for blocks in range(4):
            counts = preparation_counts(d, blocks)
            check(
                counts == brute_walk_counts(d, blocks),
                f"full-path oracle d={d}, n={blocks}",
            )
            for shift in range(2 * d):
                rate = finite_readout(counts, blocks, shift)
                check(
                    rate.bright_all + rate.dark_all == rate.survival,
                    "misclassified survivor",
                )
                check(rate.survival + rate.loss == 1, "missing loss mass")
    check(
        finite_readout(preparation_counts(1, 1), 1, 1)
        == Readout(Fraction(0), Fraction(0), Fraction(0), Fraction(1), None),
        "d=1 should have zero survivors and undefined conditional rate",
    )
    for blocks in range(5):
        d2 = finite_readout(preparation_counts(2, blocks), blocks, 1)
        check(d2.survival == Fraction(1, 2**blocks), "d=2 survival")
        check(d2.dark_given_survival == Fraction(1, 2), "d=2 survivor prep is uniform")


def check_finite_holdouts() -> None:
    rows = (
        # d, blocks, shift, endpoint counts, all-start dark, conditional dark
        (3, 1, 1, (2, 4, 2), Fraction(1, 6), Fraction(1, 4)),
        (3, 2, 1, (6, 12, 6), Fraction(1, 8), Fraction(1, 4)),
        (4, 2, 1, (6, 14, 14, 6), Fraction(3, 32), Fraction(3, 20)),
        (6, 2, 2, (6, 14, 16, 16, 14, 6), Fraction(5, 24), Fraction(5, 18)),
    )
    for d, blocks, shift, expected, dark_all, conditional in rows:
        counts = preparation_counts(d, blocks)
        check(counts == expected, f"held-out endpoint counts d={d}, n={blocks}")
        result = finite_readout(counts, blocks, shift)
        check(result.dark_all == dark_all, "held-out all-start dark rate")
        check(
            result.dark_given_survival == conditional, "held-out conditional dark rate"
        )
        print(
            f"d={d}, n={blocks}, k={shift}: endpoints={list(counts)}/{d * 4**blocks}; "
            f"S={result.survival}, bright/all={result.bright_all}, dark/all={result.dark_all}, "
            f"loss={result.loss}, dark|S={result.dark_given_survival}"
        )

    # In d=6 the symmetric masses (a,b,c,c,b,a) give D2-S/4=(a+b-c)/2.
    # One quarter-kernel application halves this linear form; at n=0 it is 1/12.
    last_gap = last_survival = Fraction(2)
    for blocks in range(17):
        result = finite_readout(preparation_counts(6, blocks), blocks, 2)
        excess = result.dark_all - result.survival / 4
        check(excess == Fraction(1, 12 * 2**blocks), "d=6 finite excess identity")
        gap = excess / result.survival
        check(0 < gap < last_gap, "d=6 conditional gap did not shrink")
        check(0 < result.survival < last_survival, "d=6 survival did not shrink")
        last_gap, last_survival = gap, result.survival
    print(f"d=6, n=16, k=2: still above 1/4 by {last_gap}; survival={last_survival}")


def check_limiting_curve() -> None:
    """Numerical sanity check of the analytic note, not an exact proof gate."""
    for d in (2, 3, 4, 6, 16):
        theta = pi / d
        v = tuple(sin((j + 0.5) * theta) for j in range(d))
        eigenvalue = cos(theta / 2) ** 2
        for row, component in zip(two_step_counts(d), v, strict=True):
            value = sum(n * part / 4 for n, part in zip(row, v, strict=True))
            check(
                isclose(value, eigenvalue * component, rel_tol=0, abs_tol=1e-12),
                "sine eigenvector",
            )
        for k in range(2 * d):
            dark = sum(p for j, p in enumerate(v) if (j + k) % (2 * d) >= d)
            check(
                isclose(
                    dark / sum(v), sin(k * theta / 2) ** 2, rel_tol=0, abs_tol=1e-12
                ),
                "sine curve",
            )
    print(
        "Limiting endpoint-conditioned curve: numerical sanity only (absolute tolerance 1e-12)"
    )


def check_sequential_control() -> None:
    counts = preparation_counts(3, 1)
    d = len(counts)
    single_bright = Fraction(sum(counts) - dark_count(counts, 1), sum(counts))
    both = Fraction(
        sum(
            n
            for j, n in enumerate(counts)
            if all((j + k) % (2 * d) < d for k in (1, 2))
        ),
        sum(counts),
    )
    independent_reset = single_bright**2
    check(
        both == Fraction(1, 4) and independent_reset == Fraction(9, 16),
        "bright reset control",
    )
    print(
        f"d=3, two consecutive bright reads: noninvasive BB={both}; supplied reset BB={independent_reset}"
    )

    # In a long-past/long-future bulk snapshot, the endpoint law gains another v factor.
    squared = tuple(n * n for n in counts)
    check(
        conditional_curve(squared)[1] == Fraction(1, 6), "bulk-vs-endpoint d=3 control"
    )
    print(
        "d=3, long-past-and-future conditioning would give k=1 dark=1/6, not endpoint 1/4"
    )


def main() -> None:
    print(f"Uniform return metric: {check_uniform_wall()} permutation/set cases")
    check_six_state_wall()
    check_kernel()
    check_finite_holdouts()
    check_limiting_curve()
    check_sequential_control()


if __name__ == "__main__":
    main()
