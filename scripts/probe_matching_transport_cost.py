"""Positive-stock resource bounds for the norm-free selected matching echo.

Copying all possible histories and randomly choosing one history are
different experiments. A single classical carrier here is a column-stochastic
transition over six labels with input-independent rules. The bounds concern
uniform gain on the WHOLE specified sector, not merely one prepared vector.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import permutations, product

from scripts import probe_balanced_phase_composition as b
from scripts.probe_matching_echo_selector import I6, P0, classify, need
from scripts.probe_matching_transport import MATCHES, polar


def col_abs(u: b.Matrix) -> tuple[F, ...]:
    return tuple(sum((abs(z) for z in col), F(0)) for col in zip(*u, strict=True))


def markov(u: b.Matrix) -> bool:
    return all(z >= 0 for row in u for z in row) and all(
        sum(col) == 1 for col in zip(*u, strict=True)
    )


def run_controls() -> None:
    m, n, r, u = classify()
    r2 = b.multiply(r, r)
    am, an = b.add(I6, b.scale(-1, m)), b.add(I6, b.scale(-1, n))
    center = b.add(I6, b.scale(-1, P0))
    odd = polar(MATCHES[4], MATCHES[0])
    need(col_abs(odd) == (F(5, 3),) * 3, "odd total variation")
    # One incoming pure mark has a unit signed-pair l1 budget. An odd-sector
    # column of cU requires 5c/3 in that budget, hence c<=3/5. The kernel
    # below attains it on every input simultaneously.
    five = b.scale(F(1, 5), b.add(b.scale(2, b.add(I6, r)), b.multiply(n, r2)))
    need(
        markov(five) and b.multiply(an, five) == b.scale(F(3, 5), b.multiply(u, am)),
        "sharp odd gain",
    )
    # Any K = cU on centered inputs has K=cU+v 1^t since all column
    # differences agree; every row of U has minimum -1/3. Positivity implies
    # v_i>=c/3 and stochasticity sum v_i=1-c. Thus c<=1/3 even without
    # stipulating a fixed uniform-output bias. At equality the bias is unique.
    need(all(min(row) == F(-1, 3) for row in u), "centered minima")
    nine = b.add(b.scale(F(1, 3), u), b.scale(F(2, 3), P0))
    need(
        markov(nine)
        and b.multiply(nine, center) == b.scale(F(1, 3), b.multiply(u, center)),
        "sharp all-centered gain",
    )
    for c in (F(1), F(1, 2), F(1, 3), F(1, 4)):
        smallest = tuple(max(-c * x for x in row) for row in u)
        need((sum(smallest) <= 1 - c) == (c <= F(1, 3)), "cannot hide the common bias")
    # A six-label isometric deterministic permutation is not a substitute for
    # c=1: extrema show impossibility before any convex mixture/search.
    for p in permutations(range(6)):
        for x in range(6):
            need(
                sum(int(p[x] in pair) for pair in MATCHES[4]) == 1,
                "classical output budget",
            )
    for size, t in product((5, 9), range(1, 5)):
        count = size**t
        gain = 3**t
        need(
            F(gain, count) == F(3, size) ** t and gain < count, "per-layer attenuation"
        )


def main() -> None:
    run_controls()
    print(
        "One conserved classical record per step: maximum state-uniform contrast gain 3/5 on odd directions; only 1/3 on the full five centered directions. Explicit positive stochastic maps attain both. An arbitrary input-independent output bias cannot improve the second bound."
    )
    print(
        "Running all integer branches gives gains 3 and total counts 5 or 9, not a costless unitary on raw probabilities. With normalized random routing at each step the corresponding signal shrinks exponentially. Distinct memory, active gain or a different preparation contract are not excluded."
    )


if __name__ == "__main__":
    main()
