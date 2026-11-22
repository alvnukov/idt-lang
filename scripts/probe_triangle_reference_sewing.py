"""Compare independent triangle-plus-reference packages without a shared phase.

The detector receives one real package per port; the hidden reference on each
may have undergone any of three independent cyclic turns. Observed data are
the eight preparations from the local cycle-axis probe. Derive terminal
signed paths, then count ordered pairs on each terminal rail. Selection of
a reference branch, an independent trit, and raw data-label access are
different detector resources. No observed physical data or quantum simulator.
"""

from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import product

from scripts.probe_triangle_cycle_phase_axis import (
    BITS,
    D,
    K,
    LABELS,
    edge,
    independent,
    observed_table,
    rank,
    read,
    signed_vector,
)
from scripts.probe_triangle_exchange_source import V, median, need, norm, outer


def dot(x: V, y: V) -> int:
    return sum(a * b for a, b in zip(x, y, strict=True))


def linear(c: int, v: V, d: int, w: V) -> V:
    return tuple(c * x + d * y for x, y in zip(v, w, strict=True))


@cache
def preparations() -> dict[tuple[int, int, int], V]:
    result = {}
    for k, b in LABELS:
        raw = independent(edge((k + 1) % 3 if k in D else 0), edge(0))
        whole = signed_vector(read(raw, k, 1), 18)
        v = whole[b * 9 : (b + 1) * 9]
        need(norm(v) == ((12, 4)[b] if k in D else 18), "addressed preparation energy")
        for turn in D:
            result[k, b, turn] = tuple(
                v[3 * a + (r - turn) % 3] for a, r in product(D, repeat=2)
            )
    return result


def overlap(v: V, w: V) -> F:
    # The skew on the extra reference has square -3 on its neutral plane.
    jw = tuple(
        w[3 * a + (r - 1) % 3] - w[3 * a + (r + 1) % 3] for a, r in product(D, repeat=2)
    )
    return (F(dot(v, w) ** 2) + F(dot(v, jw) ** 2, 3)) / (norm(v) * norm(w))


GRID = tuple(product(D, repeat=4))  # current, reference, current, reference


def perm(v: V, indices: tuple[int, ...]) -> V:
    return tuple(v[i] for i in indices)


def index(a, r, b, s) -> int:
    return ((a * 3 + r) * 3 + b) * 3 + s


def cycle_maps(on_ref: bool):
    return tuple(
        tuple(
            index(a, (r - j) % 3, b, (s - j) % 3)
            if on_ref
            else index((a - j) % 3, r, (b - j) % 3, s)
            for a, r, b, s in GRID
        )
        for j in (1, -1)
    )


REF = cycle_maps(True)
CUR = cycle_maps(False)
SWAP_CUR = tuple(index(b, r, a, s) for a, r, b, s in GRID)
SWAP_FULL = tuple(index(b, s, a, r) for a, r, b, s in GRID)


def cycles(v: V, maps) -> tuple[V, V]:
    # I+T+T² and three straight paths minus that same orbit sum.
    p, q = (perm(v, f) for f in maps)
    plus = tuple(x + y + z for x, y, z in zip(v, p, q, strict=True))
    return plus, linear(3, v, -1, plus)


def exchange(v: V, indices) -> tuple[V, V]:
    s = perm(v, indices)
    return linear(1, v, 1, s), linear(1, v, -1, s)


def detector(v: V) -> tuple[F, F, F, F]:
    """All eight final branches; no normalized operator or target drives them."""
    n = norm(v)
    cells = {}
    for i, w in enumerate(cycles(v, REF)):
        for j, u in enumerate(cycles(w, CUR)):
            for h, z in enumerate(exchange(u, SWAP_CUR)):
                cells[i, j, h] = norm(z)
    den = 9 * 9 * 4 * n
    need(sum(cells.values()) == den, "lost raw product events")
    minus = sum(cells[1, j, h] for j, h in product(BITS, repeat=2))
    need(2 * minus == den, "reference branch is not a fair premeasurement")
    singled = sum(cells[1, j, 1] for j in BITS)
    plus_complement = sum(cells[0, j, h] for j, h in product(BITS, repeat=2) if j or h)
    # In the minus reference sector both reference coordinates are swap-even.
    # Hence comparing the two currents agrees there with whole-package swap.
    full = exchange(cycles(v, REF)[1], SWAP_FULL)
    need(
        F(norm(full[1]), sum(map(norm, full))) == F(singled, minus),
        "whole-exchange crosscheck",
    )
    return (
        F(singled, minus),
        F(singled, den),
        F(plus_complement, den),
        F(3 * singled + plus_complement, 3 * den),
    )


def pieces18(v: V) -> tuple[V, V, V, V]:
    """18 times four orthogonal projectors; used only for certifying optimality."""
    plus, minus = cycles(v, REF)
    f = tuple(3 * x for x in exchange(minus, SWAP_FULL)[1])
    t = linear(6, minus, -1, f)
    l = exchange(cycles(plus, CUR)[0], SWAP_CUR)[0]
    q = linear(6, plus, -1, l)
    return f, t, l, q


def directions():
    # An orthogonal but not orthonormal basis keeps all paths integral.
    two = (edge(0), median(0))
    single = tuple(outer(x, y) for x, y in product(two, repeat=2))
    return single, tuple(outer(x, y) for x, y in product(single, repeat=2))


def optimality():
    src = preparations()
    one, basis = directions()
    need(
        len(basis) == 16
        and all(not dot(a, b) for i, a in enumerate(basis) for b in basis[:i]),
        "basis",
    )
    ops = [pieces18(a) for a in basis]
    for i, a in enumerate(basis):
        need(
            all(
                sum(w) == 18 * z
                for w, z in zip(zip(*ops[i], strict=True), a, strict=True)
            ),
            "resolution",
        )
        for j, v in enumerate(ops[i]):
            need(
                all(
                    z == tuple((18 if k == j else 0) * c for c in v)
                    for k, z in enumerate(pieces18(v))
                ),
                "scaled orthogonal idempotents",
            )
    traces = [
        sum(F(dot(a, o[k]), 18 * norm(a)) for a, o in zip(basis, ops, strict=True))
        for k in range(4)
    ]
    need(traces == [2, 6, 2, 6], "sector ranks")
    for i, a in enumerate(basis):
        for j, b in enumerate(basis):
            need(
                all(dot(a, ops[j][k]) == dot(b, ops[i][k]) for k in range(4)),
                "not self adjoint",
            )
    equal = []
    dual = [[F(0)] * 16 for _ in basis]
    coord = {key: tuple(dot(d, x) for d in one) for key, x in src.items()}
    for k, b in LABELS:
        # Six equatorial directions in total weight 2/3, two poles 1/3.
        prior = F(1, 9) if k != K else F(1, 6)
        for u, v in product(D, repeat=2):
            for c, factor in ((b, -2), (1 - b, 1)):
                l, r = (k, b, u), (k, c, v)
                x = outer(coord[l], coord[r])
                p = prior * factor / (9 * norm(src[l]) * norm(src[r]))
                if c == b:
                    equal.append(x)
                for i, xi in enumerate(x):
                    if xi:
                        for j, xj in enumerate(x):
                            dual[i][j] += p * (xi * xj)
    need(rank(equal) == 14, "equal-ray null-space count")
    # On every equal-input vector the enumeration in main gives <F>=0.
    # F is an orthogonal projector of rank 2, so its range is the entire
    # orthogonal complement of the 14D equal-input span. A positive effect
    # E vanishing there annihilates EACH equal input (positivity is crucial).
    # Thus 0 <= E <= F whenever E <= I and it has no equal-input clicks.
    # On an orthogonal preparation <F>=1/4, half the target 1/2. Ignoring
    # the other reference herald is legitimate ONLY for the conditional row.
    # D = rho_orthogonal - 2 rho_equal = F/8 - T/8 - L/4. Its positive
    # part has trace 2/8, so any effect 0<=E<=I obeys p_orth<=1/4+2p_equal.
    # Comparing to 1/2 and 0 gives delta>=1/12 for an arbitrary such effect.
    for i, a in enumerate(basis):
        for j, (f, t, l, _) in enumerate(ops):
            need(
                dual[i][j] == F(dot(a, f) - dot(a, t) - 2 * dot(a, l), 144),
                "finite dual certificate",
            )
    return traces


def main():
    src = preparations()
    table = observed_table()
    errors = Counter()
    for (k, b, u), v in src.items():
        for (j, c, w), z in src.items():
            t = overlap(v, z)
            need(t == table[k, b, j, c], "input turns changed local table")
            target = (1 - t) / 2
            conditional, f, q, out = detector(outer(v, z))
            need(
                conditional == target and f == target / 2 and q == F(1, 2) - t / 4,
                "reference-resolved independent comparator",
            )
            errors[out - target] += 1
    need(
        errors
        == {F(-1, 12): 72, F(-1, 24): 108, F(0): 216, F(1, 24): 108, F(1, 12): 72},
        "minimax",
    )
    traces = optimality()
    print(
        "576 independently twisted inputs: reference branch occurs with probability 1/2; "
        "conditional antiswap is exact. Zero false positives: tight unconditioned efficiency 1/2."
    )
    print(
        "Any positive real binary effect on one package from each port: minimax error 1/12. "
        "Two native cycle comparisons, current swap and an independent 1-in-3 accept attain it."
    )
    print(
        "Equal inputs span 14/16; sector ranks:",
        tuple(map(int, traces)),
        "; errors:",
        sorted(errors.items()),
    )
    print(
        "Uses co-location, extra reference carriers, signed integer merging and ordered same-rail pairs. "
        "No physically independent source, native random trit, or complex composition law established."
    )


if __name__ == "__main__":
    main()
