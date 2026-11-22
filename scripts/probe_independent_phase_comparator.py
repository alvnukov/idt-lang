"""Can two independent F5 preparations reproduce an unknown-state comparator?

An experimenter may hand both signals to ONE arbitrary co-located device:
there is no Bell separation assumption here. Two independent four-ticket
sources P_n and P_m send only their terminal raw phases. No preparation
labels, skip records, shared skip bits or correlated auxiliary stock may
reach the comparator. Common shifts and orientations are averaged with
known settings; *every* prepared pair is counted. The benchmark is a
supplied quantum antisymmetric measurement on two independent pure qubits,
not a claim that either source already sends qubits.

Barnett, Chefles & Jex https://doi.org/10.1016/S0375-9601(02)01602-X
give the quantum state-comparison setting. Hendrych et al.
https://doi.org/10.1016/S0375-9601(03)00262-7 measured photon polarization
overlap using symmetric/antisymmetric optical projections. They did not
implement this F5 preparation or our input-independence certificate.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import product

from scripts.probe_affine_pulse_holdouts import FRINGE, TAGS, encode, gates, need, power
from scripts.probe_midpoint_spectator_instrument import (
    Contact,
    Word,
    apply,
    clock,
    test_swap,
)

S = range(6)
TICKETS = (0, 1, 1, 2)
QUBIT = tuple((4 - u) * F(1, 8) for u in FRINGE)
FREDKIN: Word = ((0, 5, 6), (3, 5, 6), (5, 1, 2), (4, 1, 2), (0, 5, 6), (3, 5, 6))


def DIST(a: int, b: int) -> int:
    return min((a - b) % 6, (b - a) % 6)


def counts() -> tuple[tuple[int, ...], ...]:
    # Average over a common free rotation AND a sign of the nominal
    # separation (or equivalently randomize which arm is first). Every
    # stochastic raw pair comparator then reduces to four distance rates
    # g0..g3 in [0,1]. No individual device symmetry is assumed.
    return tuple(
        tuple(
            sum(DIST(i, k + j) == r for i, j in product(TICKETS, repeat=2))
            for r in range(4)
        )
        for k in range(4)
    )


def conditional(rows: tuple[tuple[int, ...], ...], raw: tuple[F, ...]) -> tuple[F, ...]:
    return tuple(
        sum((F(n, 16) * p for n, p in zip(row, raw, strict=True)), F(0)) for row in rows
    )


def check_bounds(rows: tuple[tuple[int, ...], ...]) -> None:
    need(
        rows == ((6, 8, 2, 0), (4, 7, 4, 1), (1, 4, 7, 4), (0, 2, 8, 6)),
        "raw distance counts",
    )
    # Verify the averaging reduction on every primitive raw-pair indicator;
    # all stochastic comparator response tables follow by linearity.
    for x, y in product(S, repeat=2):
        orbit_size = sum(DIST(a, b) == DIST(x, y) for a, b in product(S, repeat=2))
        raw = tuple(F(r == DIST(x, y), orbit_size) for r in range(4))
        observed = tuple(
            F(
                sum(
                    ((s + i) % 6, (s + sign * k + j) % 6) == (x, y)
                    for s, sign, i, j in product(S, (-1, 1), TICKETS, TICKETS)
                ),
                192,
            )
            for k in range(4)
        )
        need(
            observed == conditional(rows, raw),
            "twirl not valid on this asymmetric pair",
        )
    need(
        QUBIT == (F(0), F(1, 8), F(3, 8), F(1, 2), F(3, 8), F(1, 8)),
        "comparison reference",
    )
    # The first witness also works under a *common* multiplicative flag
    # efficiency eta: ideal 1/4 becomes eta/4 versus classical <=0.
    # The second gives the exact absolute (unthinned) minimax.
    for bits in product((F(0), F(1)), repeat=4):
        q = conditional(rows, bits)
        need(
            6 * q[2] - 4 * q[3] - 5 * q[0] == -F(3, 2) * (bits[0] + bits[1]),
            "scale-free certificate",
        )
        need(
            2 * q[2] - 7 * q[0] <= F(1, 2) and q[3] <= F(3, 8) + 4 * q[0],
            "positive comparator certificate",
        )
        if not q[0]:
            need(
                q == tuple(F(n, 16) * bits[3] for n in (0, 1, 4, 6)),
                "unambiguous shape",
            )
    best = conditional(rows, (F(0), F(0), F(2, 9), F(1)))
    need(
        2 * QUBIT[2] - 7 * QUBIT[0] == F(3, 4)
        and max(abs(a - b) for a, b in zip(best, QUBIT[:4], strict=True))
        == (F(3, 4) - F(1, 2)) / 9
        == F(1, 36),
        "sharp all-pairs minimax",
    )
    need(
        6 * QUBIT[2] - 4 * QUBIT[3] - 5 * QUBIT[0] == F(1, 4),
        "ideal homogeneous witness",
    )
    # Omitting random orientation permits a directional false hit:
    # comparator 'second minus first = 2' is perfectly positive.
    hand = [
        F(sum((k + j - i) % 6 == 2 for i, j in product(TICKETS, repeat=2)), 16)
        for k in S
    ]
    need(
        6 * hand[2] - 4 * hand[3] - 5 * hand[0] == F(15, 16),
        "missing orientation control",
    )
    # Identical skip tickets in both arms mimic every q_d using an ordinary
    # lookup on their observed raw difference. All one-arm calibrations
    # are unchanged; the intended product preparation is what fails.
    need(
        all(
            sum((QUBIT[(v + i - u - i) % 6] for i in TICKETS), F(0)) / 4
            == QUBIT[(v - u) % 6]
            for u, v in product(S, repeat=2)
        ),
        "shared preparation witness",
    )


def physical(accept_two: bool) -> tuple[list[int], Word, int]:
    # Supply stocks in one F5 frame. For Boolean computations use physical
    # tags 2,3 as false/true. Registers 3..7 are the immutable palette for
    # the old W clock, and 8..10 hold the other signal (no change of type).
    initial = [0, 1, 0, 0, 1, 2, 3, 4, 0, 1, 0]
    ops: list[Contact] = []

    def register(tag: int) -> int:
        initial.append(tag)
        return len(initial) - 1

    def onehot(arm: tuple[int, int, int]) -> list[int]:
        flags = [-1] * 6
        for k in S:
            flag, token = register(2), register(3)
            ops.extend(test_swap(arm[1], 3, flag, token))
            flags[(5 - k) % 6] = flag
            ops.extend(clock(arm))
        return flags

    aa = onehot((0, 1, 2))
    bb = onehot((8, 9, 10))
    # Affine-frame translation of abstract seven-wire Fredkin helpers
    # (1,3,4,3) to raw F5 chart whose Boolean tags are 2,3.
    helpers = tuple(register(x) for x in (3, 0, 1, 0))

    def control(c: int, x: int, y: int) -> None:
        labels = (c, x, y, *helpers)
        need(len(set(labels)) == 7, "reused physical address in Fredkin")
        ops.extend((labels[s], labels[i], labels[j]) for s, i, j in FREDKIN)

    out, tmp = register(2), register(2)
    for x, y in product(S, repeat=2):
        if DIST(x, y) == 3 or (accept_two and DIST(x, y) == 2):
            control(aa[x], tmp, bb[y])
            control(tmp, out, register(3))
            control(aa[x], tmp, bb[y])
    need(len(ops) == (588 if accept_two else 372), "literal comparison cost")
    return initial, tuple(ops), out


def native_controls() -> None:
    w, _ = gates()
    dial = [power(w, k) for k in S]
    expected = (F(0), F(0), F(2, 9), F(1))
    for b, a in product(range(5), repeat=2):
        if a == b:
            continue
        delta = a - b
        orbit = [TAGS[g[encode(b, a, b)]] for g in dial]
        probabilities = [[F(0) for _ in S] for _ in S]
        for switch, n in ((False, 7), (True, 2)):
            bank, ops, out = physical(switch)
            for x, y in product(S, repeat=2):
                v = [(b + delta * i) % 5 for i in bank]
                v[:3] = orbit[x]
                v[8:11] = orbit[y]
                apply(v, ops)
                need(
                    tuple(v[:3]) == orbit[x] and tuple(v[8:11]) == orbit[y],
                    "input code not restored",
                )
                flag = v[out] == (b + 3 * delta) % 5
                need(
                    v[out] in ((b + 2 * delta) % 5, (b + 3 * delta) % 5)
                    and flag == (DIST(x, y) == 3 or (switch and DIST(x, y) == 2)),
                    "raw phase flags or comparator",
                )
                probabilities[x][y] += F(n * flag, 9)
        need(
            all(
                probabilities[x][y] == expected[DIST(x, y)]
                for x, y in product(S, repeat=2)
            ),
            "positive minimax rule",
        )
        worst = max(
            abs(
                sum(
                    (
                        probabilities[(x + i) % 6][(y + j) % 6]
                        for i, j in product(TICKETS, repeat=2)
                    ),
                    F(0),
                )
                / 16
                - QUBIT[(x - y) % 6]
            )
            for x, y in product(S, repeat=2)
        )
        need(worst == F(1, 36), "literal all-pairs minimax")


def main() -> None:
    rows = counts()
    check_bounds(rows)
    native_controls()
    print(
        "Two independent four-ticket inputs, any co-located positive comparator: 6q2-4q3-5q0 <= 0; pure-state antiswap benchmark = 1/4."
    )
    print(
        "All 36 translated products: sharp maximum-coordinate discrepancy 1/36; actual five-tag circuits attain it using an independent 7:2 schedule choice."
    )
    print(
        "If equal inputs never flag, opposite inputs flag at most 3/8 vs 1/2. No sample selection; shared skip histories can fake the entire target."
    )
    print(
        "Averaging +/- nominal separations is required for the homogeneous witness. These finite device comparisons are not new measurements."
    )


if __name__ == "__main__":
    main()
