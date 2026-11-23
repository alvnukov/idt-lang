"""Real phase planes and a common-period discriminator from unsigned clocks.

The clock update itself only permutes locations. We supply real linear
scattering of signals on those locations, a physical comparison wiring,
and, when used, a coherent linear sum/difference and square-norm readout.
These are not properties of an isolated unsigned mark or a click law.

For one common tick on clock rings m,n, covariance is K T_m = T_n K.
The matrix entries are constant on simultaneous (row,column) tick orbits,
indexed by row-column modulo gcd(m,n) for primitive aligned shifts.
Thus K depends only on the common phase quotient, and rank <= gcd(m,n).
For arbitrary sampled strides with permutation orders M,N and cycle
counts A,B, K factors through the T_m^N coinvariants and into the
T_n^M invariants. The dimensions are gcd(M,N)*A and gcd(M,N)*B.
Pair corresponding tick cycles and scatter across matched quotient
fibres to realize the smaller dimension using rational, reversible stars.
Unmatched modes do not transfer; they are not globally absorbed.

No step computes with complex numbers. C4 and C3 have distinct real
two-dimensional rotation planes, analytically Gaussian and Eisenstein;
the local premises select neither. Only relative (mis)alignment is seen.
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm


def need(condition, reason):
    if not condition:
        raise ArithmeticError(reason)


def tick(v, stride=1):
    return tuple(v[(i - stride) % len(v)] for i in range(len(v)))


def mirror(v):
    return tuple(v[-i % len(v)] for i in range(len(v)))


def unit(n, j):
    return tuple(int(i == j) for i in range(n))


def dot(v, w):
    return sum(a * b for a, b in zip(v, w, strict=True))


def cycles(n, stride):
    unseen = set(range(n))
    out = []
    while unseen:
        start = min(unseen)
        p = start
        stage = []
        while p in unseen:
            unseen.remove(p)
            stage.append(p)
            p = (p + stride) % n
        need(p == start, "not a reciprocal tick orbit")
        out.append(tuple(stage))
    return tuple(out)


def fibers(m, n, sa=1, sb=1):
    left, right = cycles(m, sa), cycles(n, sb)
    length_a, length_b = len(left[0]), len(right[0])
    g = gcd(length_a, length_b)
    return tuple(
        (*a[r::g], *(m + j for j in b[r::g]))
        for a, b in zip(left, right, strict=False)
        for r in range(g)
    )


def stars(v, groups):
    out = list(v)
    for group in groups:
        common = F(2 * sum(v[j] for j in group), len(group))
        for j in group:
            out[j] = common - v[j]
    return tuple(out)


def transfer(v, n, groups):
    return stars((*v, *((0,) * n)), groups)[len(v) :]


def matrix_rank(rows):
    rows = [list(map(F, row)) for row in rows]
    running = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(running, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[running], rows[pivot] = rows[pivot], rows[running]
        p = rows[running]
        for row in rows[running + 1 :]:
            if row[j]:
                c = row[j] / p[j]
                for col in range(j, len(row)):
                    row[col] -= p[col] * c
        running += 1
    return running


def covariance(k, m, n, sa, sb):
    return all(
        k[(i + sb) % n][(j + sa) % m] == k[i][j] for i, j in product(range(n), range(m))
    )


def transfer_table(m, n, groups):
    return tuple(zip(*(transfer(unit(m, j), n, groups) for j in range(m)), strict=True))


def rank_controls():
    records = []
    tested = 0
    for m, n in product(range(2, 10), repeat=2):
        for sa, sb in ((1, 1), (1, -1), (2, 1), (2, 3), (0, 1)):
            ls, rs = cycles(m, sa), cycles(n, sb)
            oa, ob = len(ls[0]), len(rs[0])
            g = gcd(oa, ob)
            groups = fibers(m, n, sa, sb)
            table = transfer_table(m, n, groups)
            rank = matrix_rank(table)
            need(
                covariance(table, m, n, sa, sb) and rank == g * min(len(ls), len(rs)),
                "cross rank/covariance",
            )
            count_orbits = 0
            unseen = set(product(range(n), range(m)))
            while unseen:
                i, j = min(unseen)
                orbit = {
                    ((i + t * sb) % n, (j + t * sa) % m) for t in range(lcm(oa, ob))
                }
                need(orbit.issubset(unseen), "simultaneous-tick orbit overlap")
                if sa == sb == 1:
                    need(
                        orbit
                        == {
                            (u, v)
                            for u, v in product(range(n), range(m))
                            if (u - v - i + j) % g == 0
                        },
                        "primitive quotient is not the phase difference modulo gcd",
                    )
                unseen.difference_update(orbit)
                count_orbits += 1
            need(
                count_orbits == g * len(ls) * len(rs), "dimension of intertwiner space"
            )
            sample = tuple(j % 5 - 2 for j in range(m + n))
            after = stars(sample, groups)
            need(
                stars(after, groups) == sample
                and dot(sample, sample) == dot(after, after),
                "not lossless/reversible",
            )
            tested += 1
            if (m, n, sa, sb) in (
                (3, 4, 1, 1),
                (4, 6, 1, 1),
                (4, 6, 2, 3),
                (6, 3, 2, 1),
                (4, 4, 1, -1),
            ):
                records.append(
                    {
                        "sizes": (m, n),
                        "strides": (sa, sb),
                        "tick_orders": (oa, ob),
                        "cross_rank": rank,
                        "intertwiner_dimension": count_orbits,
                    }
                )
    wrong = transfer_table(4, 4, fibers(4, 4))
    corrected = transfer_table(4, 4, fibers(4, 4, 1, -1))
    need(
        covariance(wrong, 4, 4, 1, 1)
        and not covariance(wrong, 4, 4, 1, -1)
        and covariance(corrected, 4, 4, 1, -1),
        "reversal requires mirror wiring, not loss of a plane",
    )
    return {"clock_size_stride_cases": tested, "selected_ranks": records}


MODES = {2: (1, -1), 3: (2, -1, -1), 4: (1, 0, -1, 0), 6: (2, 1, -1, -2, -1, 1)}


def phase_algebra():
    u3 = (1, -1, 0)
    u4 = MODES[4]
    for u, gram in ((u3, (2, -1, 2)), (u4, (2, 0, 2))):
        v = tick(u)
        need(
            (dot(u, u), dot(u, v), dot(v, v)) == gram and sum(u) == sum(v) == 0,
            "Gram law",
        )
        for a, b in product(range(-3, 4), repeat=2):
            w = tuple(a * x + b * y for x, y in zip(u, v, strict=True))
            need(
                dot(w, w) == gram[0] * a * a + 2 * gram[1] * a * b + gram[2] * b * b,
                "wrong phase-plane norm form",
            )
            if len(u) == 3:
                need(
                    all(
                        x + y + z == 0
                        for x, y, z in zip(w, tick(w), tick(w, 2), strict=True)
                    ),
                    "C3 plane polynomial",
                )
                need(
                    all(
                        2 * x + y == -(2 * z + y)
                        for x, y, z in zip(tick(w), w, tick(w, -1), strict=True)
                    ),
                    "C3 conjugation",
                )
            else:
                need(
                    tick(w, 2) == tuple(-x for x in w)
                    and tick(w, -1) == tuple(-x for x in tick(w)),
                    "C4 plane polynomial",
                )
            need(
                mirror(tick(mirror(w))) == tick(w, -1),
                "reversing cyclic order must conjugate",
            )
    need(tick(MODES[2]) == (-1, 1), "order-two real sign")
    return {
        "C2": "one real sign",
        "C3": "T²+T+I=0; (2T+I)²=−3I; norm 2(a²−ab+b²)",
        "C4": "T²=−I; norm 2(a²+b²)",
        "orientation_reversal": "inverts T and reverses both plane generators",
    }


def selective_interface():
    rows = {}
    for n in (3, 4, 6, 12):
        groups = fibers(12, n)
        for period, shape in MODES.items():
            source = shape * (12 // period)
            wave = transfer(source, n, groups)
            full = stars((*source, *((0,) * n)), groups)
            base = 5
            # Positive concentration streams can carry coordinate deviations;
            # their decoding is still a *linear signal* premise, not packets.
            positive = tuple(base + a for a in (*source, *((0,) * n)))
            positive_out = stars(positive, groups)
            need(
                min(positive_out) >= 0
                and tuple(a - base for a in positive_out) == full,
                "positive baseline control",
            )
            gain = F(24, 12 + n)
            predicted = (
                tuple(gain * shape[i % period] for i in range(n))
                if n % period == 0
                else (0,) * n
            )
            fraction = F(dot(wave, wave), dot(source, source))
            need(
                wave == predicted
                and sum(wave) == 0
                and (fraction > 0) == (n % period == 0),
                "mode sorting",
            )
            if any(wave):
                need(
                    fraction == F(4 * 12 * n, (12 + n) ** 2),
                    "calibrated transferred norm fraction",
                )
            else:
                need(
                    full[:12] == tuple(-a for a in source),
                    "blocked mode disappeared instead of reflecting",
                )
            rows[f"C{n}<-period{period}"] = str(fraction)
    return rows


def select_gaussian(v):
    return tuple(F(a - b, 2) for a, b in zip(v, tick(v, 2), strict=True))


def center(v):
    avg = F(sum(v), len(v))
    return tuple(a - avg for a in v)


def driven_conversion():
    """External time modulation defeats static incompatibility at a cost.

    Propagate the chosen frame by one tick on both ends: K_(t+1) is
    T_4 K_t T_3^-1. An externally controlled word with period P closes
    iff its seed K_0 intertwines the Pth powers. Orbit indicator
    matrices form a complete real basis for those intertwiners.
    """
    planes = ((1, -1, 0), (0, 1, -1))
    results = {}
    for period in range(1, 25):
        # Exhaust every admissible interface direction through its orbit
        # basis: a path from a centered input may only use these ranges.
        unused = set(product(range(4), range(3)))
        centered_vectors = []
        gaussian_vectors = []
        while unused:
            i, j = min(unused)
            orbit = {((i + period * k) % 4, (j + period * k) % 3) for k in range(12)}
            unused.difference_update(orbit)
            for v in planes:
                wave = tuple(
                    sum(v[b] for b in range(3) if (a, b) in orbit) for a in range(4)
                )
                centered_vectors.append(center(wave))
                gaussian_vectors.append(select_gaussian(wave))
        expected_centered = 3 if period % 12 == 0 else int(period % 6 == 0)
        expected_gaussian = 2 if period % 12 == 0 else 0
        need(
            matrix_rank(centered_vectors) == expected_centered
            and matrix_rank(gaussian_vectors) == expected_gaussian,
            "unexpected projected range in the full periodically driven intertwiner space",
        )

        groups = fibers(3, 4, period, period)

        def numbered_group(group, t):
            return tuple(
                sorted((j + t) % 3 if j < 3 else 3 + (j - 3 + t) % 4 for j in group)
            )

        time_zero = {numbered_group(group, 0) for group in groups}
        time_end = {numbered_group(group, period) for group in groups}
        need(
            time_end == time_zero
            and covariance(transfer_table(3, 4, groups), 3, 4, period, period),
            "lossless scheduled interface did not close",
        )
        # Explicit actual seed routing, not just permission for possible
        # matrices. Dimension of source plane is two even if the span of
        # ranges of *all* period-12 interfaces reaches C4 centered dim 3.
        cs = tuple(center(transfer(v, 4, groups)) for v in planes)
        gs = tuple(select_gaussian(transfer(v, 4, groups)) for v in planes)
        need(
            matrix_rank(cs) == min(2, expected_centered)
            and matrix_rank(gs) == expected_gaussian,
            "star sequence failed to attain the scheduled conversion rank",
        )
        if period in (1, 3, 4, 6, 12):
            results[period] = {
                "demonstrated_centered_transfer_rank": matrix_rank(cs),
                "demonstrated_gaussian_plane_transfer_rank": matrix_rank(gs),
                "seed_stars": groups,
            }
    return {
        "first_period_allowing_centered_transfer_parity_only": 6,
        "first_period_allowing_gaussian_plane_transfer": 12,
        "selected_periods": results,
    }


def contrast(u, v):
    n = len(u)
    need(len(v) == n, "no comparison without a shared register")
    source = (*u, *v, *((0,) * (2 * n)))
    groups = tuple((i, i + n, i + 2 * n, i + 3 * n) for i in range(n))
    out = stars(source, groups)
    minus, plus = dot(out[: 2 * n], out[: 2 * n]), dot(out[2 * n :], out[2 * n :])
    power = dot(u, u) + dot(v, v)
    need(
        plus + minus == power > 0 and plus - minus == 2 * dot(u, v),
        "calibrated real sum/difference comparator",
    )
    return F(plus - minus, power)


def scan(u, v):
    return tuple(contrast(u, tick(v, k)) for k in range(len(u)))


def timing_controls():
    orbits = {}
    for period, u, v in ((3, MODES[3], (0, 1, -1)), (4, MODES[4], tick(MODES[4]))):
        held = scan(u, v)
        expected = (F(0), F(-3, 4), F(3, 4)) if period == 3 else (0, -1, 0, 1)
        need(held == expected, "oriented interference discriminator")
        # A global relabeling of the entire comparison apparatus reverses
        # the label for the delay too, so cannot distinguish absolute chirality.
        reversed_side = scan(u, mirror(v))
        reverse_order = tuple(held[-k % period] for k in range(period))
        need(
            reversed_side == reverse_order and reversed_side != held,
            "one-sided order and both-sided gauge control",
        )
        need(
            tuple(contrast(mirror(u), tick(mirror(v), -k)) for k in range(period))
            == held,
            "global reversal plus delay relabeling",
        )
        for common in range(period):
            need(
                scan(tick(u, common), tick(v, common)) == held,
                "common unknown origin should cancel",
            )
        independent_offsets = tuple(
            sum(
                contrast(tick(u, a), tick(v, b + k))
                for a, b in product(range(period), repeat=2)
            )
            / period**2
            for k in range(period)
        )
        need(
            not any(independent_offsets),
            "uniform independent origins wash out centered contrast",
        )
        drift_scan = tuple(
            sum(contrast(tick(u, t), tick(v, 2 * t + k)) for t in range(period))
            / period
            for k in range(period)
        )
        need(
            not any(drift_scan),
            "one relative step per tick eliminates this scan on closed windows",
        )
        orbits[period] = {
            "locked_delay_scan": tuple(map(str, held)),
            "one_side_reversed": tuple(map(str, reversed_side)),
            "independent_uniform_offsets": tuple(map(str, independent_offsets)),
            "relative_plus_one_drift_cycle_mean": tuple(map(str, drift_scan)),
        }

    u4 = MODES[4]
    rel_stride = 2
    drift_trace = tuple(
        contrast(tick(u4, t), tick(u4, (1 + rel_stride) * t)) for t in range(4)
    )
    p2 = MODES[2] * 2
    parity_drift = tuple(
        contrast(tick(p2, t), tick(p2, (1 + rel_stride) * t)) for t in range(4)
    )
    need(
        drift_trace == (1, -1, 1, -1) and parity_drift == (1,) * 4,
        "alias survivor control",
    )
    sampled = tuple(tick(u4, 2 * t) for t in range(3))
    need(
        sampled[0] == sampled[2] and sampled[1] == tuple(-a for a in u4),
        "stride-two aliases C4 to real sign",
    )
    parity_sampled = tuple(tick(p2, 2 * t) for t in range(3))
    need(
        parity_sampled[0] == parity_sampled[1] == parity_sampled[2],
        "stride-two aliases parity to stationary",
    )

    # The time-domain comparator gives a second model of period matching,
    # independent of the star-interface transfer matrices above.
    u = MODES[3] * 4
    v = MODES[4] * 3
    cross_modes = scan(u, v)
    need(
        not any(cross_modes),
        "distinct held pure modes must be orthogonal even under phase offsets",
    )
    return {
        "oriented_harmonic_reads": orbits,
        "relative_stride_two_on_C4_fundamental": tuple(map(str, drift_trace)),
        "relative_stride_two_on_C4_parity": tuple(map(str, parity_drift)),
        "co_clocked_C12_period3_vs_period4_all_delays": tuple(map(str, cross_modes)),
    }


def probe():
    return {
        "scope": "finite rational real signal scattering over unsigned cyclic timing addresses; no microscopic complex state, outcome probability, or physical clock derived",
        "phase_algebra": phase_algebra(),
        "maximal_covariant_transfer": rank_controls(),
        "C12_centered_transferred_norm_fractions": selective_interface(),
        "externally_periodic_conversion": driven_conversion(),
        "timing_and_relative_order_controls": timing_controls(),
        "assumptions": [
            "linear coherent signals or calibrated deviations across clock-addressed channels; standalone unsigned marks do not carry amplitudes",
            "physical one-tick law, orientation and matched fibre wiring as resources; differing strides or an externally modulated converter changes the interface class",
            "real star operations with coherent summing and calibrated square-norm only in the comparator; no Born or event frequencies",
            "uniform independent phase average only for that control, not the general behavior of sources prepared independently",
        ],
        "repo_distinction": "three-state phase controller and packet eigenclock already use Fourier sectors or references; here the new discriminator is covariant phase transfer between unequal clock rings with exact rank and explicit lossless interface, plus selective C12 routing",
    }


if __name__ == "__main__":
    print(json.dumps(probe(), sort_keys=True, separators=(",", ":")))
