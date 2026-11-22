"""Exact finite replay of a cube readout/parity tradeoff, not a derivation of QM.

The preparation n is uniform on the cube. The full received record L has law
mu_n, independent of the subsequent uniformly chosen request for one bit i.
All trials have an output, with no discarded/no-click outcomes. For each
nonempty S, a_S(L) = (1/8) sum_n chi_S(n) mu_n(L) is half the difference in
probability at L between the two parity ensembles. Thus TV_S = sum_L |a_S(L)|,
and the optimal bit score is P = 1/2 + sum_i TV_{i}/6.

Condition on a positive-mass L and flip each cube coordinate to make its
posterior singleton mean nonnegative. Write U for their sum, V for the sum
of aligned pair moments, and W for the aligned triple moment. Positivity at
the all-negative vertex gives U <= 1+V-W. On every aligned vertex x,
3 sum_i x_i - 5 <= sum_{i<j} x_i*x_j + x_0*x_1*x_2: the gaps for 0,1,2,3
negative coordinates are 0,0,8,16. Taking the posterior expectation gives
3U <= 5+V+W. In both cases the signed higher moments are bounded by their
absolute sum. Average over L, using the unchanged magnitudes after alignment:
P <= 1/2 + min(1+R,(5+R)/3)/6, where R sums pair and triple TVs.

A uniformly selected subset of size k, with its values and identity retained,
has singleton TV k/3 and R = 0,1,4 for k = 1,2,3 respectively. Tagged adjacent
mixtures attain the envelope all along [0,4]. The prescribed cube Bloch
vectors n/sqrt(3) with Cartesian projective readout have P=(1+1/sqrt(3))/2.
The low branch therefore forces R >= sqrt(3)-1; a share s=sqrt(3)-1 of pair
messages mixed with single messages attains it. This is an exact algebraic
threshold under the stated assumptions, not a fitted parameter or measured TV.
Report the requested bit when visible and toss a fair coin otherwise to get
the prescribed Cartesian responses at every input, not only the mean score.

For a finite qubit POVM with rows a_j(1+r_j.n/sqrt(3)), ||r_j||_2 <= 1,
the total absolute slope demand on k axes is at most sqrt(k/3), tight for
opposite projective directions uniform in magnitude on those axes. To route
affine decoders, the adjacent single/pair message lane capacities for these
subsets of axes are (1+s)/3, (2+s)/3, 1. At s=sqrt(3)-1, the first equals
1/sqrt(3); the second squared exceeds 2/3 by 2(sqrt(3)-1)/9; the third is
1. The singleton bound is also necessary by TV contraction on two adjacent
inputs. The same nonnegative affine routing argument works over the reals;
this executable tests rational cases, not all POVMs. The decoder may depend
on the requested POVM as a whole.

The uniform zero-or-one-flip ball channel has singleton, pair and triple TVs
1/2, 0, 1/2 respectively. Its mixture with pair messages attains the ideal
Cartesian score at ball share b=4-2sqrt(3), also with R=sqrt(3)-1. Reporting
the requested coordinate of the ball output realizes the same gain 1/2 on
every input and axis, so the mixture attains the full Cartesian table. However,
the +++ body-diagonal projector requires endpoint responses 1 at +++ and 0 at
---. Their disjoint ball supports cover the ball records, fixing that part
of the decoder and inducing an input triple coefficient b/8. Any pair-message
decoder depends only on its two visible coordinates and contributes zero
triple coefficient. Thus the mixture at any b>0 fails this affine projector,
even though the ideal Cartesian score is attainable at the stated share.
"""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from typing import TYPE_CHECKING, TypeVar

if TYPE_CHECKING or __package__:
    from scripts import probe_erased_bit_readouts as erased
else:
    import probe_erased_bit_readouts as erased

T = TypeVar("T")
AXES, CUBE, SIGNS = erased.AXES, erased.CUBE, erased.SIGNS
check = erased.check
Effect = erased.Effect
Law = erased.Law
Point = erased.Point
Channel = dict[Point, dict[T, F]]
Axes = tuple[int, ...]
Message = tuple[Axes, tuple[int, ...]]
MIXED_LANES = tuple(s for k in (1, 2) for s in combinations(AXES, k))
PARITIES = (*MIXED_LANES, AXES)


def parity(n: Point, axes: Axes) -> int:
    return prod(n[i] for i in axes)


def channel_tvs(channel: Channel[T]) -> tuple[F, ...]:
    check(set(channel) == set(CUBE), "channel must cover the cube")
    for row in channel.values():
        check(sum(row.values()) == 1 and min(row.values()) >= 0, "invalid channel row")
    tvs = []
    for axes in PARITIES:
        signed: defaultdict[T, F] = defaultdict(F)
        ensembles: dict[int, defaultdict[T, F]] = {x: defaultdict(F) for x in SIGNS}
        for n, row in channel.items():
            x = parity(n, axes)
            for signal, weight in row.items():
                signed[signal] += x * weight / 8
                ensembles[x][signal] += weight / 4
        tv = sum(map(abs, signed.values()), F(0))
        check(tv == erased.distance(ensembles[-1], ensembles[1]), "TV identity")
        tvs.append(tv)
    optimal_hits = F(0)
    for i in AXES:
        joint: defaultdict[tuple[int, T], F] = defaultdict(F)
        for n, row in channel.items():
            for signal, weight in row.items():
                joint[n[i], signal] += weight / 8
        optimal_hits += sum(
            max(joint[-1, signal], joint[1, signal])
            for signal in {signal for _, signal in joint}
        )
    check(optimal_hits / 3 == success(tuple(tvs)), "optimal success identity")
    check(success(tuple(tvs)) <= envelope(sum(tvs[3:], F(0))), "envelope violation")
    return tuple(tvs)


def success(tvs: tuple[F, ...]) -> F:
    return F(1, 2) + sum(tvs[:3], F(0)) / 6


def envelope(leakage: F) -> F:
    return F(1, 2) + min(1 + leakage, (5 + leakage) / 3) / 6


def reveal_channel(weights: dict[Axes, F]) -> Channel[Message]:
    return {
        n: {(s, tuple(n[i] for i in s)): w for s, w in weights.items() if w}
        for n in CUBE
    }


def adjacent_reveal(k: int, upper_share: F) -> dict[Axes, F]:
    weights: dict[Axes, F] = {}
    for size, share in ((k, 1 - upper_share), (k + 1, upper_share)):
        lanes = tuple(combinations(AXES, size))
        weights.update({s: share / len(lanes) for s in lanes})
    return weights


def verify_sharpness() -> None:
    for n in CUBE:
        u = sum(n)
        v = sum(parity(n, s) for s in PARITIES[3:6])
        w = parity(n, AXES)
        check(1 - u + v - w == prod(1 - x for x in n), "vertex positivity identity")
        check(v + w - (3 * u - 5) == (0, 0, 8, 16)[n.count(-1)], "vertex gap")
    for values in product((0, 1), repeat=len(CUBE)):
        channel_tvs({n: {y: F(1)} for n, y in zip(CUBE, values, strict=True)})
    for k in (1, 2):
        for den in range(1, 9):
            for num in range(den + 1):
                s = F(num, den)
                tvs = channel_tvs(reveal_channel(adjacent_reveal(k, s)))
                expected_r = s if k == 1 else 1 + 3 * s
                check(tvs[:3] == (F(k, 3) + s / 3,) * 3, "singleton reveal TV")
                check(sum(tvs[3:]) == expected_r, "reveal mixture leakage")
                check(success(tvs) == envelope(expected_r), "unattained envelope")
    # Positive squares certify 0 < sqrt(3)-1 < 1 and that 1/sqrt(3)
    # requires a strictly intermediate share: 1/3 < 1/sqrt(3) < 2/3.
    check(F(1, 9) < F(1, 3) < F(4, 9), "threshold branch")
    print("sharp envelope: 8 vertices, 256 binary channels, 88 rational mixtures")
    print("ideal Cartesian score=(1+1/sqrt(3))/2 requires R_min=sqrt(3)-1")


def lane_flows(masses: tuple[F, ...], share: F) -> dict[Axes, tuple[F, ...]]:
    weights = adjacent_reveal(1, share)
    for axes in PARITIES:
        demand = sum(masses[i] for i in axes)
        capacity = sum(w for lane, w in weights.items() if set(lane) & set(axes))
        expected = ((1 + share) / 3, (2 + share) / 3, F(1))[len(axes) - 1]
        check(capacity == expected, "subset capacity formula")
        if demand > capacity:
            raise ValueError(f"routing cut fails on axes {axes}")

    # Fill the private single-axis lanes first. An admissible flow can always
    # do this: moving any of that axis's shared load into its private lane
    # frees shared capacity. Scale remaining demands to the existing solver.
    single = tuple(min(masses[i], weights[(i,)]) for i in AXES)
    residual = tuple((masses[i] - single[i]) / share if share else F(0) for i in AXES)
    edge_flow = erased.allocate(residual)
    flows: dict[Axes, tuple[F, ...]] = {
        (i,): tuple(single[i] if j == i else F(0) for j in AXES) for i in AXES
    }
    for k in AXES:
        flows[tuple(i for i in AXES if i != k)] = tuple(share * f for f in edge_flow[k])
    for s, flow in flows.items():
        check(
            all(f >= 0 and (i in s or f == 0) for i, f in enumerate(flow))
            and sum(flow) <= weights[s],
            "invalid flow",
        )
    for i in AXES:
        check(sum(f[i] for f in flows.values()) == masses[i], "unfilled axis demand")
    return flows


def mixed_decoder(effects: tuple[Effect, ...], share: F) -> dict[Message, Law]:
    check(0 <= share <= 1, "invalid pair share")
    check(
        sum(a for a, _ in effects) == 1
        and all(len(g) == 3 and sum(map(abs, g)) <= a for a, g in effects)
        and all(sum(g[i] for _, g in effects) == 0 for i in AXES),
        "target is not a positive normalized affine table",
    )
    weights = adjacent_reveal(1, share)
    masses = tuple(sum((abs(g[i]) for _, g in effects), F(0)) for i in AXES)
    flows = lane_flows(masses, share)
    slopes = {
        s: [
            tuple(flow[i] * g[i] / masses[i] if masses[i] else F(0) for i in s)
            for _, g in effects
        ]
        for s, flow in flows.items()
    }
    intercepts = {s: [sum(map(abs, g), F(0)) for g in gs] for s, gs in slopes.items()}
    room = {s: weights[s] - sum(xs) for s, xs in intercepts.items()}
    check(min(room.values()) >= 0, "negative lane intercept slack")
    for j, (a, _) in enumerate(effects):
        need = a - sum(xs[j] for xs in intercepts.values())
        check(need >= 0, "negative effect intercept slack")
        for s, xs in intercepts.items():
            fill = min(room[s], need)
            xs[j] += fill
            room[s] -= fill
            need -= fill
        check(need == 0, "unfilled effect intercept slack")
    check(all(r == 0 for r in room.values()), "unfilled lane intercept slack")
    decoder = {}
    for s, w in weights.items():
        if w == 0:
            continue
        for values in product(SIGNS, repeat=len(s)):
            row = tuple(
                (a + sum(g_i * x_i for g_i, x_i in zip(g, values, strict=True))) / w
                for a, g in zip(intercepts[s], slopes[s], strict=True)
            )
            check(min(row) >= 0 and sum(row) == 1, "invalid decoder row")
            decoder[s, values] = row
    return decoder


def verify_routing() -> None:
    diagonal = tuple((F(1, 2), (F(x, 6),) * 3) for x in SIGNS)
    cartesian = tuple((F(1, 2), (F(x * 2, 7), F(0), F(0))) for x in SIGNS)
    planar = tuple((F(1, 2), (F(x, 5), F(-x, 5), F(0))) for x in SIGNS)
    tetrahedra = tuple(
        erased.tetra_effects(tuple(n for n in CUBE if prod(n) == x)) for x in SIGNS
    )
    fixtures = (diagonal, cartesian, planar, *tetrahedra)
    for effects in fixtures:
        check(
            all(sum(g_i**2 for g_i in g) * 3 <= a**2 for a, g in effects),
            "supplied fixture is not a qubit POVM",
        )
    check(
        F(1, 4) < F(16, 49) < F(1, 3) < F(49, 144),
        "Cartesian fixture versus singleton capacities at s=1/2 and 3/4",
    )
    for share in (F(3, 4), F(1)):
        for effects in fixtures:
            decoder = mixed_decoder(effects, share)
            for n, weights in reveal_channel(adjacent_reveal(1, share)).items():
                check(
                    erased.apply_channel(weights, decoder)
                    == erased.probabilities(effects, n),
                    "routing replay",
                )
    try:
        mixed_decoder(cartesian, F(1, 2))
    except ValueError as error:
        check(str(error) == "routing cut fails on axes (0,)", "wrong low-share control")
    else:
        raise RuntimeError("insufficient share admitted a Cartesian readout")
    for n, m in combinations(CUBE, 2):
        if sum(x != y for x, y in zip(n, m, strict=True)) == 1:
            for s in (F(0), F(1, 2), F(3, 4), F(1)):
                channel = reveal_channel(adjacent_reveal(1, s))
                check(
                    erased.distance(channel[n], channel[m]) == (1 + s) / 3,
                    "adjacent TV",
                )
            if n[0] != m[0]:
                p = erased.probabilities(cartesian, n)
                q = erased.probabilities(cartesian, m)
                check(
                    sum(abs(a - b) for a, b in zip(p, q, strict=True)) / 2 == F(4, 7),
                    "target TV",
                )
    print(
        "qubit controls: exact affine decoders at s=3/4 and 1; s=1/2 fails singleton cut"
    )


def verify_ball_control() -> None:
    ball = {
        n: {
            m: F(1, 4)
            for m in CUBE
            if sum(a != b for a, b in zip(n, m, strict=True)) <= 1
        }
        for n in CUBE
    }
    tvs = channel_tvs(ball)
    check(tvs == (F(1, 2),) * 3 + (F(0),) * 3 + (F(1, 2),), "ball moments")
    check(success(tvs) == F(3, 4), "ball score")
    check(F(1, 4) < F(1, 3) < F(4, 9), "ideal gain does not bracket ball/pair gains")
    top, bottom = CUBE[-1], CUBE[0]
    check(
        not (ball[top].keys() & ball[bottom].keys()), "ball supports must be disjoint"
    )
    check(
        ball[top].keys() | ball[bottom].keys() == set(CUBE),
        "ball endpoints cover records",
    )
    forced = {
        n: sum((p for v, p in ball[n].items() if v in ball[top]), F(0)) for n in CUBE
    }
    affine = {n: F(1, 2) + F(sum(n), 6) for n in CUBE}
    check(
        (forced[top], forced[bottom]) == (affine[top], affine[bottom]) == (F(1), F(0)),
        "diagonal endpoints",
    )
    pair = reveal_channel(adjacent_reveal(1, F(1)))
    for msg in {m for row in pair.values() for m in row}:
        check(
            sum(parity(n, AXES) * pair[n].get(msg, F(0)) for n in CUBE) == 0,
            "pair basis triple",
        )
    check(sum(parity(n, AXES) * affine[n] for n in CUBE) == 0, "affine target triple")
    ball_triple = sum(parity(n, AXES) * forced[n] for n in CUBE) / 8
    check(ball_triple == F(1, 8), "forced ball triple term")
    for b in (F(1, 4), F(1, 2), F(3, 4)):
        mixed = {
            n: {
                **{(AXES, v): b * p for v, p in ball[n].items()},
                **{m: (1 - b) * p for m, p in pair[n].items()},
            }
            for n in CUBE
        }
        tvs = channel_tvs(mixed)
        check(tvs[:3] == (F(2, 3) - b / 6,) * 3, "ball/pair Cartesian gain")
        check(tvs[3:] == ((1 - b) / 3,) * 3 + (b / 2,), "ball/pair higher TVs")
        check(success(tvs) == envelope(1 - b / 2), "ball/pair envelope saturation")
    print(
        "ball control: P=3/4; mixing with pair messages forces a nonaffine diagonal term b/8"
    )


def main() -> None:
    verify_sharpness()
    verify_routing()
    verify_ball_control()


if __name__ == "__main__":
    main()
