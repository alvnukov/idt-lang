"""Blind ranging with diffusing pulses, not shortest clocks or a wave cone.

The generator is the least retrace, abc=cba path quotient (see
probe_internal_signal_geometry.py). At even roles it counts words, not
distances: two sweeps of n independent port choices, one of each sign.
Interleaving them gives the original n alternating tick pairs. Signed
multiplicities implement endpoint equality; only the generator sees them.

The reader sees opaque stationary tags, a clock horizon, and ratios of arrival
counts to a colocated return. It receives no port names, differences, dimension,
or true metric. We supply comparable preparations, translation-invariant
sampling, common clocks, identifiable receivers, and unlimited counting
precision. A beacon is parked during each fix. Its sequence of positions is a
scripted test of constant displacement per fix, not a propagating particle.

Why compare n(1-K_n(x)/K_n(0))? On this *infinite least quotient*, delete
one redundant count. With positive port probabilities p, choose one reference
letter with phase zero. The one-pair Fourier multiplier is
    phi(k) = |sum_j p_j exp(i k_j)|^2.
On the d-torus it equals one only at 0; there
    phi(k) = 1 - k^T A k + O(|k|^4),  A=diag(p')-p' p'^T > 0
for the nonreference probabilities p'. The return integral has weight
phi(k)^n; subtracting the displaced integral inserts 1-cos(k.x). Outside a
fixed small neighborhood the weight decays exponentially. Inside, rescale
k=u/sqrt(n): a Gaussian times a constant or a quadratic dominates the two
rescaled integrands, by the positive quadratic bound. The limiting normalized
second moment gives (1/4) x^T A^{-1} x, or (1/4) sum_j x_j^2/p_j with all
zero-sum counts restored. This is a fixed-displacement limit, not uniform
over growing ranges. Compact quotients and missing ports need not obey it.

At each finite n the arrival kernel is the autocorrelation of the finite
one-sweep distribution. Distinct translates on the infinite quotient are
linearly independent (a nonzero Laurent polynomial has no annihilator).
Thus the chordal Gram rank for m distinct tags is exactly m-1, NOT d. We
report that exact finite rank separately from resolved pivots at a declared
relative tolerance n^(-1/2); no universal estimator is certified by a fixture.
"""

from fractions import Fraction as F
from functools import cache
from itertools import pairwise, product
from math import ceil, comb


def need(test, reason):
    if not test:
        raise ValueError(reason)


@cache
def choices(n):
    return tuple(tuple(comb(j, k) for k in range(j + 1)) for j in range(n + 1))


@cache
def coefficient(n, signature):
    """Coefficient for plus/minus multinomials, integer even for biased walks."""
    choose = choices(n)
    old, surplus = [1] + [0] * n, 0
    for channel, (w, z) in enumerate(signature):
        new = [0] * (n + 1)
        powers = [w**i for i in range(2 * n + 1)]
        for m, v in enumerate(old):
            if not v:
                continue
            # Previous minus/plus totals: m and m+surplus. Add k and k+z.
            # On the last channel no partial coefficient is queried.
            start = n - m if channel + 1 == len(signature) else 0
            for k in range(max(start, -z), min(n - m, n - m - surplus - z) + 1):
                a, b = m + k, m + surplus + k + z
                new[a] += v * choose[a][k] * choose[b][k + z] * powers[2 * k + z]
        old, surplus = new, surplus + z
    need(surplus == 0, "receivers must have the emitting role")
    return old[n]


def count(n, weights, delta):
    # Permuting (weight, difference) pairs and reversing all differences
    # preserve counts. Cache only the generator, never the reader's result.
    signature = min(
        tuple(sorted(zip(weights, (s * v for v in delta), strict=True)))
        for s in (-1, 1)
    )
    return coefficient(n, signature)


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def fixtures(ports):
    """Port paths specify the fixture only; both arities yield nine blank tags."""

    def station(*pairs):
        x = [0] * ports
        for plus, minus in pairs:
            x[plus] += 1
            x[minus] -= 1
        return tuple(x)

    spokes = [(i, 0) for i in range(1, ports)]
    unit = [item for i, j in spokes for item in ((i, j), (j, i))]
    unit += [(2, 1), (3, 1)]
    # Same fixed scrambled order and returned format for both arities.
    order = (5, 0, 3, 6, 1, 7, 2, 4)
    sites = [station()] + [station(unit[i]) for i in order]
    poses = [station((2, 3), *([(0, 1)] * t)) for t in range(3)]
    need(len(set(sites)) == 9, "tags must be distinct")
    return sites, poses


def collect(n, weights):
    sites, poses = fixtures(len(weights))
    ret = count(n, weights, sub(sites[0], sites[0]))

    def line(x):
        return [F(count(n, weights, sub(x, y)), ret) for y in sites]

    return [line(x) for x in sites], [line(x) for x in poses]


def gram_pivots(dist):
    """Complete diagonal pivoting on the reference-centered squared ranges."""
    size = len(dist)
    g = [
        [(dist[0][i] + dist[0][j] - dist[i][j]) / 2 for j in range(size)]
        for i in range(size)
    ]
    a = [row[:] for row in g]
    rest, pivots = list(range(1, size)), []
    while rest:
        k = max(rest, key=lambda i: a[i][i])
        v = a[k][k]
        if not v:
            need(all(a[i][j] == 0 for i in rest for j in rest), "indefinite Gram")
            break
        need(v > 0, "negative Gram pivot")
        pivots.append((k, v))
        rest.remove(k)
        for i in rest:
            for j in rest:
                a[i][j] -= a[i][k] * a[k][j] / v
    return g, pivots


def solve(a, b):
    """Positive definite pivot submatrix, exact symmetric Gram solve."""
    mat = [row + [v] for row, v in zip(a, b, strict=True)]
    for j in range(len(mat)):
        mat[j] = [x / mat[j][j] for x in mat[j]]
        for i in range(len(mat)):
            if i != j:
                mat[i] = [
                    x - mat[i][j] * y for x, y in zip(mat[i], mat[j], strict=True)
                ]
    return [row[-1] for row in mat]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def blind_forecast(n, anchor_returns, observe):
    """Only requests the two fixes at selected anchors; never sees fix three."""
    d = [[n * (1 - x) for x in row] for row in anchor_returns]
    g, pivots = gram_pivots(d)
    # Compare positive rational pivots to first/sqrt(n), no float comparisons.
    keep = [k for k, v in pivots if n * v**2 > pivots[0][1] ** 2]
    basis = [[g[i][j] for j in keep] for i in keep]

    def fix(t):
        r0 = n * (1 - observe(t, 0))
        return [(r0 + d[0][i] - n * (1 - observe(t, i))) / 2 for i in keep]

    b0, b1 = fix(0), fix(1)
    b2 = [2 * y - x for x, y in zip(b0, b1, strict=True)]
    coords = solve(basis, b2)
    radius = dot(coords, b2)
    prediction = [
        radius + d[0][i] - 2 * dot(coords, [g[i][j] for j in keep])
        for i in range(len(g))
    ]
    return (
        len(pivots),
        len(keep),
        prediction,
        [k for k in range(len(g)) if k not in [0, *keep]],
    )


def experiment(n, weights):
    am, fixes = collect(n, weights)
    # The withheld row is inaccessible via the training reader's callback.
    earlier = fixes[:2]
    exact, resolved, pred, unused = blind_forecast(n, am, lambda t, i: earlier[t][i])
    target = [n * (1 - a) for a in fixes[2]]
    # Normalize by the largest withheld range, not by a hidden unit or position.
    error = max(abs(x - y) for x, y in zip(pred, target, strict=True)) / max(target)
    # Rival fixture: same first two fixes, but the beacon turns back at the
    # second fix. It now returns to its starting pose. The training observations
    # cannot choose between these futures; scoring is separate in both cases.
    turnback = [n * (1 - a) for a in fixes[0]]
    rival_error = max(abs(x - y) for x, y in zip(pred, turnback, strict=True)) / max(
        turnback
    )
    return exact, resolved, error, len(unused), rival_error


def other_observers(n, weights):
    """Give every tag its own origin and change the order of all other tags."""
    table, fixes = collect(n, weights)
    span, errors = [], []
    for origin in range(len(table)):
        order = [(origin - j) % len(table) for j in range(len(table))]
        renamed = [[table[i][j] for j in order] for i in order]
        earlier = [[row[j] for j in order] for row in fixes[:2]]
        _, resolved, pred, _ = blind_forecast(
            n, renamed, lambda t, i, rows=earlier: rows[t][i]
        )
        target = [n * (1 - fixes[2][j]) for j in order]
        span.append(resolved)
        errors.append(
            max(abs(x - y) for x, y in zip(pred, target, strict=True)) / max(target)
        )
    return set(span), max(errors)


def control_counts():
    # Compare DP to independent enumeration of every four-tick pulse.
    from collections import Counter

    weights = (1, 1, 1, 3)
    observed = Counter()
    for word in product(range(4), repeat=4):
        x, w = [0] * 4, 1
        for i, port in enumerate(word):
            x[port] += 1 if i % 2 == 0 else -1
            w *= weights[port]
        observed[tuple(x)] += w
    need(sum(observed.values()) == sum(weights) ** 4, "all pulse words counted")
    need(all(count(2, weights, x) == w for x, w in observed.items()), "enumeration")


def independent_trial_cost(n):
    """Variance of two independent binomial proportions, not a confidence bound."""
    w = (1, 1, 1, 1)
    words = sum(w) ** (2 * n)
    p0 = F(count(n, w, (0, 0, 0, 0)), words)
    p1 = F(count(n, w, (1, -1, 0, 0)), words)
    # With N shots per receiver the variance of the estimated difference is
    # (p0*(1-p0)+p1*(1-p1))/N. One standard deviation is NOT reliable recovery.
    return ceil((p0 * (1 - p0) + p1 * (1 - p1)) / (p0 - p1) ** 2)


def rival_rulers(n):
    # On the unwrapped cover two directed single-pair displacements were
    # exchangeable; bias changes operational lengths on that very same cover.
    u, v, zero = (1, -1, 0, 0), (1, 0, 0, -1), (0, 0, 0, 0)
    w = (1, 1, 1, 3)
    central = count(n, w, zero)
    bias_ratio = F(central - count(n, w, u), central - count(n, w, v))
    fair = (1, 1, 1, 1)
    need(count(n, fair, u) == count(n, fair, v), "fair orientation exchange")
    need(count(n, (1, 1, 1, 0), v) == 0, "absent channel: a station never responds")
    # Compact mod-two endpoint equality. Count the same two-pulse ticks,
    # now using only bit flips and station equality.
    a = [1] + [0] * 15
    for _ in range(2 * n):
        a = [sum(a[s ^ (1 << j)] for j in range(4)) for s in range(16)]
    wrapped = n * (1 - F(a[3], a[0]))
    # Tree with only retraces: counts per individual receiver at radius r.
    a = [1] + [0] * (2 * n + 2)
    for _ in range(2 * n):
        a = [4 * a[1], *(a[r - 1] + 3 * a[r + 1] for r in range(1, len(a) - 1)), 0]
    tree = n * (1 - F(a[2], a[0]))
    return bias_ratio, wrapped, tree


def main():
    control_counts()
    # Keep the initially unresolved horizons and continue doubling, without
    # changing the tolerance to give a preferred low dimension.
    horizons = (16, 32, 64, 128, 256, 512)
    for weights in ((1, 1, 1, 1), (1, 1, 1, 1, 1)):
        rows = [experiment(n, weights) for n in horizons]
        exact, resolved, error, unused, rival = zip(*rows, strict=True)
        need(set(exact) == {8}, "finite rank is full")
        need(resolved[-1] == len(weights) - 1, "late resolved rank")
        need(unused[-1] > 0, "late forecast tests additional stations")
        need(all(a > b for a, b in pairwise(error)), "held-out forecast improves")
        need(rival[-1] > 1 > error[-1], "same past, distinguishable future")
        print(
            f"{len(weights)}-port fair generator, n={horizons}: finite ranks {exact}; "
            f"resolved {resolved}; maximum next-fix squared-range error / largest squared range "
            f"{tuple(round(float(e), 5) for e in error)} (nine tags in both worlds)."
        )
        print(
            f"At the last horizon, {unused[-1]} stations were unused in both moving "
            f"fixes; if the beacon turns back, the same forecast's error is "
            f"{float(rival[-1]):.5f} of that world's largest squared range."
        )
        ranks, worst = other_observers(horizons[-1], weights)
        need(ranks == {resolved[-1]}, "late dimension under change of origin")
        print(
            f"All nine reference choices resolve {resolved[-1]}; worst normalized "
            f"forecast error across these frames: {float(worst):.5f}."
        )
    rivals = [rival_rulers(n) for n in horizons[:3]]
    ratios, wraps, trees = zip(*rivals, strict=True)
    need(
        abs(ratios[2] - F(3, 2)) < abs(ratios[0] - F(3, 2)) and ratios[0] > 1,
        "sampler-dependent length ratio",
    )
    need(
        0 < wraps[2] < wraps[1] < wraps[0] and trees[2] > trees[1] > trees[0] > 1,
        "collapsed compact ruler vs diverging tree ruler",
    )
    print(
        "Rivals at n=(16,32,64): equal fair squared lengths; weighted length-squared "
        f"ratios {tuple(round(float(r), 5) for r in ratios)} (limit 3/2). "
        "An omitted port leaves one tag silent."
    )
    print(
        "One fixed two-link displacement: mod-two squared ruler "
        f"{tuple(format(float(r), '.3g') for r in wraps)}; four-regular tree "
        f"{tuple(round(float(r), 4) for r in trees)}."
    )
    print(
        f"Four-port horizon {horizons[-1]}: one-standard-deviation separation of "
        f"self vs a two-link receiver requires {independent_trial_cost(horizons[-1]):,} "
        "independent shots per receiver in the simple difference experiment."
    )
    print(
        "Station tags, comparable clocks and samples, and the moving track are supplied; "
        "no unique topology, physical rods, inertial law or wave speed follows."
    )


if __name__ == "__main__":
    main()
