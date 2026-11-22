"""Exchangeable extension plus a collision observable as a sampling candidate.

This is a statement about labels actually compared by a detector. It does
not turn a shuffled output log into chronological exchangeability, or infer
independence of hidden fine labels from an independent coarse readout.
No imported experiment, fitted constant, or formal claim status.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


def falling(n: int, k: int) -> int:
    return prod(range(n - k + 1, n + 1)) if 0 <= k <= n else 0


def conditional_word(k: int, n: int, hits: int, length: int) -> F:
    """One specified word with hits ones, sampled from k ones among n."""
    return F(falling(k, hits) * falling(n - k, length - hits), falling(n, length))


def extremal(n: int) -> dict[int, F]:
    """Distribution of total sign S for maximal three-sign parity."""
    if n % 2:
        return {-1: F(n, n + 1), n: F(1, n + 1)}
    return {-2: F(n, 2 * (n + 2)), 0: F(1, 2), n: F(1, n + 2)}


def max_vertex_third(n: int) -> F:
    """Independent moment-polytope vertex check, no assumed extremal law.

    Three linear constraints on the distribution: mass 1, mean 0 and
    second moment n. An extreme point has at most three nonzero entries.
    The three weights below are expectations of Lagrange basis polynomials.
    """
    best = F(-(n**3))
    for a, b, c in combinations(range(-n, n + 1, 2), 3):
        weights = tuple(
            F(n + y * z, (x - y) * (x - z))
            for x, y, z in ((a, b, c), (b, a, c), (c, a, b))
        )
        if min(weights) >= 0:
            best = max(
                best,
                sum((w * s**3 for w, s in zip(weights, (a, b, c), strict=True)), F(0)),
            )
    return best


def finite_bits() -> None:
    for n in range(3, 22):
        law = extremal(n)
        values = range(-n, n + 1, 2)
        # Exact nonnegative polynomials on the actual parity grid.
        need(
            all(
                (n - s) * ((s + 1) ** 2 if n % 2 else s * (s + 2)) >= 0 for s in values
            ),
            "dual certificate",
        )
        need(
            sum(law.values()) == 1
            and sum(w * s for s, w in law.items()) == 0
            and sum(w * s * s for s, w in law.items()) == n,
            "first two moments",
        )
        cubic = sum((w * s**3 for s, w in law.items()), F(0))
        need(cubic == max_vertex_third(n), "primal/dual mismatch")
        parity = F(0)
        for t in (1, 2, 3):
            for word in product((0, 1), repeat=t):
                p = sum(
                    (
                        w * conditional_word((n + s) // 2, n, sum(word), t)
                        for s, w in law.items()
                    ),
                    F(0),
                )
                if t <= 2:
                    need(p == F(1, 2**t), "pairwise fair law")
                else:
                    parity += p * prod(2 * b - 1 for b in word)
        sharp = F(1, n - 2 if n % 2 else n - 1)
        need(parity == cubic / falling(n, 3) == sharp, "three-record extremum")
        # The same polynomial bounds survive bias and a nonzero pair sign
        # correlation. Check each count shell, hence all their mixtures.
        for s in values:
            m = F(s, n)
            r = F(s * s - n, falling(n, 2))
            third = F(s**3 - (3 * n - 2) * s, falling(n, 3))
            need(abs(third + sharp * m) <= sharp + r, "robust shell bound")
    print(
        "Exchangeable fair pairwise-independent bits: sharp |three-sign parity| ≤1/(N−2) at odd N, 1/(N−1) at even N; exact extrema checked N=3..21."
    )


def label_variance(counts: tuple[int, ...]) -> None:
    n, h = sum(counts), len(counts)
    equal = F(sum(x * (x - 1) for x in counts), n * (n - 1))
    spread = sum(((F(x, n) - F(1, h)) ** 2 for x in counts), F(0))
    need(
        spread == (1 - F(1, h)) / n + F(n - 1, n) * (equal - F(1, h)),
        "finite composition identity",
    )


def tv_against_uniform(counts: tuple[int, ...], k: int) -> F:
    n, h = sum(counts), len(counts)
    total = F(0)
    for word in product(range(h), repeat=k):
        c = Counter(word)
        p = F(prod(falling(x, c[i]) for i, x in enumerate(counts)), falling(n, k))
        total += abs(p - F(1, h**k))
    return total / 2


def check_tv(counts: tuple[int, ...], k: int) -> None:
    n, h = sum(counts), len(counts)
    spread = sum(((F(x, n) - F(1, h)) ** 2 for x in counts), F(0))
    collision = 1 - F(falling(n, k), n**k)
    # TV <= collision + k/2 sqrt(h E||f-u||²), including mixtures by
    # convexity + Jensen. Test the bound in exact rational arithmetic.
    excess = max(F(0), tv_against_uniform(counts, k) - collision)
    need(4 * excess**2 <= k * k * h * spread, "sampling without-replacement coupling")


def fair_marginal_control() -> None:
    """With Ef uniform the linear term of E[f tensor ... tensor f] vanishes.

    Taylor-expand the k-fold product along u+t(f-u). Remaining terms in its
    second derivative have L1 norm <= k(k-1)||f-u||_1^2, since the other
    k-2 factors are probability laws. Integrate with weight (1-t) and
    divide by two for TV. Add the separate repeated-index coupling cost.
    A chance collision by itself does NOT give the fair marginal at finite N.
    """
    for n in range(3, 11):
        for a in range(n // 2 + 1):
            for b in range((n + 1) // 2, n + 1):
                if a == b:
                    continue
                w = (F(b) - F(n, 2)) / (b - a)
                mix = ((w, a), (1 - w, b))
                delta2 = sum(weight * (2 * F(x, n) - 1) ** 2 for weight, x in mix)
                for k in range(1, min(n, 4) + 1):
                    err = F(0)
                    for word in product((0, 1), repeat=k):
                        p = sum(
                            weight * conditional_word(x, n, sum(word), k)
                            for weight, x in mix
                        )
                        err += abs(p - F(1, 2**k))
                    need(
                        err / 2
                        <= 1 - F(falling(n, k), n**k) + k * (k - 1) * delta2 / 4,
                        "fair-marginal second-order control",
                    )
    for s in range(2, 10):
        n, x = s * s, (s * s + s) // 2
        equal = conditional_word(x, n, 2, 2) + conditional_word(x, n, 0, 2)
        need(
            equal == F(1, 2) and F(x, n) - F(1, 2) == F(1, 2 * s),
            "square-root bias with chance collision",
        )


def stationary_control() -> None:
    """Stationary random offset of independent (A,B,AB) sign blocks."""
    counts: Counter[tuple[int, ...]] = Counter()
    for phase in range(3):
        for signs in product((-1, 1), repeat=6):
            seq = tuple(
                x
                for i in (0, 2, 4)
                for x in (signs[i], signs[i + 1], signs[i] * signs[i + 1])
            )
            counts[seq[phase : phase + 7]] += 1
    size = sum(counts.values())
    for i, j in combinations(range(7), 2):
        for a, b in product((-1, 1), repeat=2):
            need(
                sum(v for s, v in counts.items() if s[i] == a and s[j] == b) * 4
                == size,
                "not pairwise uniform",
            )

    def third(indices: tuple[int, ...]) -> F:
        return F(sum(v * prod(s[i] for i in indices) for s, v in counts.items()), size)

    need(
        third((0, 1, 2)) == F(1, 3) and third((0, 3, 6)) == 0,
        "stationary but not exchangeable",
    )
    # Fixed three-quarter ones, one-quarter zeros in an exchangeable
    # four-shot window: chance adjacent collision without a fair marginal.
    need(
        conditional_word(3, 4, 2, 2) + conditional_word(3, 4, 0, 2) == F(1, 2)
        and conditional_word(3, 4, 1, 1) == F(3, 4),
        "biased finite extension",
    )
    # Shared hidden bit and two fresh visible bits. Each fine label is
    # uniform; comparing only the visible labels misses the common bit.
    visible = fine = 0
    for hidden, a, b in product((0, 1), repeat=3):
        visible += int(a == b)
        fine += int((a, hidden) == (b, hidden))
    need(
        F(visible, 8) == F(1, 2) and F(fine, 8) != F(1, 4),
        "coarse equality vs fine equality",
    )
    print(
        "Stationary pairwise-independent chronology: neighboring triple parity 1/3, spaced triple 0. Shuffled subsets and hidden labels are not the tested chronology."
    )


def ordered_blocks() -> None:
    """A chronologically sampled version does not need a de Finetti theorem.

    Partition a single joint record into k successive blocks of length L.
    Draw one index independently and uniformly in each block, regardless of
    outcomes. Conditional on the entire record, these selected labels have
    product law with the individual empirical block frequencies f_b. If
    each block has distinct-position mean collision c_b, its squared
    discrepancy from uniform has the same exact expectation as above.
    Thus TV(consecutive, uniform^k) <= TV(consecutive, selected)
    + k/2 sqrt((h-1)/L + h(1-1/L)(mean_b c_b-1/h)).
    Interpreting the comparison requires a common joint record or a proven
    nondisturbing discard operation, not suppressing a causal interaction.
    """
    # Enumerate every two-block binary record including nonexchangeable
    # records; verify conditional product and the quadratic bound, no fit.
    for record in product((0, 1), repeat=6):
        left, right = record[:3], record[3:]
        hist = Counter(product(left, right))
        delta = (
            sum((abs(F(hist[a, b], 9) - F(1, 4)) for a in (0, 1) for b in (0, 1)), F(0))
            / 2
        )
        spreads = []
        for block in (left, right):
            freqs = [F(block.count(i), 3) for i in (0, 1)]
            spread = sum(((p - F(1, 2)) ** 2 for p in freqs), F(0))
            c = F(sum(block[i] == block[j] for i, j in combinations(range(3), 2)), 3)
            need(spread == F(1, 6) + F(2, 3) * (c - F(1, 2)), "within-block collision")
            spreads.append(spread)
        need(delta**2 <= sum(spreads), "ordered-block estimate")
        for a, b in product((0, 1), repeat=2):
            need(hist[a, b] == left.count(a) * right.count(b), "conditional product")

    # Every sliding 4-window of the uniform-phase 0011 rotor is balanced.
    # Dilution over disjoint 4-blocks therefore manufactures iid fair
    # outcomes, even though 4 successive emissions are highly non-iid.
    cyclic = (0, 0, 1, 1) * 5
    consecutive = Counter(cyclic[j : j + 4] for j in range(4))
    diluted: Counter[tuple[int, ...]] = Counter()
    for j in range(4):
        for selected in product(range(4), repeat=4):
            diluted[tuple(cyclic[j + 4 * b + t] for b, t in enumerate(selected))] += 1
    need(len(diluted) == 16 and set(diluted.values()) == {64}, "dilution baseline")
    distance = (
        sum((abs(F(consecutive[w], 4) - F(diluted[w], 1024)) for w in diluted), F(0))
        / 2
    )
    need(distance == F(3, 4), "actual gap effect")
    print(
        "Ordered-block coupling holds on all 64 two-block fixtures. A gap test is essential: 0011 rotor looks iid after dilution but its consecutive four-click law differs in TV by 3/4."
    )


def main() -> None:
    finite_bits()
    fair_marginal_control()
    cases = 0
    for counts in product(range(5), repeat=3):
        if sum(counts) < 3:
            continue
        label_variance(counts)
        for k in (1, 2, 3):
            check_tv(counts, k)
        cases += 1
    stationary_control()
    ordered_blocks()
    print(
        f"Checked exact categorical collision identity and finite TV upper bound on {cases} three-label stocks. Arbitrarily long symmetric extensions with collision ≤1/h imply iid uniform visible labels."
    )


if __name__ == "__main__":
    main()
