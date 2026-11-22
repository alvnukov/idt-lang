"""Prospective all-herald test of a specific real, independently turned source.

Before the run, fix N, alpha, budgets, comparator click rail, response window,
and scoring rule. Register a herald *before* drawing anything. For every
herald draw orth with probability 1/3 (else same); independently draw one of
the eight first rays (each equatorial 1/9, each pole 1/6). Port B gets its
antipode for orth or itself for same. Independently turn the reference at
each port by a fresh uniform cyclic trit. The two ray labels are intentionally
related; the reference turns and product preparations conditional on the ray
labels are independent. Neither orth/same nor any label, turn, random seed,
extra copy, shared phase, timing, herald flag selected by treatment, or other
side channel goes to the co-located comparator. Hide keys until outputs lock.

Record one bit for EVERY registered trial: any designated click in the fixed
window is 1 (also if another rail fires), otherwise 0. No conditional
reference-branch denominator or removal of failed preparations/losses. A lost
log is not a known zero: an incomplete record cannot yield this test result.
Winning means orth-click or same-no-click. Never rebalance, peek/stop early,
or choose a rail, threshold, or study from the observed wins.

The nominal null is one normalized real triangle-plus-reference package per
port, the specified preparation law, and any common binary positive effect
0 <= E <= I. The finite dual in probe_triangle_reference_sewing bounds
p_orth - 2*p_same <= 1/4. This is not a bound on all real theories. If the
bound holds conditional on each history (e.g. the device changes its common
effect between shots but receives fresh sources independent of its memory),
each win probability is <= U. Coupling each conditional Bernoulli outcome
with a uniform draw gives pathwise domination by independent Bernoulli(U)
wins; thus the fixed-N upper binomial tail is a valid size bound even then.
The power calculation, in contrast, assumes iid shots of the stated target.

An eligible future stream must independently justify that the assigned
ensembles, rotation independence, one-copy capacity, source/device isolation,
herald completeness and error/leakage bounds implement that comparison.
A reference label in software, tomography of just one port, a selected
coincidence table or ideal design arithmetic cannot establish eligibility.
If a calibration budget is itself a confidence bound, account for its failure
probability in the overall error guarantee (or report conditional size only).
A rejection challenges the specified joint assumptions, not all real models;
it would not identify the alternative or derive a physical composition law.
No physical comparator or dataset is identified or measured by this script.
Run: python3 -B -m scripts.probe_reference_sewing_trials
"""

from fractions import Fraction as F
from itertools import product
from math import comb

from scripts.probe_triangle_reference_sewing import (
    D, K, LABELS, dot, need, norm, optimality, preparations,
)

N, ALPHA = 317, F(1, 100)


def win(orth: bool, click: bool) -> bool:
    return orth == click


def mean(p_orth: F, p_same: F) -> F:
    return (2 + p_orth - 2 * p_same) / 3


def budget_cap(d_orth: F, d_same: F, compromise: F) -> F:
    """On clean trials bound joint ensemble trace distances (half trace norm),
    separately by class, to the nominal two-port ensembles. The clean class
    prior is still exact; the common effect cannot see the source seed.
    Classwise click discrepancies are then <= d_c. On a compromised trial
    grant a full win. Require a clean/adversarial mixture conditional on EVERY
    history, with adversarial probability <= compromise; an aggregate bad-shot
    estimate or an unbudgeted class leak does not justify this correction.
    These are independently established uniform bounds, not fitted estimates.
    """
    need(all(0 <= x <= 1 for x in (d_orth, d_same, compromise)), "invalid budget")
    clean = min(F(1), F(3, 4) + (d_orth + 2 * d_same) / 3)
    return (1 - compromise) * clean + compromise


def mass(n: int, k: int, a: int, b: int) -> int:
    return comb(n, k) * a**k * (b-a)**(n-k)


def tail(n: int, k: int, p: F) -> F:
    a, b = p.as_integer_ratio()
    return F(sum(mass(n, j, a, b) for j in range(k, n + 1)), b**n)


def critical(n: int, p: F, alpha: F) -> int:
    """Smallest rejecting win count; n+1 denotes impossible rejection."""
    a, b = p.as_integer_ratio()
    acc = 0
    for k in reversed(range(n + 1)):
        acc += mass(n, k, a, b)
        if acc * alpha.denominator > alpha.numerator * b**n:
            return k + 1
    raise ValueError("alpha must be less than one")


def source_controls() -> None:
    src = preparations()
    # On pole-only inputs the two bit-labeled rotated ray spans are
    # orthogonal. Project each port onto those two subspaces, click on unequal
    # bits. This is a class-blind effect, with no extra copy or classical key.
    need(all(dot(src[K, 0, u], src[K, 1, v]) == 0 for u, v in product(D, repeat=2)),
         "pole-only supports not orthogonal")
    need(mean(F(1), F(0)) == 1, "counterfeit reduced-support comparator")
    # Even correct marginal ray and rotation distributions are not enough:
    # with synchronized turns, ordinary whole-package antiswap has target
    # statistics. Compute its click law on all label/turn/class settings.
    click_rates = [F(0), F(0)]
    weights = [F(0), F(0)]
    for k, b in LABELS:
        w = F(1, 6) if k == K else F(1, 9)
        for u, orth in product(D, (0, 1)):
            x, y = src[k, b, u], src[k, b ^ orth, u]
            click = (1 - F(dot(x, y)**2, norm(x)*norm(y))) / 2
            weights[orth] += w / 3
            click_rates[orth] += w * click / 3
    need(weights == [1, 1] and click_rates == [0, F(1, 2)], "shared-turn control")
    need(all(win(c, c) for c in (False, True)), "leaked class key should win perfectly")


def main() -> None:
    need(optimality() == [2, 6, 2, 6], "parent finite dual changed")
    source_controls()
    need([win(c, y) for c, y in product((False, True), repeat=2)]
         == [True, False, False, True], "binary scoring")
    null = budget_cap(F(0), F(0), F(0))
    target = mean(F(1, 2), F(0))
    need(null == mean(F(1, 4), F(0)) == F(3, 4) and target == F(5, 6), "nominal means")
    # Independent class-common erasure of true clicks; no added false clicks.
    # p_same=0 and p_orth=eta/2: strict mean advantage iff eta>1/2 at U=3/4.
    need(mean(F(1, 4), F(0)) == null < mean(F(501, 2000), F(0)), "efficiency edge")
    k = critical(N, null, ALPHA)
    size, near, power = tail(N, k, null), tail(N, k-1, null), tail(N, k, target)
    need(k == 256 and size <= ALPHA < near and power >= F(9, 10), "fixed plan")
    # Design controls at adjacent win counts: never actual trial data.
    need(critical(N, F(1), ALPHA) == N + 1, "unrestricted leakage permits no rejection")
    corrected = budget_cap(F(1, 100), F(1, 100), F(1, 100))
    k2 = critical(N, corrected, ALPHA)
    need(corrected == F(953, 1250) and k2 > k, "sensitivity control")
    print("Prospective design only; no observed trials, p-value, or empirical comparator.")
    print(f"Fixed {N} all-herald shots; alpha={ALPHA}; nominal null win <= {null}; "
          f"iid ideal win={target}. Reject only at >= {k} wins.")
    print(f"Null tail at {k}: {float(size):.9f}; at {k-1}: {float(near):.9f} "
          f"(does not reject); ideal iid power {float(power):.9f}.")
    print("Under pure common click erasure, strict nominal mean advantage iff eta > 1/2.")
    print(f"Separate prospective design: classwise trace errors 1/100 and compromised "
          f"probability <= 1/100 give cap {corrected}, cutoff {k2}, "
          f"worst-case binomial tail approximately {float(tail(N, k2, corrected)):.9f}, "
          f"power at unchanged iid ideal {float(tail(N, k2, target)):.9f}.")
    print("Controls: poles only or disclosed class can win 1; synchronized turns + "
          "whole antiswap win 5/6. Nonrejection is inconclusive.")


if __name__ == "__main__":
    main()
