"""Design-only, all-herald statistical witness for the two serial phase games.

The single forward classical channel carries at most d symbols at every cut.
The reader sees its final setting; no second path, clock or changing reference
can carry earlier settings. Condition on prior-trial history and trial-static
device/shared random tapes (including any future device coins if pre-sampled).
At each dial, conditional also on the setting prefix, its law must be uniform
or within its specified TV budget of uniform. The setting generator's private
fresh randomness is *not* given to the devices. Between trials, the devices
may remember everything. Herald and register trials before choosing settings;
label both ports in advance and record both bits, including zeros.

The parent probes prove the fair-setting upper bound C2 * Cd**(k-1) for
arbitrary serial kernels. Couple each successive setting to a fresh fair dial
while the prefixes agree: mismatch probability <= 1-product(1-delta_j).
Use the same device tapes in both games. Scores in [-1,1] can differ by at
most two, so the corrected bound below holds conditional on pretrial history.
Budgets must be justified uniformly for all device information and prefixes,
not averaged over a run. They and the stake must be fixed before each trial.

Given past history, E[R] <= U and 0 <= stake <= 1/(1+U). Thus 1+stake*(R-U)
is nonnegative with conditional expectation <= 1. Starting at 1, multiplying
these factors over EVERY herald yields a nonnegative supermartingale; under
the null, chance of ever crossing 1/alpha is <= alpha. One registered game,
port orientation and stake rule: picking the best game, sign or stake after
the fact is not covered. Predictable adaptation from *past* trials is fine.
Threshold noncrossing does not establish the null, or identify a carrier.

This program ingests no experimental data. Its balanced counts are design
arithmetic, not a random sample, a reported significance or a power forecast.
Run: python3 -B -m scripts.probe_serial_trial_witness
"""

from dataclasses import dataclass
from fractions import Fraction as F
from math import ceil, log, prod


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ValueError(why)


COS = tuple(F(x, 2) for x in (2, 1, -1, -2, -1, 1))


@dataclass(frozen=True)
class Design:
    d: int
    k: int
    upper: F
    stake: F


DESIGNS = (Design(4, 5, F(23, 50), F(1, 8)), Design(5, 8, F(97, 200), F(1, 20)))


def certify(design: Design) -> None:
    # In the companion partition probes: 6*C4=2+2 sqrt(3), 6*C5=4+sqrt(3).
    r, s = {4: (2, 2), 5: (4, 1)}[design.d]
    a, b, den = 2, 0, 3  # C2=2/3
    for _ in range(design.k - 1):
        a, b, den = r * a + 3 * s * b, s * a + r * b, 6 * den
    left = design.upper * den - a
    need(left > 0 and left * left > 3 * b * b, "rational U does not dominate bound")


def corrected(design: Design, deltas: tuple[F, ...]) -> F:
    need(len(deltas) == design.k, "one predictable TV bound required per dial")
    need(all(0 <= d <= 1 for d in deltas), "invalid TV bound")
    mismatch = 1 - prod((1 - d for d in deltas), start=F(1))
    return min(F(1), design.upper + 2 * mismatch)


def score(total: int, left: int, right: int) -> F:
    need(left in (0, 1) and right in (0, 1), "both port bits required")
    return (right - left) * COS[total % 6]


def factor(reward: F, upper: F, stake: F) -> F:
    need(-1 <= reward <= 1 and 0 <= upper <= 1, "invalid score or upper bound")
    need(0 <= stake <= 1 / (1 + upper), "unsafe stake")
    return 1 + stake * (reward - upper)


def leaked_sum(k: int) -> F:
    # Choose hidden SUM uniformly first. Choose the first k-1 dials privately
    # and uniformly; force the last to SUM-prefix mod 6. For each fixed prefix
    # and proposed last setting exactly one equally likely seed completes it.
    # Hence each observed WORD has probability 6**(-k), not merely fair marginals.
    # The receiver knows SUM at preparation; all interstation messages constant.
    for prefix in range(6):
        last_counts = [0] * 6
        for hidden in range(6):
            last_counts[(hidden - prefix) % 6] += 1
        need(last_counts == [1] * 6, "leak control disturbed observed word law")
    fair_prefix = F(1, 6 ** (k - 1))
    need(fair_prefix * F(1, 6) == F(1, 6**k), "not uniform over entire words")
    tv_last = sum(abs(int(i == 0) - F(1, 6)) for i in range(6)) / 2
    need(tv_last == F(5, 6), "last setting predictable conditional on seed/prefix")
    return (
        sum((score(h, int(c < 0), int(c > 0)) for h, c in enumerate(COS)), start=F(0))
        / 6
    )


def run(design: Design) -> None:
    certify(design)
    upper = corrected(design, (F(0),) * design.k)
    need(upper == design.upper, "fair-setting bound changed")
    need(factor(F(-1), upper, 1 / (1 + upper)) == 0, "stake endpoint")
    need(factor(upper, upper, design.stake) == 1, "null endpoint")
    for total in range(6):
        need(score(total, 0, 0) == score(total, 1, 1) == 0, "miss/double omitted")
        need(factor(F(0), upper, design.stake) < 1, "silent herald was skipped")

    # Model: E[Y|total]=eta * visibility * cos(total*pi/3). Silent heralds
    # contribute zero; eta is setting-independent. No normalization by
    # detected counts. E[cos^2]=1/2 for uniform settings.
    second = sum((c * c for c in COS), start=F(0)) / 6
    need(second == F(1, 2), "wrong ideal score")
    threshold = upper / second
    need(F(9, 10) * second < upper < second, "noisy six-symbol negative control")
    # A two-state match latch reports right only for the all-zero word.
    # If one illegally drops all silent trials, its apparent mean is 1.
    click_mass = F(1, 6**design.k)
    need(click_mass < upper < click_mass / click_mass, "postselection control")

    # Ideal all-herald row with no loss: P(right|t)=(1+cos(t*pi/3))/2.
    weights: dict[F, F] = {}
    for t, c in enumerate(COS):
        for right in (0, 1):
            y = 2 * right - 1
            val = score(t, 1 - right, right)
            weights[val] = weights.get(val, F(0)) + (1 + y * c) / 12
    weights = {v: w for v, w in weights.items() if w}
    need(
        weights == {F(1): F(1, 3), F(1, 2): F(1, 2), F(-1, 2): F(1, 6)}, "ideal weights"
    )
    need(sum(v * w for v, w in weights.items()) == second, "ideal score mismatch")
    block = prod(
        (factor(v, upper, design.stake) ** int(6 * w) for v, w in weights.items()),
        start=F(1),
    )
    need(block > 1, "no positive log growth at these ideal proportions")
    # Illustrative balanced counts only; fresh random trials will NOT remain
    # balanced block by block. Verify the rough logarithmic estimate exactly.
    nblocks = ceil(log(20) / log(float(block)))
    need(block ** (nblocks - 1) < 20 <= block**nblocks, "incorrect planning count")

    biased = corrected(design, (F(1, 1000),) * design.k)
    need((biased < second) == (design.d == 4), "unexpected budget sensitivity")
    need(
        corrected(design, (F(0),) * (design.k - 1) + (F(5, 6),)) == 1,
        "leak not guarded",
    )
    need(leaked_sum(design.k) == F(2, 3) > upper, "preloaded SUM control")
    print(
        f"d={design.d}, k={design.k}: fair U={upper}; mean advantage requires eta*V > "
        f"{threshold} in the specified model. TV 1/1000 per dial: U'={float(biased):.6f}."
    )
    print(
        f"  Fixed stake {design.stake}: balanced ideal counts first reach product 20 "
        f"at block {nblocks} ({6 * nblocks} hypothetical heralds, evaluated in blocks of six)."
    )
    print(f"  Loss latch: all-herald {click_mass}, clicks-only 1.")


def main() -> None:
    print(
        "Design self-checks only: no experimental trials, significance or power estimate."
    )
    for design in DESIGNS:
        run(design)
    print("Perfectly uniform observed words, one symbol and preloaded SUM: score 2/3.")
    print(
        "Inconclusive outcomes do not select a model; freshness/capacity require independent justification."
    )


if __name__ == "__main__":
    main()
