"""Exact readout limits for an unsigned stock with a subtracted background.

MODEL, NOT PHYSICS. Four observed colors have fixed total N=4B. Compare
dark H0=(B,B,B,B) with bright H1=(B+a,B-a,B,B), integer 0<=a<=B. A detector
uniformly samples k actual marks, without replacement unless stated, and
sees ONLY their ordered colors. One hypothesis-blind randomized policy
r(word) in [0,1] decides whether to click. Its auxiliary randomness must
not reveal the preparation. Absolute identities, pair labels, active tags,
stock queries, and a condition-dependent policy are outside this model.
Uniform sampling and this classical probability law are supplied, not derived.

If k<=B, every color word has positive H0 probability. Nonnegativity then
makes dark rate zero imply bright rate zero. For a word with r plus and s
minus colors, its likelihood ratio is
    (B+a)_r/(B)_r * (B-a)_s/(B)_s <= (B+a)_k/(B)_k = L.
Here (n)_j is the falling factorial. The minus factor is at most one, and
each additional plus factor exceeds one. Thus bright<=L*dark for EVERY
such policy. The all-plus word attains L. Scaling its click probability
attains dark=bright/L only up to P1(all-plus), not at every requested bright
rate. The finite exact Neyman-Pearson envelope below handles all rates.
Fill the highest likelihood ratios first: transferring a fixed amount of
bright probability from a lower ratio to a higher one cannot increase dark
cost. At most one boundary count class needs a fractional click probability.
Order does not improve this envelope: words with the same color counts
have the same ratio, so a policy can be averaged within each count class.
With replacement, L=(1+a/B)^k and full dark support holds for every finite k.

At k=B+1, all-plus has zero dark probability and bright probability
    a(a+1)...(a+B)/(4B)_(B+1).
For positive a, it is the ONLY dark-null word with positive H1 probability.
Consequently every exactly dark color-only policy at this budget has that
same positive-a shape up to one constant, if that SAME policy is used for
every a. For B>=3 its values at a=1,2 have ratio B+2, not the fixed-scale
quadratic ratio 4. This is not a no-go for all normalized quantum readouts.
Do not overstate: B=2 coincides
with a squared law on the entire allowed nonnegative integer grid {0,1,2};
B=1 is trivial. Symmetrizing all-plus/all-minus gives the same small-grid
coincidence for signed a. Larger budgets or other observation alphabets
are not covered by this nonquadratic statement.

A stopping policy with a HARD bound k can be padded with ignored samples,
so the same bound applies. A bound on MEAN samples alone is different:
rarely taking B+1 samples, otherwise taking none, gives positive bright
rate and exact darkness at arbitrarily small positive mean cost. Its bright
rate also shrinks. This is not a useful-rate or fixed-budget counterexample.

Postselection must retain acceptance rates s0,s1: for conditional click
rates q0,q1, q1*s1<=L*q0*s0. Ignoring unequal acceptance can falsely reject
the model. A conditional rate with zero accepted trials is undefined, not
zero. Optional input intervals must cover the relevant probabilities
SIMULTANEOUSLY. No confidence level, independence across trials, data fit,
or confidence intervals are manufactured here. Exact-region compatibility
is reported as inconclusive, never as physical validation.
Zero OBSERVED dark clicks in finitely many trials is not a zero underlying
dark rate; a supplied simultaneous upper interval must reflect that fact.

RESOURCE CAVEAT. If an UNREDUCED denominator-2^t integer representation
must cover the whole signed unit range, n=B+2^t*x requires B>=2^t and
N>=4*2^t. This is a conditional representation cost, not a theorem that
every t-mixer word needs that stock: cancellation, restricted states, or
another encoding may avoid it. At fixed raw deviation a and fixed k,
L tends to one as B grows. At fixed physical amplitude a/2^t and B=2^t,
a grows too, so that contrast does NOT vanish. We do not reimplement the
native rotation, complement-pair matching, or its integer denominator cost.

Hidden active labels give a deliberate escape control: all dark marks may
be tagged inactive while some bright marks are active, with unchanged color
marginals. A one-mark active-tag readout can then be exactly dark. Such a
relation or deterministic neutralization rule is additional structure, not
a consequence of subtracting B from a marginal count.

The arguments above are not Lean proofs or a Born/readout-origin claim.
Run: python3 -B -O -m scripts.probe_unsigned_background_readout
Rate diagnostic: --dark 0:1/10 --bright 1/4:3/10
Conditional diagnostic: add --conditional --dark-retention lo:hi
                        --bright-retention lo:hi
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import factorial, prod
from typing import Literal

Counts = tuple[int, int, int, int]
Word = tuple[int, ...]


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError(reason)


def falling(n: int, k: int) -> int:
    need(n >= 0 and k >= 0, "nonnegative falling-factorial arguments required")
    return prod(range(n - k + 1, n + 1)) if k <= n else 0


def count_vectors(k: int) -> tuple[Counts, ...]:
    return tuple(
        (a, b, c, k - a - b - c)
        for a in range(k + 1)
        for b in range(k - a + 1)
        for c in range(k - a - b + 1)
    )


def stocks(background: int, amplitude: int) -> Counts:
    need(background >= 1 and abs(amplitude) <= background, "invalid unsigned stocks")
    return background + amplitude, background - amplitude, background, background


def word_probability(stock: Counts, word: Word, replacement: bool = False) -> F:
    need(all(0 <= color < 4 for color in word), "invalid color")
    total = sum(stock)
    need(replacement or len(word) <= total, "sample budget exceeds population")
    remaining = list(stock)
    value = F(1)
    for step, color in enumerate(word):
        if not remaining[color]:
            return F(0)
        value *= F(remaining[color], total if replacement else total - step)
        if not replacement:
            remaining[color] -= 1
    return value


def count_probability(stock: Counts, counts: Counts, replacement: bool) -> F:
    k, total = sum(counts), sum(stock)
    multiplicity = factorial(k) // prod(factorial(c) for c in counts)
    numerator = prod(
        n**c if replacement else falling(n, c)
        for n, c in zip(stock, counts, strict=True)
    )
    denominator = total**k if replacement else falling(total, k)
    return F(multiplicity * numerator, denominator)


@dataclass(frozen=True)
class Atom:
    counts: Counts
    dark: F
    bright: F


def atoms(
    background: int, amplitude: int, k: int, replacement: bool = False
) -> tuple[Atom, ...]:
    need(0 <= amplitude <= background and background >= 1, "require 0<=a<=B and B>=1")
    need(k >= 0 and (replacement or k <= 4 * background), "invalid sample budget")
    dark, bright = stocks(background, 0), stocks(background, amplitude)
    rows = tuple(
        Atom(
            counts,
            count_probability(dark, counts, replacement),
            count_probability(bright, counts, replacement),
        )
        for counts in count_vectors(k)
    )
    rows = tuple(row for row in rows if row.dark or row.bright)
    need(sum((row.dark for row in rows), F(0)) == 1, "dark normalization")
    need(sum((row.bright for row in rows), F(0)) == 1, "bright normalization")
    return rows


def likelihood_bound(
    background: int, amplitude: int, k: int, replacement: bool = False
) -> F | None:
    stocks(background, amplitude)
    need(amplitude >= 0 and k >= 0, "nonnegative amplitude and budget required")
    need(replacement or k <= 4 * background, "sample budget exceeds population")
    if amplitude == 0:
        return F(1)
    if replacement:
        return F(background + amplitude, background) ** k
    if k > background:
        return None  # A bright-positive, dark-null event exists.
    return F(falling(background + amplitude, k), falling(background, k))


def likelihood_key(row: Atom) -> tuple[bool, F]:
    return row.dark == 0, row.bright / row.dark if row.dark else F(0)


def minimum_dark(rows: tuple[Atom, ...], bright_target: F) -> F:
    """Sharp minimum dark rate at one EXACT bright rate, allowing randomization."""
    need(0 <= bright_target <= 1, "invalid bright target")
    left, dark = bright_target, F(0)
    for row in sorted(rows, key=likelihood_key, reverse=True):
        if not left:
            return dark
        if not row.bright:
            continue
        fraction = min(F(1), left / row.bright)
        dark += fraction * row.dark
        left -= fraction * row.bright
    need(left == 0, "unfilled bright target")
    return dark


def maximum_dark(rows: tuple[Atom, ...], bright_target: F) -> F:
    return 1 - minimum_dark(rows, 1 - bright_target)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self) -> None:
        need(0 <= self.lo <= self.hi <= 1, "probability interval outside [0,1]")


@dataclass(frozen=True)
class Diagnostic:
    status: Literal["excluded", "inconclusive"]
    minimum_dark: F | None
    maximum_dark: F | None
    reason: str


def diagnose(
    rows: tuple[Atom, ...], dark: Interval | None, bright: Interval | None
) -> Diagnostic:
    """Intersect a rate rectangle with the convex region of all color policies.

    Its projection over bright in [lo,hi] is exactly
    [minimum_dark(lo), maximum_dark(hi)]. For retention-derived outer
    intervals, intersection need not certify the original conditional data.
    """
    if dark is None or bright is None:
        return Diagnostic(
            "inconclusive", None, None, "Both simultaneous rate intervals are required."
        )
    lower = minimum_dark(rows, bright.lo)
    upper = maximum_dark(rows, bright.hi)
    if lower > dark.hi:
        return Diagnostic(
            "excluded",
            lower,
            upper,
            "Bright lower bound forces more dark clicks than allowed.",
        )
    if upper < dark.lo:
        return Diagnostic(
            "excluded",
            lower,
            upper,
            "Dark lower bound forces more bright clicks than allowed.",
        )
    return Diagnostic(
        "inconclusive",
        lower,
        upper,
        "Rate rectangle intersects the exact color-policy region; this does not validate the apparatus.",
    )


def unconditional_envelope(
    conditional: Interval | None, retention: Interval | None
) -> Interval | None:
    if retention is not None and retention.hi == 0:
        return Interval(F(0), F(0))
    if conditional is None or retention is None:
        return None
    return Interval(conditional.lo * retention.lo, conditional.hi * retention.hi)


def conditional_rate(click: F, retained: F) -> F | None:
    need(0 <= click <= retained <= 1, "invalid click/retention pair")
    return click / retained if retained else None


def all_plus(background: int, amplitude: int, k: int, replacement: bool = False) -> F:
    return word_probability(stocks(background, amplitude), (0,) * k, replacement)


def enumerate_controls() -> int:
    cases = 0
    for background in range(1, 5):
        for amplitude in range(background + 1):
            for replacement in (False, True):
                for k in range(5 if replacement else background + 1):
                    rows = atoms(background, amplitude, k, replacement)
                    bound = likelihood_bound(background, amplitude, k, replacement)
                    need(bound is not None, "missing finite likelihood bound")
                    if bound is None:
                        raise ArithmeticError("unreachable")
                    need(all(row.dark > 0 for row in rows), "missing dark support")
                    need(
                        max(row.bright / row.dark for row in rows) == bound,
                        "likelihood maximum",
                    )
                    d = all_plus(background, 0, k, replacement)
                    b = all_plus(background, amplitude, k, replacement)
                    need(b == bound * d, "all-plus ratio is not sharp")
                    for coin in (F(0), F(1, 3), F(1)):
                        need(
                            minimum_dark(rows, coin * b) == coin * d,
                            "sharp low-rate segment",
                        )
                    by_count: dict[Counts, tuple[F, F]] = {}
                    policy_dark, policy_bright = F(0), F(0)
                    for word in product(range(4), repeat=k):
                        counts: Counts = (
                            word.count(0),
                            word.count(1),
                            word.count(2),
                            word.count(3),
                        )
                        p0 = word_probability(stocks(background, 0), word, replacement)
                        p1 = word_probability(
                            stocks(background, amplitude), word, replacement
                        )
                        need(p0 > 0 and p1 <= bound * p0, "ordered-word likelihood")
                        old0, old1 = by_count.get(counts, (F(0), F(0)))
                        by_count[counts] = old0 + p0, old1 + p1
                        click = F(
                            sum((j + 1) * (c + 1) for j, c in enumerate(word)) % 8, 7
                        )
                        policy_dark += click * p0
                        policy_bright += click * p1
                    need(
                        policy_bright <= bound * policy_dark,
                        "randomized ordered policy",
                    )
                    for row in rows:
                        need(
                            by_count[row.counts] == (row.dark, row.bright),
                            "count/word agreement",
                        )
                    cases += 1
    return cases


def roc_controls() -> None:
    # Independent exhaustive policy vertices for a one-draw experiment.
    rows = atoms(3, 2, 1)
    vertices = tuple(
        (
            sum((F(bit) * row.dark for bit, row in zip(bits, rows, strict=True)), F(0)),
            sum(
                (F(bit) * row.bright for bit, row in zip(bits, rows, strict=True)), F(0)
            ),
        )
        for bits in product((0, 1), repeat=len(rows))
    )
    for j in range(17):
        target = F(j, 16)
        candidates = [dark for dark, bright in vertices if bright == target]
        for (d0, b0), (d1, b1) in product(vertices, repeat=2):
            if b0 <= target <= b1 and b0 < b1:
                weight = (target - b0) / (b1 - b0)
                candidates.append((1 - weight) * d0 + weight * d1)
        need(
            minimum_dark(rows, target) == min(candidates),
            "lower ROC convex-hull control",
        )
        need(
            maximum_dark(rows, target) == max(candidates),
            "upper ROC convex-hull control",
        )
    rows = atoms(8, 2, 3)
    bound = likelihood_bound(8, 2, 3)
    need(bound == F(15, 7), "example likelihood")
    need(likelihood_bound(8, 2, 3, True) == F(125, 64), "replacement likelihood")
    target = F(1, 4)
    linear_dark = F(7, 60)
    need(
        minimum_dark(rows, target) > linear_dark,
        "linear bound was overclaimed as globally sharp",
    )
    need(
        diagnose(
            rows, Interval(linear_dark, linear_dark), Interval(target, target)
        ).status
        == "excluded",
        "ROC-only exclusion",
    )
    need(
        diagnose(rows, Interval(F(0), F(1, 10)), Interval(F(1, 4), F(3, 10))).status
        == "excluded",
        "rate exclusion",
    )
    need(
        diagnose(rows, None, Interval(F(1, 4), F(3, 10))).status == "inconclusive",
        "missing data status",
    )
    d, b = all_plus(8, 0, 3), all_plus(8, 2, 3)
    need(
        diagnose(rows, Interval(d, d), Interval(b, b)).status == "inconclusive",
        "attainable rates rejected",
    )
    # Reverse-side exclusion: same distributions cannot have unequal rates.
    same = atoms(3, 0, 2)
    need(
        diagnose(same, Interval(F(3, 4), F(1)), Interval(F(0), F(1, 4))).status
        == "excluded",
        "reverse exclusion",
    )


def boundary_controls() -> None:
    for background in range(1, 7):
        k = background + 1
        for amplitude in range(1, background + 1):
            rows = atoms(background, amplitude, k)
            dark_null = tuple(row for row in rows if row.dark == 0 and row.bright > 0)
            need(
                len(dark_null) == 1 and dark_null[0].counts == (k, 0, 0, 0),
                "first support escape",
            )
            p = all_plus(background, amplitude, k)
            rising = prod(range(amplitude, amplitude + background + 1))
            need(p == F(rising, falling(4 * background, k)), "all-plus amplitude law")
            need(minimum_dark(rows, p) == 0, "exact darkness at support boundary")
        if background >= 2:
            p1, p2 = all_plus(background, 1, k), all_plus(background, 2, k)
            need(p2 / p1 == background + 2, "nonquadratic ratio")
            need((p2 == 4 * p1) == (background == 2), "small-grid exception")
    for amplitude in range(-2, 3):
        p = word_probability(stocks(2, amplitude), (0,) * 3) + word_probability(
            stocks(2, amplitude), (1,) * 3
        )
        need(p == F(amplitude * amplitude, 56), "signed B=2 accidental quadratic")
    # A mean-cost cap cannot replace a hard sampling cap.
    background, amplitude = 4, 1
    trial_coin = F(1, (background + 1) ** 2)
    mean_cost = trial_coin * (background + 1)
    bright = trial_coin * all_plus(background, amplitude, background + 1)
    dark = trial_coin * all_plus(background, 0, background + 1)
    need(mean_cost < 1 and dark == 0 and bright > 0, "rare over-budget escape")
    # Deliberately broaden observation to a hidden active flag: not a color policy.
    # Each pair lists (inactive, active); no matching or neutralization
    # mechanism is inferred or implemented by this countercontrol.
    tagged_dark = ((background, 0),) * 4
    tagged_bright = (
        (background - amplitude, 2 * amplitude),
        (background - amplitude, 0),
        (background, 0),
        (background, 0),
    )
    need(tuple(map(sum, tagged_dark)) == stocks(background, 0), "dark color marginals")
    need(
        tuple(map(sum, tagged_bright)) == stocks(background, amplitude),
        "bright color marginals",
    )
    hidden_dark = F(sum(active for _, active in tagged_dark), 4 * background)
    hidden_bright = F(sum(active for _, active in tagged_bright), 4 * background)
    need(hidden_bright > 0 and hidden_dark == 0, "active-label escape")
    need(
        all(row.dark > 0 for row in atoms(background, amplitude, 1)),
        "hidden flag changed only marginals",
    )


def selection_controls() -> None:
    # On plus, click AND retain with probability 1/4; on minus retain without
    # clicking; otherwise abstain. All choices are preparation-blind.
    dark_click, bright_click = F(1, 16), F(5, 64)
    dark_keep, bright_keep = F(5, 16), F(17, 64)
    q0, q1 = (
        conditional_rate(dark_click, dark_keep),
        conditional_rate(bright_click, bright_keep),
    )
    need(q0 is not None and q1 is not None, "positive retention")
    if q0 is None or q1 is None:
        raise ArithmeticError("unreachable")
    bound = F(5, 4)
    need(q1 > bound * q0, "conditional-rate false exclusion control")
    need(q1 * bright_keep == bound * q0 * dark_keep, "retention-corrected sharp bound")
    d = unconditional_envelope(Interval(q0, q0), Interval(dark_keep, dark_keep))
    b = unconditional_envelope(Interval(q1, q1), Interval(bright_keep, bright_keep))
    need(
        d == Interval(dark_click, dark_click)
        and b == Interval(bright_click, bright_click),
        "retention envelope",
    )
    need(
        diagnose(atoms(8, 2, 1), d, b).status == "inconclusive",
        "valid retained policy rejected",
    )
    need(
        conditional_rate(F(0), F(0)) is None,
        "undefined conditional rate was set to zero",
    )
    need(
        unconditional_envelope(None, Interval(F(0), F(0))) == Interval(F(0), F(0)),
        "known zero retention",
    )
    need(
        unconditional_envelope(Interval(F(0), F(1)), None) is None,
        "missing retention silently supplied",
    )


def scaling_controls() -> None:
    previous_fixed = F(100)
    fixed_contrast = F(125, 64)
    for t in range(2, 13):
        denominator = 2**t
        background = denominator
        need(
            background - denominator == 0 and background - 1 - denominator < 0,
            "full-range stock requirement",
        )
        raw = likelihood_bound(background, 1, 3)
        need(raw is not None, "scaling likelihood")
        if raw is None:
            raise ArithmeticError("unreachable")
        need(1 < raw < previous_fixed, "fixed raw deviation contrast did not decrease")
        previous_fixed = raw
        physical_amplitude = denominator // 4
        need(
            F(physical_amplitude, denominator) == F(1, 4), "physical amplitude changed"
        )
        need(
            likelihood_bound(background, physical_amplitude, 3, True) == fixed_contrast,
            "fixed physical contrast collapsed",
        )
        finite = likelihood_bound(background, physical_amplitude, 3)
        need(finite is not None and finite >= fixed_contrast, "replacement comparison")


def parse_interval(value: str) -> Interval:
    try:
        low, high = value.split(":")
        return Interval(F(low), F(high))
    except (ValueError, ZeroDivisionError) as error:
        raise argparse.ArgumentTypeError(
            "use rational lo:hi with 0<=lo<=hi<=1"
        ) from error


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--background", type=int, default=8)
    parser.add_argument("--amplitude", type=int, default=2)
    parser.add_argument("--samples", type=int, choices=range(17), default=3)
    parser.add_argument("--replacement", action="store_true")
    parser.add_argument("--dark", type=parse_interval)
    parser.add_argument("--bright", type=parse_interval)
    parser.add_argument("--conditional", action="store_true")
    parser.add_argument("--dark-retention", type=parse_interval)
    parser.add_argument("--bright-retention", type=parse_interval)
    args = parser.parse_args()
    cases = enumerate_controls()
    roc_controls()
    boundary_controls()
    selection_controls()
    scaling_controls()
    try:
        rows = atoms(args.background, args.amplitude, args.samples, args.replacement)
        bound = likelihood_bound(
            args.background, args.amplitude, args.samples, args.replacement
        )
    except ValueError as error:
        parser.error(str(error))
    dark, bright = args.dark, args.bright
    if args.conditional:
        dark = unconditional_envelope(dark, args.dark_retention)
        bright = unconditional_envelope(bright, args.bright_retention)
    elif args.dark_retention is not None or args.bright_retention is not None:
        parser.error("retention intervals require --conditional")
    diagnostic = diagnose(rows, dark, bright)
    print(
        f"Exact bounded regressions: {cases} likelihood cases, ROC, support boundary, selection and scaling controls."
    )
    print(
        f"B={args.background}, a={args.amplitude}, k={args.samples}, replacement={args.replacement}."
    )
    print(
        f"Likelihood maximum: {bound if bound is not None else 'unbounded (dark-null bright event)'}."
    )
    print(f"Sharp minimum dark rate at bright=1/4: {minimum_dark(rows, F(1, 4))}.")
    print(
        f"Supplied simultaneous-rate diagnostic: {diagnostic.status}; {diagnostic.reason}"
    )
    print(
        "Without replacement, k=B+1 allows exact darkness; nonquadratic for B>=3, with B=1,2 grid exceptions."
    )
    print(
        "Hidden labels/neutralization, average-only budgets, and unrecorded selection are outside the fixed color-only claim."
    )
    print(
        "No observed data, fitted detector, probability-origin derivation, or physical darkness claim."
    )


if __name__ == "__main__":
    main()
