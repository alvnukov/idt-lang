"""Retrospective extension of the frozen pump-index HBT check to signed lags 1..9.

The 1.5 ns half-window, 76.2 MHz pump, file and bin coordinates are unchanged
from probe_pump_locked_hbt. Neither the new lags nor the comparison below are
blind or preregistered. Source: Münzberg et al., Fig. 2(d), 10.1063/5.0091867;
numerical data: 10.5281/zenodo.6337697. No extraction of individual trials.

Two different clean nulls predict different absent/suppressed structures:

* A fixed exclusive arm assignment repeated every d pump pulses has zero
  unlike-arm pairs at lag d. Censoring genuine outputs cannot add them.
* Let I_j be a stationary scalar intensity and f,g fixed nondecreasing click
  probabilities. Require E[A_j B_m | intensity history] = f(I_j)g(I_m) at
  m=j AND m=j+k. Shifted intensities need not be independent or positively
  correlated. The same-draw threshold sets {f(I)>u} and {g(I)>v} are nested;
  their joint probability attains the smaller marginal. No shifted coupling
  with these marginals can exceed it. Integrate u,v over [0,1] to obtain
  E[f(I_j)g(I_j)] >= E[f(I_j)g(I_{j+k})] for every k. Thus the population
  center-to-mean-side ratio is >=1 when its denominator is positive.

This second statement needs comparable pair exposure, pulse IDs, elementary
pair recording, and equivalent area capture in the acquisition windows to
compare with EXPECTED histogram counts. Unknown detector history, gradients
in efficiency, dead time and timing/gating artifacts need independent bounds.
It is neither a deterministic inequality on observed noisy counts nor a test
of all classical models. Subtracting background or fitting peaks is not done.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from pathlib import Path

if __package__:
    from . import probe_pump_locked_hbt as frozen
else:
    import probe_pump_locked_hbt as frozen


SIGNED = tuple(range(-9, 10))
WIDTH_PS = 1500


def binary_de_bruijn_ten() -> tuple[int, ...]:
    """Euler tour of the shift graph: each ten-bit edge is used exactly once."""
    mask = (1 << 9) - 1
    unused = [2] * (mask + 1)
    path = [0]
    reverse = []
    while path:
        v = path[-1]
        if unused[v]:
            unused[v] -= 1
            path.append(((v << 1) | unused[v]) & mask)
        else:
            reverse.append(path.pop())
    return tuple(v & 1 for v in reversed(reverse[:-1]))


def ordered_pairs(word: tuple[int, ...], lag: int) -> Counter:
    return Counter((a, word[(i + lag) % len(word)]) for i, a in enumerate(word))


def clock_controls() -> dict:
    seven = tuple(frozen.controls()["period_seven_word"])
    frozen.require(seven == (1, 1, 1, 0, 1, 0, 0), "frozen seven-state candidate changed")
    seven_ab = {k: ordered_pairs(seven, k)[0, 1] for k in SIGNED}
    frozen.require([k for k in SIGNED if seven_ab[k] == 0] == [-7, 0, 7],
                   "frozen candidate must forbid lag seven, not only lag zero")

    tested = 0
    for d in range(1, 10):
        for word in product((0, 1), repeat=d):
            frozen.require(ordered_pairs(word, d)[0, 1] == ordered_pairs(word, -d)[1, 0] == 0,
                           "period-d output must return to its arm")
            tested += 1
    word = binary_de_bruijn_ten()
    wrapped = word + word[:9]
    frozen.require(len(word) == 1024 and sum(word) == 512 and
                   len({wrapped[i:i + 10] for i in range(1024)}) == 1024,
                   "ten-bit windows must be complete and unique on the circle")
    pairs = {k: ordered_pairs(word, k) for k in SIGNED}
    frozen.require(all(table == Counter({(0, 0): 512, (1, 1): 512}) if k == 0 else
                       all(table[a, b] == 256 for a, b in product((0, 1), repeat=2))
                       for k, table in pairs.items()), "balanced pair-frequency countercontrol")
    frozen.require(ordered_pairs(word, len(word))[0, 1] == 0, "deterministic repeat")
    return {"short_period_words_checked": tested, "frozen_seven_AB_by_lag": seven_ab,
            "balanced_longer_word_period": len(word), "distinct_ten_bit_windows": 1024,
            "longer_AB_by_lag": {k: table[0, 1] for k, table in pairs.items()},
            "longer_AB_at_lag1024": 0}


def dot_lag(a: tuple[int, ...], b: tuple[int, ...], k: int) -> int:
    return sum(x * b[(j + k) % len(b)] for j, x in enumerate(a))


def intensity_controls() -> dict:
    # Periodic scalar histories with uniformly sampled phase are stationary;
    # integer response levels are twice the conditional click probabilities.
    shapes = tuple(combinations_with_replacement(range(3), 3))
    compared = 0
    strict = 0
    for length in range(2, 6):
        for seq in product(range(3), repeat=length):
            profiles = [tuple(response[i] for i in seq) for response in shapes]
            for a, b in product(profiles, repeat=2):
                center = dot_lag(a, b, 0)
                for k in range(1, length):
                    side = dot_lag(a, b, k)
                    frozen.require(center >= side, "stationary monotone intensity peak bound")
                    compared += 1
                    strict += int(center > side)

    x = (0, 1, 0, 1)
    opposite = tuple(1 - v for v in x)
    # Opposite local response, or two complementary efficiency shutters with
    # constant incident light, can produce this pattern. Neither realizes
    # stationary scalar illumination with two static increasing responses.
    opposite_peaks = [dot_lag(x, opposite, k) for k in (0, 1)]
    # Both arms truly respond identically, but one pulse of reporting offset
    # all by itself creates a measured dip; no negative response is needed.
    delay_peaks = [dot_lag(x, x, k - 1) for k in (0, 1)]
    frozen.require(opposite_peaks == delay_peaks == [0, 2], "reversed-response/timing controls")
    # Constant scalar, unbiased iid hidden routing to exactly one arm. Local
    # marginals 1/2 would give 1/4 at zero if they factored; exclusivity gives 0.
    arm_assignments = tuple(product((0, 1), repeat=2))
    hidden = [sum(int(first == 0 and (first if k == 0 else second) == 1)
                  for first, second in arm_assignments) for k in (0, 1)]
    frozen.require(hidden == [0, 1], "conditional dependence at a single pulse")
    return {"cyclic_comparisons": compared, "strict": strict, "equal": compared - strict,
            "response_grid": "each of f,g is a nondecreasing map {0,1,2} -> {0,1/2,1}",
            "opposite_response_or_complementary_shutters_center_side": opposite_peaks,
            "pulse_misregistration_center_side": delay_peaks,
            "exclusive_hidden_arm_center_side_out_of_four": hidden}


def analyze(data: bytes) -> dict:
    histogram, actual_sha = frozen.read_histogram(data)
    counts = {k: frozen.count_window(histogram, k, WIDTH_PS) for k in SIGNED}
    side = sum(n for k, n in counts.items() if k != 0)
    ratio = Fraction(18 * counts[0], side)
    return {"source_sha256": frozen.SOURCE_SHA256, "actual_file_sha256": actual_sha,
            "scope": "Retrospective added lags on the same histogram; not independent validation.",
            "half_width_ps": WIDTH_PS, "signed_lag_counts": counts,
            "periods_with_observed_cross_pairs_at_both_signs":
                [k for k in range(1, 10) if counts[k] > 0 and counts[-k] > 0],
            "center": counts[0], "side_total_across_18_windows": side,
            "center_over_mean_side_exact": str(ratio), "center_over_mean_side": float(ratio),
            "clock_controls": clock_controls(), "intensity_controls": intensity_controls(),
            "next_discriminator": "Extend the pump-indexed acquisition to +/-1024T, outside "
            "this archive. The frozen 1024-cycle has ideal directed AB fraction 0 there; "
            "fair iid exclusive arms give 1/4 before loss. Log no-clicks, resets and phase "
            "slips; calibrate false pairs, delay offsets and live exposure in advance. "
            "A separate synchronized two-arm calibration on common classical input can "
            "check whether a timing mismatch creates an apparent center dip.",
            "conditional_comparison": "Clean periods 1..9 forbid true cross pairs at their "
            "own period. Static same-scalar monotone responses with conditional cross-arm "
            "factorization predict population center >= each side, NOT that every finite "
            "record satisfies the bound. No iid test, replication, p-value or detector-"
            "independent rejection is obtained. Pair counts can reuse clicks."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-file", type=Path, default=frozen.DEFAULT_FILE)
    args = parser.parse_args()
    with args.raw_file.open("rb") as stream:
        data = stream.read(frozen.SOURCE_SIZE + 1)
    print(json.dumps(analyze(data), ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
