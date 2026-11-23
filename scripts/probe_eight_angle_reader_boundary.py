"""Sharp finite reader-capacity controls for a supplied eight-setting target.

x,y are external settings in Z8; the target is cos²(pi*(x-y)/8), not a law
derived here. The two arms see only their own setting and a setting-independent
shared stock. Each sends one symbol to a central Boolean decoder; any extra
randomness can be sampled in that stock. The decoder must not separately see
the settings. No outcomes are discarded. This is an interferometer reader
contract, not a Bell experiment, an exclusion of local realism, a native Z8
plate or an empirical result. Only the even/even restriction is replayed
through the supplied native four-phase contact schedule.
"""

import argparse
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import sqrt

from scripts import probe_native_four_phase_gray as native

FOUR_CELLS = (((0, 1), True), ((0, 7), True), ((2, 1), True), ((2, 7), False))
# One 4x4 mixed-parity block. Wins mean D0 for distance 1 and D1 for distance 3.
BLOCK = tuple(((x, y), (x-y) % 8 in (1, 7))
              for x in (0, 2, 4, 6) for y in (1, 3, 5, 7))
TRITS = (0, 0, 0, 1, 1, 1, 2, 2)
RIGHT_FOUR = (2, 0, 0, 1, 1, 3, 3, 2)
FUSION = (0b001, 0b010, 0b101, 0b110)  # Columns; bits indexed by left symbol.


def chsh_deterministic_scores():
    """Parity forces one or three wins. Mixing cannot exceed three in expectation."""
    scores = set()
    for a0, a2, b1, b7 in product(range(2), repeat=4):
        scores.add((a0 == b1) + (a0 == b7) + (a2 == b1) + (a2 != b7))
    return tuple(sorted(scores))


def decode(a, b):
    return (FUSION[b] >> a) & 1


def triangle_probability(x, y):
    """Half-clock shade compared for equality; also the binary corner of FUSION."""
    return F(sum(decode(int((x+k) % 8 < 4), int((y+k) % 8 < 4))
                 for k in range(8)), 8)


def block_cap(row_symbols, column_symbols):
    """Maximum wins out of 16 for *any* central function and local encoders.

    Enumerate partitions of the four row settings up to renaming. Each possible
    column message represents a Boolean function (bit mask) of the used row
    symbols. Duplicate columns have no effect; unused masks can pad any subset.
    With the candidate mask set fixed, each column setting chooses its own best
    mask. Convexity transfers this deterministic cap to any shared stock.

    For 3x3 there is also a counting argument: merging two opposite rows forces
    four errors. Merging adjacent rows forces two errors in opposite columns.
    A 3-symbol column encoder must merge columns too: an opposite pair costs
    four, while an adjacent pair forces errors in two opposite rows. At least
    one of those lies outside the first adjacent row pair, for >=3 errors.
    """
    if not (1 <= row_symbols <= 4 and column_symbols >= 1):
        raise ValueError("need 1..4 row symbols and at least one column symbol")
    target = tuple(tuple(w for (x, y), w in BLOCK if y == j) for j in (1, 3, 5, 7))
    best = 0
    for row in product(range(row_symbols), repeat=4):
        used = tuple(dict.fromkeys(row))
        if used != tuple(range(len(used))):
            continue
        masks = range(1 << len(used))
        # score[setting][mask] is the number of its four row outcomes correct.
        score = tuple(tuple(sum(((mask >> a) & 1) == w for a, w in zip(row, col, strict=True))
                            for mask in masks) for col in target)
        for allowed in combinations(masks, min(column_symbols, len(masks))):
            best = max(best, sum(max(s[m] for m in allowed) for s in score))
    return best


def trit_probability(x, y):
    """Sharp 3x3 full-grid comparator; shared fair switch selects == or !=."""
    return F(sum((TRITS[(x+k) % 8] == TRITS[(y+k+4*flip) % 8]) ^ flip
                 for k, flip in product(range(8), range(2))), 16)


def sharpened_probability(x, y):
    return F(sum(decode(TRITS[(x+k) % 8], RIGHT_FOUR[(y+k) % 8]) for k in range(8)), 8)


def finite_probability(x, y, m, n):
    """Use 8*n equiprobable stocks, with m of n tags selecting the sharper encoder.

    Because the two protocols differ by 1/8 on odd cells and agree on all
    even cells, rounding n*w to the nearest integer gives error <= 1/(16*n).
    The rounding target w is still supplied externally.
    """
    if type(n) is not int or type(m) is not int or n < 1 or not 0 <= m <= n:
        raise ValueError("need integer 0 <= m <= n, n > 0")
    return F((n-m)*triangle_probability(x, y) + m*sharpened_probability(x, y), n)


def mixed_coefficients(x, y):
    """Exact 3x4 probability a+b*sqrt(2) with one *fixed* decoder.

    Supply rotation k uniformly on Z8. With supplied probability
    w=2*(sqrt(2)-1), send TRITS[x+k], RIGHT_FOUR[y+k]. Otherwise send the two
    binary half-clock shades to the same decoder. w is an imported calibration;
    any finite equiprobable deterministic stock has only rational frequencies.
    """
    base = triangle_probability(x, y)
    delta = sharpened_probability(x, y) - base
    return base - 2*delta, 2*delta


def lower_wins(cells, counts, *, calibration=F(0)):
    """Sum conservative success fractions for D0/D1/total-launched triples.

    Missing cells contribute zero; unresolved launches are never postselected.
    'calibration' subtracts a supplied absolute probability allowance per cell.
    Sampling uncertainty is separate: use a pre-specified sampling design and
    simultaneous confidence allowances before inferring a population violation.
    """
    if not 0 <= calibration <= 1:
        raise ValueError("invalid absolute probability allowance")
    lower = F(0)
    for pair, want_d0 in cells:
        n0, n1, n = counts.get(pair, (0, 0, 0))
        if any(type(v) is not int or v < 0 for v in (n0, n1, n)) or n0+n1 > n:
            raise ValueError("invalid all-launch counts")
        if n:
            lower += max(F(0), F(n0 if want_d0 else n1, n) - calibration)
    return lower


def native_even_check():
    launches = 0
    for x, y in native.SETTINGS:
        outcomes = [native.trial("upstream_full", (True, True), (x, y), s).outcome
                    for s in native.STOCKS]
        expected = triangle_probability(2*x, 2*y)
        if 2 in outcomes or F(outcomes.count(0), len(outcomes)) != expected:
            raise ValueError("even/even native contact replay differs")
        launches += len(outcomes)
    return launches


def verify():
    caps = {(2, 4): 12, (3, 3): 13, (3, 4): 14, (4, 4): 16}
    if chsh_deterministic_scores() != (1, 3) or any(block_cap(*s) != v for s, v in caps.items()):
        raise ValueError("mixed-setting lower-bound certificate changed")
    for x, y in product(range(8), repeat=2):
        d = min((x-y) % 8, (y-x) % 8)
        target = ((1, 0), (F(1, 2), F(1, 4)), (F(1, 2), 0), (F(1, 2), F(-1, 4)), (0, 0))[d]
        if (triangle_probability(x, y) != 1 - F(d, 4)
                or trit_probability(x, y) != (1, F(13, 16), F(1, 2), F(3, 16), 0)[d]
                or mixed_coefficients(x, y) != target):
            raise ValueError(f"full-grid attainment failed at {(x, y)}")
    # The ideal per-cell win probability on mixed settings is (2+sqrt(2))/4.
    # A uniform absolute probability error epsilon costs at most n*epsilon on
    # an n-cell witness. The full-grid constructors meet these bounds exactly.
    return {"scope": __doc__, "native_even_even_launches": native_even_check(),
            "checked_external_setting_pairs": 64, "equality_four_cell_cap": 3,
            "general_fusion_caps_out_of_16": {f"{m}x{n}": k for (m, n), k in caps.items()},
            "minimax_uniform_probability_errors": {
                "binary_equality": "(sqrt(2)-1)/4", "any_binary_side": "(sqrt(2)-1)/4",
                "two_trits_shared_stock_decoder": "(4*sqrt(2)-5)/16", "3x4_fixed_decoder": "0"},
            "imported_3x4_mixture_weight": "2*(sqrt(2)-1)",
            "rounded_3x4_mixture": "8*n equiprobable stocks: uniform error at most 1/(16*n)",
            "odd_distance_ideal_win_probability": (2+sqrt(2))/4}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    options = parser.parse_args()
    report = verify()
    if options.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print(f"{report['native_even_even_launches']} native Z4 launches; 64 external Z8 cells.")
        print("Mixed-block caps /16: one binary arm 12; two trits 13; 3x4 symbols 14.")
        print("Uniform errors: binary 0.103553..., trits 0.041053..., calibrated 3x4 0.")
        print("Reader-contract separation only; no native eight-phase fringe or experimental claim.")
