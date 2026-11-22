"""Can four classical colors carry a sequence of six-position phase choices?

One heralded emission, five serial stations on one arm, one static spectator
arm, one terminal detector pair. At each station choose a fresh uniform
x in Z/6, independent of every earlier setting, preparation and apparatus
seed. Supply x copies of a common increment, or a six-position dial. Read
Y=+1 for right only, -1 for left only, 0 for no/double click. Use EVERY
emission in S=E[Y cos(pi sum(x)/3)]; the six final totals are equally likely.
The benchmark right-port probabilities (1,3/4,1/4,0,1/4,3/4), with the
remaining probability at left, give S=1/2. They are a proposed comparison,
not a derivation, a calibration from these data, or a measured IDT fringe.

RIVAL. Across each interstation cut only d<=4 dynamic classical symbols may
carry information about earlier inputs. Conditional on arbitrary static
shared randomness (including initial source/spectator correlations and
prior-trial history), a station may use ANY stochastic kernel K(t|s,x),
different at every station. Reusing one randomized update is included.
The last station/reader may see its current x directly. No other register,
timing channel, adaptive setting history or writable reference may carry
past x's to later stations or the detector. A trial-static reference is
free; fresh independent stochasticity is free; a changing shared reference
is memory and counts. Calibration and source heralding must precede the
choices; equal-duration slots avoid an unintended pulse-count channel.
Conditioning on occupied/vacant and the untouched arm leaves four colors
in the eight-label occupation-conserving candidate, not eight dynamic
symbols. A joint operation that changes the other arm is a different null.

BOUND. Write w=exp(i*pi/3), v_j(s)=E[w^(x1+...+xj) 1_{state=s}].
For one input state s, the sum over outputs t of
|sum_x w^x K(t|s,x)|/6 is at most C_d: by convexity it suffices to
partition the six inputs among d output labels, maximizing the sum of
the polygon resultants divided by six. Independence and triangle inequality
now give ||v_j||_1 <= C_d ||v_(j-1)||_1, initially ||v_0||_1=1.
The terminal mean Y lies in [-1,1]; randomizing between signs represents
even a no-click mean of zero, so the terminal scalar factor is at most C_2.
Consequently |S| <= C_2 C_4^(k-1), also after averaging over shared seeds.
The exact finite partition maxima are C_2=2/3 and C_4=(1+sqrt(3))/3.
For k=5 the bound is (56+32 sqrt(3))/243 < 23/50. Five stations are first
for THIS certificate, not necessarily optimal. Beating it does not identify
quantum physics, imply six symbols are necessary, or establish a native
six-position plate. Below, a positive six-state counter reproduces the
entire benchmark using an independently supplied stochastic port readout.

ROBUSTNESS. If each conditional outcome distribution is within total
variation epsilon of the benchmark, each conditional mean Y changes by at
most 2 epsilon. E[|cos|]=2/3, so epsilon<=3/100 keeps S>=23/50, strictly
above the exact bound. This is a sufficient distribution-level margin, not
a confidence interval for finite or device-selected data. An ideal fringe
with constant, setting-independent detection efficiency eta instead has
S=eta/2: missed emissions cannot be silently normalized away.

Experimental relative, not validation: Trojek et al., Phys. Rev. A 72,
050305 (2005), https://arxiv.org/abs/quant-ph/0502066, did use five serial
phase controls. Their task B uses continuous settings weighted jointly by
|cos(sum)| and N-1 classical bits total for N parties. They retained
exactly-one-trigger windows and included analyzer misses by assigning a
random guess. It is not this independently randomized six-setting test of
four-symbol interstation memory; no measurement or replication is claimed.

Run: python3 -B -m scripts.probe_serial_phase_memory
"""

import sys
from fractions import Fraction as F
from itertools import product
from math import sqrt
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts import probe_eight_label_interferometer as native

PHASES = range(6)
# (2 Re(w^x), 2 Im(w^x)/sqrt(3)). Only the first coordinate scores a shot.
HEX = ((2, 0), (1, 1), (-1, 1), (-2, 0), (-1, -1), (1, -1))
RIGHT_QUARTERS = (4, 3, 1, 0, 1, 3)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def positive(a: int, b: int) -> bool:
    """Compare a+b sqrt(3) to zero exactly."""
    if a >= 0 and b >= 0:
        return bool(a or b)
    if a <= 0 and b <= 0:
        return False
    if a > 0:
        return a * a > 3 * b * b
    return 3 * b * b > a * a


def partition_maximum(symbols: int) -> tuple[int, int]:
    """Exact 6*C_d in integer coordinates of 1,sqrt(3); empty bins allowed."""
    # Every subset of this regular hexagon has length 0, 1, sqrt(3) or 2.
    lengths = {0: (0, 0), 4: (1, 0), 12: (0, 1), 16: (2, 0)}
    radii = []
    for mask in range(64):
        a = sum(x for j, (x, _) in enumerate(HEX) if mask >> j & 1)
        b = sum(y for j, (_, y) in enumerate(HEX) if mask >> j & 1)
        radii.append(lengths[a * a + 3 * b * b])
    best = (0, 0)
    for assignment in product(range(symbols), repeat=6):
        bins = [0] * symbols
        for x, t in enumerate(assignment):
            bins[t] |= 1 << x
        a, b = (sum(radii[m][i] for m in bins) for i in range(2))
        if positive(a - best[0], b - best[1]):
            best = (a, b)
    return best


def four_color_bound(k: int) -> tuple[int, int, int]:
    """The certificate (a+b sqrt(3))/den, not the optimum game score."""
    require(k >= 1, "need at least one station")
    a, b, den = 2, 0, 3
    for _ in range(k - 1):
        a, b, den = a + 3 * b, a + b, 3 * den
    return a, b, den


def detector(left: int, right: int) -> int:
    require(left in (0, 1) and right in (0, 1), "expected binary ports")
    return right - left


def native_score_table() -> tuple[int, ...]:
    """Two ready plate references return unchanged; one fixed source, fair vacuum."""
    native.verify_raw_coupler()
    action = native.verify_plate()
    # Apply the native plate x times, not a fitted per-setting hidden operation.
    starts = [native.coupler(native.source_pair(0, 0, v)) for v in native.PHASES]
    sums = []
    for x in PHASES:
        total = 0
        for left, right in starts:
            for _ in range(x):
                left = action[left]
            output = native.coupler((left, right))
            dl, dr = map(native.number, output)
            require(dl + dr == 1, "unexpected loss or multi-event in native control")
            total += detector(dl, dr)
        sums.append(total)
    require(all(action[action[s]] == s for s in native.LABELS), "plate not period two")
    require(sums == [2, -2, 2, -2, 2, -2], "changed native XOR response")
    return tuple(sums)


def triangle_score_table(max_pulses: int) -> list[F]:
    """Reusable stochastic increment: stay or advance on a triangle, each 1/2."""
    paths = [1, 0, 0]
    result = []
    for n in range(max_pulses + 1):
        require(sum(paths) == 2**n, "lost triangle Markov paths")
        # Fixed stochastic readout means are 1, -1/2, -1/2 on the three states.
        mean = F(2 * paths[0] - paths[1] - paths[2], 2 ** (n + 1))
        # Each pulse multiplies the mean complex phase by (1+w^2)/2 = w/2.
        require(mean == F(HEX[n % 6][0], 2 ** (n + 1)), "wrong triangle diffusion")
        result.append(mean)
        paths = [paths[j] + paths[j - 1] for j in range(3)]
    return result


def check_emissions(k: int = 5) -> tuple[F, F, F, F, F]:
    """Enumerate all independent control words, then all fair readout seeds."""
    xor = native_score_table()
    triangle = triangle_score_table(5 * k)
    counts_by_pulses = [0] * len(triangle)
    positive_numer = xor_numer = matched = 0
    counts = [0] * 6
    for word in product(PHASES, repeat=k):
        memory = 0
        for x in word:
            memory = (memory + x) % 6
        pulses = sum(word)
        counts_by_pulses[pulses] += 1
        total = pulses % 6
        counts[total] += 1
        c2 = HEX[total][0]
        quarter_sum = 0
        for seed in range(4):
            right = int(seed < RIGHT_QUARTERS[memory])
            quarter_sum += detector(1 - right, right)
        require(quarter_sum == 2 * c2, "wrong conditional six-state fringe")
        positive_numer += c2 * quarter_sum
        xor_numer += c2 * xor[total]
        # Two-state loss spoof: a mismatch latches a silent shot permanently.
        # With only registered shots the spurious score would be 1.
        matched += int(not any(word))
    n = 6**k
    require(counts == [n // 6] * 6, "settings are not uniformly accounted")
    ideal, xor_score = F(positive_numer, 8 * n), F(xor_numer, 4 * n)
    loss_spoof = F(matched, n)
    # Six-state false negative: an independent 1/8 chance to scramble the
    # final residue uniformly before reading. Its fringe survives but is weaker.
    require(sum(RIGHT_QUARTERS) == 12, "scrambled readout has nonzero mean")
    dephased = F(7, 8) * ideal
    require(
        (ideal, xor_score, loss_spoof, dephased) == (F(1, 2), F(0), F(1, n), F(7, 16)),
        "unexpected all-emission controls",
    )
    triangle_score = sum(
        c * HEX[j % 6][0] * triangle[j] for j, c in enumerate(counts_by_pulses)
    ) / (2 * n)
    require(
        0 < triangle_score < F(7, 16),
        "stochastic triangle should retain partial contrast",
    )
    return ideal, xor_score, loss_spoof, dephased, triangle_score


def main() -> None:
    require(detector(0, 0) == detector(1, 1) == 0, "null/double click mishandled")
    require(partition_maximum(2) == (4, 0), "wrong binary partition bound")
    require(partition_maximum(4) == (2, 2), "wrong four-color partition bound")
    a4, b4, d4 = four_color_bound(4)
    require(positive(2 * a4 - d4, 2 * b4), "four-station certificate already excludes")
    a, b, d = four_color_bound(5)
    require((a, b, d) == (56, 32, 243), "wrong five-station bound")
    require(positive(23 * d - 50 * a, -50 * b), "bound not below 23/50")
    require(positive(16 * a - 7 * d, 16 * b), "dephased control exceeds bound")
    mean_abs_cos = F(sum(abs(a2) for a2, _ in HEX), 12)
    require(
        F(1, 2) - 2 * F(3, 100) * mean_abs_cos == F(23, 50),
        "wrong uniform total-variation margin",
    )
    ideal, xor, spoof, dephased, triangle = check_emissions()
    print("Five independent six-position dials; all 7776 words retained.")
    print(
        f"Four dynamic colors, stochastic kernels and shared seeds: |S| <= "
        f"(56+32 sqrt(3))/243 = {(a + b * sqrt(3)) / d:.6f}."
    )
    print(
        f"Supplied six-state counter: S={ideal}; native eight-label XOR plate: S={xor}."
    )
    print(f"Three-state reusable stochastic plate: S={triangle} (partial contrast).")
    print(
        f"Scrambled six-state control: S={dephased} (inconclusive); "
        f"two-state loss spoof: S={spoof} (illegally dropping misses: 1)."
    )
    print(
        "Benchmark advantage > 1/25 in mean score; not an observed difference "
        "or a bound on a device with a changing hidden reference."
    )


if __name__ == "__main__":
    main()
