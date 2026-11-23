# Calibrating the delayed-return test

Two well-separated launches are not enough. Within **one** launch, the prompt output and its delayed copies may overlap before the meter squares the field. A loop that gives a ratio of 1 for a sub-round-trip pulse gives **4/25** for a two-tick rectangular pulse, even when the loop starts empty, the meter collects all energy and its gain is exact. These are predictions for the [two candidate contacts](WHEN_THIRDS_ARE_ACTUALLY_BUILT.md), not observations.

For this calibration assume full, flat temporal collection, the same temporal pulse shape at both sources and a stationary real normalized overlap sequence C(d), with C(0)=1 and |C(d)| ≤ 1. C(d) is the normalized inner product of the pulse and a copy delayed by d round trips (use the real part for complex pulses). These premises are different from weighting *already separated* energy samples. Write

    A = C(1) − C(2)/2 + C(3)/4 − C(4)/8 + ...

For a unit-energy launch, a diagonal loop output has energy (1−A)/3; an off-diagonal one has (2+A)/6. To see this, use the signed impulse sequence h: its first entry is −1/2 on the diagonal and +1/2 off it; both have tail h[n]=(1/4)(−1/2)^(n−1), n ≥ 1. In the quadratic energy sum, the diagonal in **time** gives sum h[n]^2 = 1/3 at every port. The coefficient of C(d) is twice sum h[n]h[n+d], equal to −(−1/2)^(d−1)/3 and +(−1/2)^(d−1)/6 respectively. The three energies still sum to one. The direct contact has no delayed tail and keeps its ratio 1/16.

| Pulse overlap | Loop diagonal, off-diagonal energy per unit input | Loop ratio |
| --- | --- | --- |
| No overlap at positive delays | 1/3, 1/3 | 1 |
| Two equal consecutive ticks: C(1)=1/2, C(d≥2)=0 | 1/6, 5/12 | 4/25 |
| C(d)=(1/2)^d: **same first-lag overlap** | 1/5, 2/5 | 1/4 |
| C(d)=1: perfectly coherent limiting control | 1/9, 4/9 | 1/16 |

The last row is a coherence limit, not a finite-duration normalized pulse. Measuring only the first lag cannot separate the two middle preparations. A two-copy calibration can measure C(d): apply an equal-strength delayed copy with each relative sign, collect the two energies, and divide their difference by their sum. This requires control of relative sign and stable linear response. If only the first L lags are calibrated, the absolute contribution of all remaining terms to A is at most 2^(1−L); propagate individual calibration uncertainties with weights 2^(1−d). A range overlapping the direct prediction is inconclusive.

For the third row, for example, independent residual errors of magnitude at most ε times the true energy in each of the four cells give a disjoint contrast against 1/16 only for ε < 3−2√2 (about 17.2%), not the 1/3 allowed for separated returns. Each ratio can move up or down by a multiplicative factor ((1+ε)/(1−ε))², so distinguishability requires the upper direct bound to be strictly below the lower loop bound. Real instruments would also require calibration of additive background, gain drift and bandwidth.

The following check, run from the repository root, reads the existing contact dynamics directly. It compares finite pulse trains against the infinite-sum predictions without assuming an exact match after truncation. The omitted tail has absolute amplitude sum 2^(−N) and the full sequence has absolute sum one, bounding the energy change by 2^(1−N).

```python
from fractions import Fraction as F
from scripts.probe_feedback_pulse_gain_control import fields

N = 18
h = fields("loop", 0, N)
samples = (
    (lambda d: int(d == 0), (F(1, 3), F(1, 3))),
    (lambda d: (1, F(1, 2))[d] if d < 2 else 0, (F(1, 6), F(5, 12))),
    (lambda d: F(1, 2)**d, (F(1, 5), F(2, 5))),
    (lambda d: 1, (F(1, 9), F(4, 9))),
)
for overlap, target in samples:
    for j in (0, 1):
        energy = sum(h[m][j] * h[n][j] * overlap(abs(m-n))
                     for m in range(N) for n in range(N))
        if abs(energy - target[j]) > F(2)**(1-N):
            raise ArithmeticError("temporal-overlap calibration mismatch")
print("8 temporal energy controls passed")
```
