"""Fixed-input, fixed-port recurrence in a supplied three-slot mixer model.

One run injects e0, applies t copies of D=T12 T01 without intermediate
measurement, and reads port 0's squared norm. Each transparent pair gate is
[[1+i, 1-i], [1-i, 1+i]]/2, with identity bypass. This is NOT the
A B³ operator-infinite-order word in NativeMixerInfiniteOrder.lean.

Both gates are unitary (eigenvalues 1,i on sums/differences) and fix the
uniform direction. D has determinant -1 and trace 1+3i/2 (its diagonal
is a,a²,a for a=(1+i)/2). On the orthogonal plane its roots are therefore
i exp(±iθ), cos θ=3/4, sin θ=√7/4. The return amplitude is the sum of
these eigenvalues to power t weighted by the squared projections of e0.
The uniform weight is 1/3, so w+ + w- = 2/3. At t=1 the amplitude a
gives w+ - w- = -2/(3√7). The program cross-checks every sampled port
probability using these facts and an independent Gaussian-integer gate walk.

If θ/π were rational, 2 cos θ would be a root of a monic integer
polynomial (a root of unity plus its inverse) but it equals 3/2.
Hence cos(4Lkθ) is dense in [-1,1] for every positive integer L.
On t=4k the readout is f(u)=(11+28u+24u²)/63 for u=cos(tθ).

For a fixed finite time-homogeneous stochastic matrix P, there is an L
with P^(Ln) converging: take the lcm of the periods of the closed classes;
on these cyclic subclasses P^L mixes, while transient mass decays. Thus
μ P^(4Lk) r converges for any initial distribution μ and fixed event
responses r in [0,1]. Subsequences of the native readout there approach
both extrema of f. Any uniform all-time approximation in this model
has error at least half their separation, not necessarily at a finite
specified horizon. The bound is sharp: at even t the formula is f(±u);
at odd t it is 31/54 - (s ∓ 1/3)²/6, with s=sin(tθ)/sin θ.
A deterministic parity counter can emit the midpoint 395/756 on even t
and 1/3 on odd t (where the error is at most 1/3). For every horizon M,
an M+1 state saturating counter with the prefix as event responses fits
exactly; it does not approximate all times to arbitrary accuracy.

On a *fixed* prefix, H[i,j]=p(i+j) factors as rows μ P^i times columns
P^j r in any homogeneous d-dimensional linear model. Nonzero determinant
for the first 7x7 Hankel matrix thus excludes d≤6 even without stochastic
constraints; d counts linear coordinates, not quantum Hilbert dimension.
Conversely, squared amplitude from three spectral components uses at most
seven exponentials (constant plus six ordered off-diagonal ratios), so
the infinite exact Hankel rank is seven when the minor is nonsingular.
External clocks, time-varying channels, postselection and nonlinear
hidden-state readouts are not covered. Neither physical accessibility,
the detector law, nor experimental verification is established here.

Run: python3 -O -m scripts.probe_native_recurrence_witness
"""

from collections.abc import Iterator, Sequence
from fractions import Fraction as F

Gaussian = tuple[int, int]
Table = list[list[F]]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def gate(v: Sequence[Gaussian], left: int) -> list[Gaussian]:
    """One denominator-2 step; double the bypass numerator as well."""
    right = left + 1
    a, b = v[left]
    c, d = v[right]
    out = [(2 * x, 2 * y) for x, y in v]
    out[left] = (a - b + c + d, a + b - c + d)
    out[right] = (a + b + c - d, -a + b + c + d)
    return out


def native_prefix(horizon: int) -> list[F]:
    require(horizon >= 0, "negative time")
    v = [(1, 0), (0, 0), (0, 0)]
    denominator = 1
    values = []
    for t in range(horizon + 1):
        total = sum(x * x + y * y for x, y in v)
        require(total == denominator**2, f"norm at t={t}")
        x, y = v[0]
        values.append(F(x * x + y * y, total))
        v = gate(gate(v, 0), 1)
        denominator *= 4  # squared norm denominator is 16^t, not 4^t
    return values


def fourth_slice(u: F) -> F:
    return (11 + 28 * u + 24 * u * u) / 63


def spectral_values() -> Iterator[tuple[F, F, F]]:
    """(p(t), cos(tθ), sin(tθ)/sin θ), using only rationals."""
    c_prev, c = F(3, 4), F(1)
    s_prev, s = F(-1), F(0)
    t = 0
    while True:
        x, y = 2 * c / 3, -s / 6
        for _ in range(t % 4):
            x, y = -y, x
        yield (F(1, 3) + x) ** 2 + y * y, c, s
        c_prev, c = c, F(3, 2) * c - c_prev
        s_prev, s = s, F(3, 2) * s - s_prev
        t += 1


def invert(h: Table) -> tuple[F, Table]:
    """Exact determinant and inverse by row operations (no float thresholds)."""
    n = len(h)
    a = [row + [F(i == j) for j in range(n)] for i, row in enumerate(h)]
    det = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            raise ValueError(f"singular minor at column {j}")
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            det = -det
        v = a[j][j]
        det *= v
        a[j] = [x / v for x in a[j]]
        for i in range(n):
            if i != j:
                q = a[i][j]
                a[i] = [x - q * y for x, y in zip(a[i], a[j], strict=True)]
    return det, [row[n:] for row in a]


def hankel_certificate(values: Sequence[F]) -> tuple[F, F]:
    n = 7
    h = [[values[i + j] for j in range(n)] for i in range(n)]
    det, inv = invert(h)
    for i in range(n):
        for j in range(n):
            require(
                sum(h[i][k] * inv[k][j] for k in range(n)) == int(i == j),
                "inverse certificate",
            )
    # Singular H+E needs ||H^-1 E||∞ >= 1, whereas ||E||∞ <= n max|Eij|.
    tolerance = F(1) / (n * max(sum((abs(x) for x in row), F(0)) for row in inv))
    return det, tolerance


def run() -> None:
    values = native_prefix(128)
    for t, (p, (q, u, s)) in enumerate(zip(values, spectral_values())):
        require(p == q, f"independent spectral cross-check at t={t}")
        sign = -1 if t % 4 >= 2 else 1
        if t % 2 == 0:
            require(p == fourth_slice(sign * u), f"even slice at t={t}")
        else:
            odd = F(31, 54) - (s - F(sign, 3)) ** 2 / 6
            require(p == odd, f"odd slice at t={t}")
    # Convex quadratic: vertex gives minimum, larger endpoint gives maximum.
    low = fourth_slice(F(-7, 12))
    high = max(fourth_slice(F(-1)), fourth_slice(F(1)))
    gap = (high - low) / 2
    require((low, high, gap) == (F(17, 378), F(1), F(361, 756)), "extrema")
    midpoint = (high + low) / 2
    require(midpoint == F(395, 756) and F(31, 54) < F(2, 3), "parity fit")
    det, tolerance = hankel_certificate(values)
    print("supplied mixer, e0 injection, one terminal port-0 squared-norm readout")
    print("first 13 probabilities:", ", ".join(str(p) for p in values[:13]))
    print(f"Hankel 7x7 determinant={det}; exact scalar Hankel rank=7")
    print(f"any ≤6-state homogeneous linear fit: max prefix error ≥ {tolerance}")
    print(f"t=4Lk native limit range [{low}, {high}] for every L≥1")
    print(f"any fixed finite homogeneous stochastic fit: all-time sup error ≥ {gap}")
    print(
        f"sharp: a two-state parity counter attains {gap} (responses {midpoint}, 1/3)"
    )
    print("every finite prefix t=0..M admits an exact (M+1)-state counter fit")
    print("model-conditional analytical witness; not an experiment or Lean proof")


if __name__ == "__main__":
    run()
