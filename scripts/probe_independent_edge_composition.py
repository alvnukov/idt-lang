"""Conditional finite composition control for the retained cube edge.

Fix adjacent cube words differing only in coordinate 0. A local edge marker
retains the erasure axis and the other two bits. When axis 0 is erased it is
common to the two words; otherwise it reveals the source bit. An additional
independent fair endpoint is uninformative conditional on the edge.

Under independent preparation records, the all-erased marker has common mass
w = 3**-n, and no other marker is shared by every input. For any normalized
source-blind decoder, summing the diagonal over all source words allocates
all of w to that sum. If the decoder can lose an outcome, with conditional
loss l on the shared marker, the sum is at least w(1-l), and every input loses
at least w*l. This is an unconditional inequality, not one for postselected
rows. A uniform guess when all bits are erased and a deliberate mismatch
otherwise attain w/2**n for both mean and maximum diagonal.

The supplied quantum comparator is not obtained from the cube. Put
t = sqrt(3)-sqrt(2), c = 1/sqrt(1+t**2) and use states c*(|0>+(-1)**x*t*|1>).
Their overlap is sqrt(2/3). For n copies let d = 2**n. Averaging any POVM over
simultaneous XOR shifts of inputs and output labels preserves mean diagonal
and makes each diagonal equal to that mean. The seed effect of a covariant
POVM has diagonal 1/d, by completeness and Walsh orthogonality, so it is a
Gram matrix of vectors of norm 1/sqrt(d). Its diagonal probability is the
squared norm of their sum with weights c**n*t**wt(z). The largest side has
weight c**n. The reverse triangle inequality supplies the bound; lining up
all other sides opposite it, or closing the polygon in the complex plane
when possible, attains it with a rank-one seed. Therefore the optimal mean
and minimax are both c**(2*n)*max(0, 2-(1+t)**n)**2/d. This argument concerns
the supplied complex states and all d-outcome POVMs, not all cube models.

The Walsh formula and an independent complex tensor-state/basis calculation
are compared numerically. Exact rational arithmetic verifies the marker laws;
rational interval arithmetic certifies strict comparator margins. The n=3
diagonal is zero algebraically: 1-2*t*cos(theta)-t-3*t**2-t**3 = 0 by the
chosen cos(theta). Floating-point agreement is not a proof of that equality.
For n=2 the amplitudes reduce using (1-t**2)/(1+t**2)=sqrt(2/3) and
2*t/(1+t**2)=1/sqrt(3). Mixing uniform outputs at weight eta moves the
diagonal q to (1-eta)*q+eta/d, yielding the two exact noise thresholds shown.

The correlated escapes apply only to these aligned preparations and to this
fixed output setting. They change the joint erasure law, despite matching
single-copy laws (and in one case pair laws): the masks are source-independent
and each marker is obtained from just its local mask and input. The partial
decoder's offset law b depends only on relative bits; on fully visible records
set the offset law to (p-b)/w_full, where p is the comparator offset law.
Unit-modulus phases preserve the orthonormal Walsh basis, so sum(p)=1, and
sum(b)=1-w_full by normalized partial decoding. Thus the residual is exactly
normalized and its positivity checks make b+w_full*(p-b)/w_full=p for every
source. Nothing here tests a physical detector or proves independence,
quantum rules, or general composition.
"""

from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt, sqrt

Mask = tuple[int, ...]
Edge = tuple[int, tuple[int, ...]]
Record = tuple[Edge, ...]
Partial = tuple[int, ...]
RationalRow = tuple[F, ...]
FloatRow = tuple[float, ...]
Vector = tuple[complex, ...]

AXES = (0, 1, 2)
UNKNOWN = -1
TOL = 2e-14


def check(test: bool, message: str) -> None:
    if not test:
        raise RuntimeError(message)


@dataclass(frozen=True)
class Bounds:
    lo: F
    hi: F

    def __add__(self, other: "Bounds") -> "Bounds":
        return Bounds(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other: "Bounds") -> "Bounds":
        return Bounds(self.lo - other.hi, self.hi - other.lo)

    def __mul__(self, other: "Bounds") -> "Bounds":
        endpoints = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Bounds(min(endpoints), max(endpoints))

    def __truediv__(self, other: "Bounds") -> "Bounds":
        check(other.lo > 0, "interval divisor must be positive")
        return self * Bounds(1 / other.hi, 1 / other.lo)

    def square(self) -> "Bounds":
        lo, hi = sorted((self.lo**2, self.hi**2))
        return Bounds(F(0) if self.lo <= 0 <= self.hi else lo, hi)

    def power(self, exponent: int) -> "Bounds":
        result = point(1)
        for _ in range(exponent):
            result *= self
        return result


def point(value: int | F) -> Bounds:
    return Bounds(F(value), F(value))


def root_bounds(value: int) -> Bounds:
    scale = 10**15
    lower = isqrt(value * scale * scale)
    check(lower**2 <= value * scale**2 < (lower + 1) ** 2, "sqrt bracket")
    return Bounds(F(lower, scale), F(lower + 1, scale))


def lower_decimal(value: F, places: int = 12) -> str:
    scale = 10**places
    scaled = value * scale
    whole, fraction = divmod(scaled.numerator // scaled.denominator, scale)
    return f"{whole}.{fraction:0{places}d}"


def sign(word: int) -> int:
    return -1 if word.bit_count() % 2 else 1


def bits(word: int, n: int) -> tuple[int, ...]:
    return tuple((word >> shift) & 1 for shift in reversed(range(n)))


def emit(source: int, mask: Mask) -> Record:
    return tuple(
        (k, tuple(bit for j, bit in enumerate((x, 0, 0)) if j != k))
        for x, k in zip(bits(source, len(mask)), mask, strict=True)
    )


def read(record: Record) -> Partial:
    return tuple(UNKNOWN if k == 0 else shown[0] for k, shown in record)


def mask_law(masks: Iterable[Mask]) -> dict[Mask, F]:
    counts = Counter(masks)
    return {mask: F(count, counts.total()) for mask, count in counts.items()}


def floor_decoder(record: Record, common_loss: F) -> RationalRow:
    revealed = read(record)
    d = 1 << len(revealed)
    for k, bit in enumerate(revealed):
        if bit != UNKNOWN:
            y = (1 - bit) << (len(revealed) - 1 - k)
            return tuple(F(int(j == y)) for j in range(d + 1))
    return (*((1 - common_loss) / d for _ in range(d)), common_loss)


def replay_independent(n: int) -> None:
    d = 1 << n
    masks = tuple(product(AXES, repeat=n))
    laws = tuple({emit(x, mask): F(1, 3**n) for mask in masks} for x in range(d))
    common = set.intersection(*(set(law) for law in laws))
    overlap = sum(min(law[s] for law in laws) for s in common)
    check(overlap == F(1, 3**n), "wrong common overlap")
    for loss_on_common in (F(0), F(1, 7), F(1)):
        diagonal, losses = [], []
        for x, law in enumerate(laws):
            check(sum(law.values()) == 1, "unnormalized preparation")
            diagonal.append(
                sum(
                    mass * floor_decoder(s, loss_on_common)[x]
                    for s, mass in law.items()
                )
            )
            losses.append(
                sum(
                    mass * floor_decoder(s, loss_on_common)[d]
                    for s, mass in law.items()
                )
            )
            for s in law:
                row = floor_decoder(s, loss_on_common)
                check(sum(row) == 1 and min(row) >= 0, "invalid floor decoder")
        check(
            set(diagonal) == {(1 - loss_on_common) * F(1, 6**n)}
            and sum(diagonal) + min(losses) == overlap,
            "attainability or loss equality failed",
        )


def compare_amplitudes(n: int) -> tuple[FloatRow, float, float]:
    """Two routes: an offset Walsh sum, and explicit complex vectors."""
    d = 1 << n
    t = sqrt(3) - sqrt(2)
    c = 1 / sqrt(1 + t * t)
    phases = [1 + 0j, *([-1 + 0j] * (d - 1))]
    if n == 3:
        cosine = (1 - t - 3 * t**2 - t**3) / (2 * t)
        sine = sqrt(1 - cosine**2)
        phases[4], phases[2] = complex(-cosine, -sine), complex(-cosine, sine)

    row = tuple(
        c ** (2 * n)
        / d
        * abs(sum(t ** z.bit_count() * phases[z] * sign(z & delta) for z in range(d)))
        ** 2
        for delta in range(d)
    )

    def tensor(factors: Iterable[tuple[complex, complex]]) -> Vector:
        vector: Vector = (1 + 0j,)
        for pair in factors:
            vector = tuple(a * b for a in vector for b in pair)
        return vector

    def inner(left: Vector, right: Vector) -> complex:
        return sum((a.conjugate() * b for a, b in zip(left, right, strict=True)), 0j)

    states = tuple(
        tensor(
            (complex(c), complex(c * t if x_i == 0 else -c * t)) for x_i in bits(x, n)
        )
        for x in range(d)
    )
    basis = tuple(
        tuple(
            phase.conjugate() * amplitude
            for phase, amplitude in zip(phases, raw, strict=True)
        )
        for y in range(d)
        for raw in (
            tensor(
                (complex(1 / sqrt(2)), complex((-1 if y_i else 1) / sqrt(2)))
                for y_i in bits(y, n)
            ),
        )
    )
    basis_error = max(
        abs(inner(basis[y], basis[z]) - int(y == z)) for y in range(d) for z in range(d)
    )
    state_error = max(
        abs(inner(states[x], states[y]) - sqrt(2 / 3) ** (x ^ y).bit_count())
        for x in range(d)
        for y in range(d)
    )
    direct = tuple(tuple(abs(inner(v, s)) ** 2 for v in basis) for s in states)
    row_error = max(abs(direct[x][y] - row[x ^ y]) for x in range(d) for y in range(d))
    check(
        max(basis_error, state_error, row_error, *(abs(sum(p) - 1) for p in direct))
        < TOL,
        "complex oracle or normalization mismatch",
    )
    check(
        abs(row[0] - c ** (2 * n) * max(0, 2 - (1 + t) ** n) ** 2 / d) < TOL,
        "phase choice does not reach the analytic optimum",
    )
    return (
        ((0.0, *row[1:]) if n == 3 else row),
        max(basis_error, state_error),
        row_error,
    )


def certify_comparator(n: int) -> tuple[Bounds, ...]:
    r2 = root_bounds(2)
    t = root_bounds(3) - r2
    gain = (point(1) / (point(1) + t.square())).power(n) / point(1 << n)
    d = 1 << n
    polygon = (point(1) + t).power(n)
    check(polygon.hi < 2 if n == 2 else polygon.lo > 2, "wrong polygon regime")
    cosine = (point(1) - t - point(3) * t.square() - t.power(3)) / (point(2) * t)
    check(-1 < cosine.lo <= cosine.hi < 1, "invalid n=3 phase cosine")
    row = []
    for y in range(d):
        if n == 3 and y == 0:
            row.append(point(0))  # By the stated algebraic cancellation.
            continue
        real = point(1)
        for z in range(1, d):
            factor = cosine if n == 3 and z in (2, 4) else point(1)
            real -= point(sign(y & z)) * t.power(z.bit_count()) * factor
        imag_square = point(0)
        if n == 3:
            imag_square = (point(sign(y & 2) - sign(y & 4)) * t).square() * (
                point(1) - cosine.square()
            )
        row.append(gain * (real.square() + imag_square))

    if n == 2:
        expected = (
            (point(3) - point(2) * r2) / point(12),
            point(F(1, 4)),
            point(F(1, 4)),
            (point(3) + point(2) * r2) / point(12),
        )
        check(
            all(max(a.lo, b.lo) <= min(a.hi, b.hi) for a, b in zip(row, expected)),
            "n=2 closed form disagrees with Walsh computation",
        )
        check(0 < row[0].lo, "n=2 diagonal must be strictly positive")
    check(row[0].hi < F(1, 6**n), "strict independent-composition separation")
    check(min(p.lo for p in row[1:]) > 0, "off-diagonal positivity")
    return tuple(row)


def flip_known(revealed: Partial) -> RationalRow:
    """Flip one uniformly selected revealed bit; guess missing bits fairly."""
    n = len(revealed)
    known = sum(bit != UNKNOWN for bit in revealed)
    check(known > 0, "flip-known requires a revealed bit")
    row = tuple(
        F(
            int(sum(b != a for a, b in zip(revealed, bits(y, n)) if a != UNKNOWN) == 1),
            known * (1 << (n - known)),
        )
        for y in range(1 << n)
    )
    check(sum(row) == 1 and min(row) >= 0, "invalid partial decoder")
    return row


def patterns(law: dict[Mask, F]) -> dict[tuple[bool, ...], F]:
    masses: dict[tuple[bool, ...], F] = {}
    for mask, w in law.items():
        key = tuple(k == 0 for k in mask)
        masses[key] = masses.get(key, F(0)) + w
    return masses


def check_uniform_margins(law: dict[Mask, F], order: int, n: int) -> None:
    for places in combinations(range(n), order):
        for axes in product(AXES, repeat=order):
            mass = sum(
                w for mask, w in law.items() if tuple(mask[i] for i in places) == axes
            )
            check(mass == F(1, 3**order), "wrong correlated marginal")


def replay_escape(
    n: int, target: FloatRow, bounds: tuple[Bounds, ...]
) -> tuple[float, F]:
    expected: RationalRow
    if n == 2:
        law = mask_law((r, (r + 1) % 3) for r in AXES)
        expected = (F(0), F(1, 6), F(1, 6), F(1, 3))
    else:
        law = mask_law((a, b, (1 - a - b) % 3) for a, b in product(AXES, repeat=2))
        expected = tuple(
            (F(0), F(1, 12), F(1, 9), F(1, 12))[y.bit_count()] for y in range(8)
        )
        check_uniform_margins(law, 2, n)
        pattern_mass = patterns(law)
        for pattern in product((False, True), repeat=3):
            mass = (F(1, 3), F(1, 9), F(1, 9), F(0))[sum(pattern)]
            check(
                pattern_mass.get(pattern, F(0)) == mass,
                "wrong pairwise erasure pattern",
            )
    check_uniform_margins(law, 1, n)
    check((0,) * n not in law and sum(law.values()) == 1, "invalid correlated mask law")
    complete = sum((w for mask, w in law.items() if 0 not in mask), F(0))
    check(complete == F(1, 3), "wrong fully visible mass")
    d = 1 << n
    base = tuple(
        sum(
            (
                w * flip_known(read(emit(0, mask)))[y]
                for mask, w in law.items()
                if 0 in mask
            ),
            F(0),
        )
        for y in range(d)
    )
    check(base == expected and sum(base) == 1 - complete, "wrong offset base law")
    residual_floor = min(
        (p.lo - b) / complete for p, b in zip(bounds, base, strict=True)
    )
    check(residual_floor >= 0, "negative certified complete-marker residual")
    positive_floor = min(
        (p.lo - b) / complete for p, b in zip(bounds[1:], base[1:], strict=True)
    )
    check(positive_floor > 0, "nonzero offsets must have a strict residual margin")
    # Exactly normalized in the algebra: (sum(target) - sum(base))/complete = 1.
    residual = tuple(
        (p - float(b)) / float(complete) for p, b in zip(target, base, strict=True)
    )
    check(min(residual) >= 0 and abs(sum(residual) - 1) < TOL, "invalid residual row")

    def decode(record: Record) -> FloatRow:
        visible = read(record)
        if UNKNOWN in visible:
            return tuple(map(float, flip_known(visible)))
        revealed_word = sum(bit << (n - 1 - i) for i, bit in enumerate(visible))
        return tuple(residual[revealed_word ^ y] for y in range(d))

    max_error = 0.0
    for x in range(d):
        rows = tuple((float(w), decode(emit(x, mask))) for mask, w in law.items())
        for _, row in rows:
            check(min(row) >= 0 and abs(sum(row) - 1) < TOL, "bad correlated decoder")
        p = tuple(sum(w * row[y] for w, row in rows) for y in range(d))
        check(abs(sum(p) - 1) < TOL, "unnormalized correlated replay")
        max_error = max(max_error, *(abs(p[y] - target[x ^ y]) for y in range(d)))
    check(max_error < TOL, "correlated replay mismatch")
    return max_error, positive_floor


def cyclic_control(bounds: tuple[Bounds, ...]) -> Bounds:
    law = mask_law(tuple((r + i) % 3 for i in range(3)) for r in AXES)
    check_uniform_margins(law, 1, 3)
    check(
        all(mask.count(0) == 1 for mask in law), "cyclic mask must always erase one bit"
    )
    for x in range(8):
        check(
            all(flip_known(read(emit(x, mask)))[x] == 0 for mask in law), "cyclic zero"
        )
    # With any decoder, each per-mask response ignores one input bit, so the
    # alternating sum over x vanishes for each fixed y. For y=0 in the
    # comparator, that sum is instead bounded strictly away from zero.
    parity = point(0)
    for x, b in enumerate(bounds):
        parity += point(sign(x)) * b
    check(parity.lo > 0, "comparator must contain a nonzero full input parity")
    return parity


def main() -> None:
    print("Conditional aligned-edge composition control; quantum comparator supplied.")
    for n in range(1, 5):
        replay_independent(n)
    print("Independent markers: exact overlap 3^-n, mean/minimax diagonal 6^-n;")
    print("  loss floor sum(diagonal)+min(loss) >= 3^-n (unconditional).")
    for n in (2, 3):
        bounds = certify_comparator(n)
        row, gram_error, oracle_error = compare_amplitudes(n)
        for value, b in zip(row, bounds, strict=True):
            check(
                float(b.lo) - TOL <= value <= float(b.hi) + TOL,
                "oracle/interval disagreement",
            )
        error, margin = replay_escape(n, row, bounds)
        white_threshold = (1 / 6**n - row[0]) / (1 / (1 << n) - row[0])
        expected = 1 - 2 * sqrt(2) / 3 if n == 2 else 1 / 27
        threshold_exact = "1-2*sqrt(2)/3" if n == 2 else "1/27"
        check(abs(white_threshold - expected) < TOL, "white output-noise threshold")
        print(f"n={n} offset row: {', '.join(f'{p:.12f}' for p in row)}")
        print(
            f"  diagonal {row[0]:.12f} < {F(1, 6**n)}; "
            f"white-noise threshold {threshold_exact} (~{white_threshold:.12f})"
        )
        print(
            f"  complex Gram error {gram_error:.3g}; all-row oracle error {oracle_error:.3g}"
        )
        print(
            f"  correlated all-row replay error {error:.3g}; "
            f"nonzero-offset residual >= {lower_decimal(margin)}"
        )
        if n == 3:
            parity = cyclic_control(bounds)
            print(
                "  cyclic also reaches zero, but full input parity is absent "
                f"(target >= {lower_decimal(parity.lo)})"
            )
    print(f"Replay tolerance {TOL:g}; no physical or general composition claim.")


if __name__ == "__main__":
    main()
