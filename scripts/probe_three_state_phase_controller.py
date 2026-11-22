"""A deterministic, approximate three-state escape from a two-state wall.

SUPPLIED resources: six coherent data species C3 x C2, a neutral tensor
controller initialized in |0>, the usual complex norm/topology, arbitrarily
long finite words, common ancillary T and local i on three logical levels,
and SELECT(h): translate the data by h iff the controller is in level 2.
No measurement, acceptance branch, reset or irrational initial state occurs.
SELECT is a permutation in packet coordinates; Fourier characters below
are an analysis basis, NOT an available irrational Fourier gate. All data
translations commute with complement. The output phase choice is programmed,
not selected by charge conservation.

Common logical T uses two matched physical mixers on paired rails, and local
i uses one within-pair mixer (gaussian_dyadic_words.py). Acting identically
over six data addresses therefore requires synchronized copies, identity
bypass and a common phase/clock convention. SELECT needs coherent JOINT
configuration addressing, not independent additive pilot amplitudes. Neutral
tensor structure, preparation, addressing and this synchronization are not
derived, nor are a detector law, spacetime or local gauge dynamics.

DENSITY PREMISE, kept separate from the exact checks. The existing
probe_native_mixer_sector_density.py gives an irrational native circle and
its nonparallel conjugate, hence SU(2) on the centered three-port plane in
the closed group. Here local i_0 conjugates that su(2) to another plane;
exact generator ranks 3, 6, 8 supply the small extension to su(3). The
closed-subgroup/Lie argument then gives common SU(3) in closure. The scalar
Lean theorem NativeGaussianDyadicDensity is NOT a fixed-size unitary-density
proof, and finite ranks alone are not that proof. No continuous rotation is
an elementary instruction. A common target rotation can instead be compiled
by exhaustive native-word search with certified approximation tests; density
ensures termination, but no word-length/running-time bound is provided here.

CHARACTER SEPARATION. Write chi=(a,b), h=(r,s), chi(h)=omega**(a*r)*(-1)**(b*s).
In character chi, SELECT(h) is D_h=diag(1,1,chi(h)). Put
A=E02-E20, B=i(E02+E20), A_h=Ad(D_h)A, B_h=Ad(D_h)B.
For any character alpha, (1/6) sum_h [Re(alpha(h)) A_h +
Im(alpha(h)) B_h] equals A in block alpha and zero in the other five.
The analogous coefficients (-Im,Re) isolate B. Brackets with common E12
couplings give all eight su(3) directions in each block: independent SU(3)^6
lies in closure. Thus any six phases can act on |0>, compensated on unused
controller levels. Approximate return is uniform on unknown/entangled data:
the joint operator-norm error is the maximum block error, also after tensoring
an arbitrary reference. This is not an exact reusable catalyst statement.

FINITE COMPILED ERROR SCHEDULE. For sector
weights q=(0 on uniform, -2 on b=1, +3 on a!=0,b=0), the Fourier coefficients
are c=(0,2,-1/2,-1/2,-1/2,-1/2), all real. Native T02 A T02^dagger is
i(E00-E22). Therefore T02 [product_{h=1..5}
D_h exp(t*c_h*A/r) D_h^dagger]^r T02^dagger approximates the requested
z^-2/z^3 phase, z=exp(i*t), with |0> returned. For skew-Hermitian terms,
Duhamel plus unitary telescoping bounds first-order product error by
(1/(2r))*sum_{j<k} ||[t*c_j*A_j,t*c_k*A_k]|| <= 11*t^2/(2r).
At t=1/8, r=128, compiling each of 640 common rotations to eta=2^-22 gives
total error <= 27/32768 < 1/1000. There are only TWO distinct common target
rotations and 1280 SELECT queries; the native outer conjugations are exact.
For each tiny-angle target, an explicit six-integer unit-vector certificate
at denominator 2^52 gives a dyadic Householder product H_v H_e0. Rational
Taylor intervals bound v's distance to (cos(theta/2),0,-sin(theta/2));
||H_v-H_w|| <= 4||v-w|| certifies the required error. The existing exact
compiler produces 952- and 924-move T/i words, both exactly replayed here.
The full schedule has 594948 common logical moves plus the SELECT queries.
It is specified by these two compiled words and repetitions, not by a costly
matrix multiplication of the expanded schedule. Its certificate needs no
unperformed common compilation or density inference for this one target.
The same bound applies to every normalized input and its purifications;
controller leakage amplitude is <= this bound (probability needs readout).

CONTROLS. Two levels are not globally Clifford: order-three character blocks
see non-Clifford SELECT phases. However the trivial and parity characters
see only I/Z, and common two-level T,i generate exactly 96 matrices (24
projectively). Their closure is finite, obstructing generic relative phases.
For the same t=1/8 target, nonreturning columns leak norm >=1/sqrt(2), while
returning phases lie in mu4. Comparing the trivial/parity columns bounds the
uniform error below by sin(1/4)/2 >= 95/768, even allowing a common global
phase: two column errors epsilon can change their relative phase by <=2epsilon.
Adding the FIXED non-dyadic phase (3+4i)/5 to a two-level controller is another
escape: its irrational circle and a native conjugate contain SU(2), and the
same Fourier argument works. This imports a discrete non-Clifford resource.
Two parity SELECT queries with T02 and its inverse already give an exact
conditional -i swap, but not a continuous control. An ensuing local-phase
commutator returns |0> with minus-sector phase -i, an exact off-weight-circle
central operation. Swap/SELECT/swap also returns |0> with an exact noncentral
data translation. Neither is forbidden by the following narrower wall.

EXACT RETURN WALL. A finite T,i/permutation word has Gaussian-dyadic entries;
with this coordinate seed and exact uncorrelated return its effective data
matrix does too. A unit Gaussian-dyadic scalar is in mu4 (clear powers of 2
and descend the two-squares equation). For scalar minus/centered-plus phases
(a,b), fixing the uniform reference, (1-b)/3 must also be dyadic; b=1 is
the only unit option. The weight relation a^3 b^2=1 then forces a=b=z=1.
This does NOT prohibit exact noncentral sector operations, off-circle central
ones, another initial-state contract, or arbitrarily accurate approximate
return. No full QM or physical charge claim follows.

Run: python3 -B -O -m scripts.probe_three_state_phase_controller
"""

from __future__ import annotations

import sys
from collections import deque
from collections.abc import Iterator
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    Move,
    apply,
    eye,
    g,
    run,
    synthesize,
    unitary,
)
from scripts.probe_native_mixer_sector_density import (
    bracket as integer_bracket,
)
from scripts.probe_native_mixer_sector_density import (
    check_three_port_axes,
    flatten,
    realify,
    triple_couplings,
)
from scripts.probe_packet_phase_program import from_phases, translate
from scripts.probe_raw_gate_reconstruction import mul, rank, tr


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


@dataclass(frozen=True)
class Cyclo:
    """Exact Q(i,omega), omega^2+omega+1=0; no numerical roots."""

    a: Gaussian = ZERO
    b: Gaussian = ZERO

    def __add__(self, other: Cyclo) -> Cyclo:
        return Cyclo(self.a + other.a, self.b + other.b)

    def __sub__(self, other: Cyclo) -> Cyclo:
        return Cyclo(self.a - other.a, self.b - other.b)

    def __mul__(self, other: Cyclo) -> Cyclo:
        return Cyclo(
            self.a * other.a - self.b * other.b,
            self.a * other.b + self.b * other.a - self.b * other.b,
        )

    def star(self) -> Cyclo:
        return Cyclo(self.a.star() - self.b.star(), ZERO - self.b.star())

    def real(self) -> Cyclo:
        return Cyclo(g(F(1, 2))) * (self + self.star())

    def imag(self) -> Cyclo:
        return Cyclo(g(0, -F(1, 2))) * (self - self.star())


C0, C1, CI, W = Cyclo(), Cyclo(ONE), Cyclo(I), Cyclo(ZERO, ONE)
CM = tuple[tuple[Cyclo, ...], ...]
Word = tuple[Move, ...]
LABELS = tuple(product(range(3), range(2)))
COMPILATION_ERROR = F(1, 2**22)


def cm(a: Matrix) -> CM:
    return tuple(tuple(Cyclo(x) for x in row) for row in a)


def add(a: CM, b: CM) -> CM:
    return tuple(
        tuple(x + y for x, y in zip(r, s, strict=True))
        for r, s in zip(a, b, strict=True)
    )


def scale(z: Cyclo, a: CM) -> CM:
    return tuple(tuple(z * x for x in row) for row in a)


def mm(a: CM, b: CM) -> CM:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), C0)
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def dagger(a: CM) -> CM:
    return tuple(tuple(x.star() for x in col) for col in zip(*a, strict=True))


def comm(a: CM, b: CM) -> CM:
    return add(mm(a, b), scale(Cyclo(g(-1)), mm(b, a)))


def conjugate(u: CM, a: CM) -> CM:
    return mm(u, mm(a, dagger(u)))


def diagonal(values: tuple[Cyclo, ...]) -> CM:
    return tuple(
        tuple(v if i == j else C0 for j in range(len(values)))
        for i, v in enumerate(values)
    )


def coupling(i: int, j: int, imaginary: bool = False) -> CM:
    return tuple(
        tuple(
            (CI if imaginary else C1)
            if (r, s) == (i, j)
            else (CI if imaginary else Cyclo(g(-1)))
            if (r, s) == (j, i)
            else C0
            for s in range(3)
        )
        for r in range(3)
    )


def character(alpha: tuple[int, int], h: tuple[int, int]) -> Cyclo:
    a, b = alpha
    r, s = h
    value = (C1, W, W * W)[a * r % 3]
    return value if b * s % 2 == 0 else Cyclo(g(-1)) * value


def selector(alpha: tuple[int, int], h: tuple[int, int]) -> CM:
    return diagonal((C1, C1, character(alpha, h)))


def rational_row(a: CM) -> tuple[int, ...]:
    values = tuple(
        v for row in a for z in row for v in (z.a.re, z.a.im, z.b.re, z.b.im)
    )
    need(all(v.denominator == 1 for v in values), "expected integral Lie control")
    return tuple(int(v) for v in values)


def common_density_extension() -> tuple[int, int, int]:
    # Reuse the existing native-circle finite certificate, not a duplicate.
    check_three_port_axes()
    phase = realify(
        ((0, 0, 0), (0, 1, 0), (0, 0, 1)), ((1, 0, 0), (0, 0, 0), (0, 0, 0))
    )
    initial = triple_couplings(3, 2)
    enlarged = initial + tuple(mul(phase, mul(x, tr(phase))) for x in initial)
    closed = enlarged + tuple(
        integer_bracket(x, y) for x, y in combinations(enlarged, 2)
    )
    result = tuple(rank(map(flatten, rows)) for rows in (initial, enlarged, closed))
    need(result == (3, 6, 8), "common logical su(3) extension")
    return result[0], result[1], result[2]


def fourier_controls() -> int:
    need(W * W + W + C1 == C0 and W.star() * W == C1, "cyclotomic arithmetic")
    a, b, zero = (
        coupling(0, 2),
        coupling(0, 2, True),
        cm(tuple((ZERO,) * 3 for _ in range(3))),
    )
    count = 0
    for target, block in product(LABELS, repeat=2):
        sa, sb = zero, zero
        for h in LABELS:
            c = character(target, h)
            ah, bh = (conjugate(selector(block, h), x) for x in (a, b))
            sa = add(sa, add(scale(c.real(), ah), scale(c.imag(), bh)))
            sb = add(sb, add(scale(Cyclo(g(-1)) * c.imag(), ah), scale(c.real(), bh)))
        need(
            scale(Cyclo(g(F(1, 6))), sa) == (a if block == target else zero),
            "A isolation",
        )
        need(
            scale(Cyclo(g(F(1, 6))), sb) == (b if block == target else zero),
            "B isolation",
        )
        count += 2
    # Every bracket has an isolated factor, so its other five blocks stay zero.
    a01, b01 = comm(a, coupling(1, 2)), comm(b, coupling(1, 2))
    isolated = (a, b, a01, b01, comm(a01, a), comm(a01, b), comm(a, b), comm(a01, b01))
    need(rank(map(rational_row, isolated)) == 8, "eight isolated su(3) directions")
    return count


def compiled_rotations() -> tuple[Word, Word]:
    """Replay two finite native words; bound errors by exact rational intervals."""
    denominator = 2**52
    certificates = (
        (F(1, 512), 4503597479887018, 4398045812053, (1, 33, 77485743, 1983088)),
        (F(-1, 2048), 4503599493152768, 1099511616853, (3, 61, 77088343, 7932198)),
    )
    words: list[Word] = []
    for theta, cosine, sine, extras in certificates:
        x = abs(theta) / 2
        need(0 < x < 1, "alternating Taylor interval domain")
        cosine_lo = sum(
            ((-1) ** j * x ** (2 * j) / factorial(2 * j) for j in range(4)), F(0)
        )
        sine_lo = sum(
            ((-1) ** j * x ** (2 * j + 1) / factorial(2 * j + 1) for j in range(4)),
            F(0),
        )
        cosine_hi, sine_hi = (
            cosine_lo + x**8 / factorial(8),
            sine_lo + x**9 / factorial(9),
        )
        need(
            cosine <= denominator * cosine_lo <= denominator * cosine_hi < cosine + 1,
            "certified cosine floor",
        )
        need(
            sine <= denominator * sine_lo <= denominator * sine_hi < sine + 1,
            "certified sine floor",
        )
        residual = denominator**2 - cosine**2 - sine**2
        need(
            sum(k * k for k in extras) == residual, "four-square completion certificate"
        )
        # Two floored real coordinates err by <1/D; the other four complete
        # the exact unit vector. No irrational vector is physically prepared.
        distance2_bound = F(residual + 2, denominator**2)
        need(16 * distance2_bound <= COMPILATION_ERROR**2, "Householder operator error")
        c, d, e, f = extras
        v = (
            g(F(cosine, denominator), F(c, denominator)),
            g(F(d, denominator), F(e, denominator)),
            g(F(-sine if theta > 0 else sine, denominator), F(f, denominator)),
        )
        need(sum((z.norm2() for z in v), F(0)) == 1, "exact normalized dyadic vector")
        target = tuple(
            tuple(
                g(-1 if j == 0 else 1)
                * ((ONE if i == j else ZERO) - g(2) * v[i] * v[j].star())
                for j in range(3)
            )
            for i in range(3)
        )
        need(unitary(target), "dyadic Householder product")
        word = synthesize(target)
        need(run(eye(3), word) == target, "exact replay of compiled common rotation")
        words.append(word)
    need(tuple(map(len, words)) == (952, 924), "frozen common-word resource counts")
    return words[0], words[1]


def compiled_schedule(words: tuple[Word, Word]) -> Iterator[tuple[str, int, int]]:
    """Chronological instructions; SELECT always controls on ancillary level 2."""
    for _ in range(3):
        yield ("T", 0, 2)
    for _ in range(128):
        for j, (r, s) in enumerate(LABELS[1:]):
            yield ("SELECT", -r % 3, s)
            yield from words[0 if j == 0 else 1]
            yield ("SELECT", r, s)
    yield ("T", 0, 2)


def finite_error_schedule(words: tuple[Word, Word]) -> tuple[F, int, int, int]:
    weights = tuple(-2 if b else 3 if a else 0 for a, b in LABELS)
    coefficients = (F(0), F(2), F(-1, 2), F(-1, 2), F(-1, 2), F(-1, 2))
    for h, expected in zip(LABELS, coefficients, strict=True):
        value = sum(
            (
                Cyclo(g(F(q, 6))) * character(alpha, h)
                for alpha, q in zip(LABELS, weights, strict=True)
            ),
            C0,
        )
        need(value == Cyclo(g(expected)), "five-factor Fourier profile")
    t02 = cm(run(eye(3), (("T", 0, 2),)))
    need(cm(run(eye(3), (("T", 0, 2),) * 3)) == dagger(t02), "compiled native inverse")
    need(
        conjugate(t02, coupling(0, 2)) == diagonal((CI, C0, Cyclo(g(0, -1)))),
        "native outer conjugation turns A into the phase generator",
    )
    t, repetitions, eta = F(1, 8), 128, COMPILATION_ERROR
    nonzero = coefficients[1:]
    need(
        (t * nonzero[0] / repetitions, t * nonzero[1] / repetitions)
        == (F(1, 512), F(-1, 2048)),
        "compiled angles match the schedule",
    )
    pair_sum = sum((abs(x * y) for x, y in combinations(nonzero, 2)), F(0))
    need(pair_sum == F(11, 2), "commutator error budget")
    common_count = len(nonzero) * repetitions
    error = t * t * pair_sum / repetitions + common_count * eta
    need(error == F(27, 32768) < F(1, 1000), "uniform approximation budget")
    need(2 * t - (2 * t) ** 3 / 6 > error, "identity cannot pass this target budget")
    # T02^dagger is three native Ts; the final T02 adds one more.
    logical_moves = repetitions * (len(words[0]) + 4 * len(words[1])) + 4
    need(logical_moves == 594948, "expanded finite schedule length")
    counts = {"T": 0, "i": 0, "SELECT": 0}
    for kind, i, j in compiled_schedule(words):
        need(0 <= i < 3 and 0 <= j < (2 if kind == "SELECT" else 3), "schedule address")
        counts[kind] += 1
    need(counts == {"T": 397316, "i": 197632, "SELECT": 1280}, "instruction census")
    return error, common_count, 2 * common_count, logical_moves


def finite_clifford_control() -> tuple[int, int, F]:
    moves: tuple[Move, ...] = (("T", 0, 1), ("i", 0, 0), ("i", 1, 1))
    seen, pending = {eye(2)}, deque([eye(2)])
    while pending:
        matrix = pending.popleft()
        for move in moves:
            candidate = apply(matrix, move)
            if candidate not in seen:
                seen.add(candidate)
                pending.append(candidate)
        need(len(seen) <= 96, "two-level finite-group control")
    projective = set()
    returns = set()
    for matrix in seen:
        first = next(x for row in matrix for x in row if x != ZERO)
        inverse = g(1 / first.norm2()) * first.star()
        projective.add(tuple(tuple(inverse * x for x in row) for row in matrix))
        if matrix[1][0] == ZERO:
            returns.add(matrix[0][0])
        else:
            need(matrix[1][0].norm2() >= F(1, 2), "nonreturning Clifford leakage")
    need((len(seen), len(projective)) == (96, 24), "Clifford census")
    need(returns == {ONE, I, g(-1), g(0, -1)}, "coordinate-return phases")
    for alpha in ((0, 0), (0, 1)):
        need({character(alpha, h) for h in LABELS} <= {C1, Cyclo(g(-1))}, "I/Z block")
    need(character((1, 0), (1, 0)) == W, "do not call all character blocks Clifford")
    angle = F(1, 4)
    lower = (angle - angle**3 / 6) / 2
    need(lower == F(95, 768) > F(27, 32768), "robust two-state separation")
    return len(seen), len(projective), lower


def exact_return_controls() -> None:
    t, p = cm(run(eye(3), (("T", 0, 2),))), cm(run(eye(3), (("i", 0, 0),)))
    for alpha in LABELS:
        d = selector(alpha, (0, 1))
        echo = mm(conjugate(t, d), d)
        expected = (
            cm(eye(3))
            if alpha[1] == 0
            else ((C0, C0, Cyclo(g(0, -1))), (C0, C1, C0), (Cyclo(g(0, -1)), C0, C0))
        )
        need(echo == expected, "two-query exact conditional -i swap")
        returned = mm(conjugate(dagger(echo), p), dagger(p))
        phase = C1 if alpha[1] == 0 else Cyclo(g(0, -1))
        need(
            tuple(row[0] for row in returned) == (phase, C0, C0),
            "off-circle exact return",
        )
    # Swap 0<->2, SELECT(1,0), swap back: unknown data translated, controller 0.
    for (r, s), x in product(LABELS, range(6)):
        h, inverse = 2 * r + s, 2 * (-r % 3) + s
        need(translate(h, x ^ 1) == (translate(h, x) ^ 1), "complement conservation")
        need(translate(inverse, translate(h, x)) == x, "compiled SELECT inverse")
    need(translate(2, 0) != 0, "exact return must not forbid noncentral actions")
    units = (ONE, I, g(-1), g(0, -1))
    exact_central = [
        (a, b)
        for a, b in product(units, repeat=2)
        if all(v.dyadic() for row in from_phases(a, b) for v in row)
    ]
    need(
        exact_central == [(a, ONE) for a in units], "uniform-reference denominator wall"
    )
    need(
        [(a, b) for a, b in exact_central if a * a * a * b * b == ONE] == [(ONE, ONE)],
        "only identity on the specified exact weight circle",
    )


def missing_resource_controls() -> None:
    # Which characters can each restricted SELECT vocabulary distinguish?
    vocabularies = (((0, 0),), ((0, 0), (0, 1)), ((0, 0), (1, 0), (2, 0)), LABELS)
    classes = tuple(
        len({tuple(character(a, h) for h in vocabulary) for a in LABELS})
        for vocabulary in vocabularies
    )
    need(classes == (1, 2, 3, 6), "missing translations leave unresolved characters")
    z = g(F(3, 5), F(4, 5))
    need(
        z.norm2() == 1 and not z.dyadic() and (z + z.star()).re == F(6, 5),
        "fixed non-Clifford import has infinite order by algebraic integrality",
    )
    native = cm(run(eye(2), (("T", 0, 1),)))
    # Twice the actual circle generator clears the conjugation denominators.
    axis = diagonal((C0, Cyclo(g(0, 2))))
    rotated = conjugate(native, axis)
    need(
        rank(
            map(
                rational_row,
                (axis, rotated, comm(axis, rotated), comm(axis, comm(axis, rotated))),
            )
        )
        == 4,
        "actual imported circle and native conjugate span u(2), without dropping their trace",
    )


def main() -> None:
    ranks = common_density_extension()
    identities = fourier_controls()
    words = compiled_rotations()
    error, common, queries, logical_moves = finite_error_schedule(words)
    clifford = finite_clifford_control()
    exact_return_controls()
    missing_resource_controls()
    print(
        f"Common native density extension ranks {ranks}; {identities} exact Fourier identities; six independent su(3) blocks in closure."
    )
    print(
        f"Certified schedule: t=1/8, r=128; {common} common approximants at error <=2^-22, {queries} SELECT queries; uniform joint error <= {error} < 1/1000."
    )
    print(
        f"Two exact dyadic common approximants compiled/replayed in {tuple(map(len, words))} native moves; expanded schedule {logical_moves} common logical moves plus SELECT."
    )
    print(
        "This one finite error certificate does not need density. General arbitrary-phase closure still uses the separate Lie/topology argument, not a continuous primitive or a Lean proof."
    )
    print(
        f"Two-state trivial/parity blocks: {clifford[0]} exact matrices / {clifford[1]} projective classes; other character blocks need not be Clifford."
    )
    print(
        f"Same target with two states: uniform error >= {clifford[2]}, even modulo one common global phase."
    )
    print(
        "Exact conditional swap, off-circle central phase and noncentral returning translation survive; only z=1 survives the specified exact dyadic weight-circle wall."
    )
    print(
        "Three neutral states or an imported fixed non-Clifford phase suffice conditionally; coherent tensor control, synchronization and norm remain supplied. No measurement or physical-charge claim."
    )


if __name__ == "__main__":
    main()
