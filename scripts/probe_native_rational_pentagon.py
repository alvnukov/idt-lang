"""Exact projector-instrument hit versus three-slot unitary and prime-5 walls.

This is a conditional finite probe, not a derivation of a measurement law.
The supplied model has normalized complex amplitudes, sharp projective
readout with probabilities psi*P*psi, coherent outcome/data product addresses,
blank ancillas, ancilla-only readout, and exact neutral-failure reset/retry.
The native logical T/i instructions and their paired-rail interpretation are
those in gaussian_dyadic_words.py. Initial encoded rails, grouped readout,
record retention, and ideal feedback are apparatus assumptions. All native
words checked here are compiled; no independent Hadamard is imported.

UNITARY WALL. For B over Q(i), B*B=m I in three slots implies
Norm(det B)=m^3. Every inert prime (3 mod 4) therefore has even valuation
in m, so m is itself a Q(i)-norm. If B's first column is c*(1,1,1), then
m=3*Norm(c), a contradiction. This excludes even projectively Q(i) exact
unitaries taking an axis to that ray, hence the exact ideal native RUS
unitary class of probe_projective_repeat_classification.py. It does not
exclude the rational projector vv*/3, or the rational reflection I-2vv*/3.

INSTRUMENT HIT. Orthogonal rational projectors summing to I can be stacked
as D*P_j, with common integral denominator D. Their squared column norm is
D^2. Pad to 2^k using scalar identity failure blocks and divide by pi^k,
pi=1+i. Exact dyadic isometry synthesis supplies a native word. Success
has probability D^2/2^k independent of data; each failure is scalar I,
including on inputs entangled with a reference. Repetition gives the sharp
projector instrument almost surely, with finite mean but no bounded worst
case. This uses additional ancilla addresses, NOT a lossless raw qutrit
unitary. Recording the data rail as well as the ancilla would break it.

PENTAGON. The directions e1,e2,(1,0,1),(-1,-1,1),(0,1,1) have consecutive
orthogonal pairs. The supplied native state (1,1,0)/pi gives sum 13/6>2.
Each adjacent pair has its complete three-outcome context checked below.
Although only one listed pentagon ray has non-dyadic normalization, two
auxiliary context rays have norm 6. A context-independent deterministic
assignment to these sharp events has at most two yes values. Thus this is
a state-dependent noncontextual-probability witness, not an uncolourable
Kochen-Specker set, and not an empirical test. Identity of the shared sharp
event across contexts is an explicit premise. Repeatability is checked.

Finite cutoffs retain an abort flag. In this supplied model heralding is
data-independent; unmodelled detector loss need not be. The common-D=6
construction has p=9/16 in every context and tail (7/16)^N. The numerical
loss boundary eta>12/13 below assumes uniform independent thinning and
counts missing yes events as zero; it does NOT establish a fair-sampling
assumption or outcome determinism for arbitrary unsharp POVMs.

PRIME-5 QUESTION. Let R5=Z[i,1/2,1/5]. A primitive Gaussian-integer ray
has an R5 unit representative iff its norm is 2,5-smooth: Gaussian Bezout
forces its normalizing scalar into R5, and both 2 and 5 are Gaussian norms.
Any pentagon with a complete first edge can be transformed to e1,e2, then
has outer rays (a,0,b),(0,c,d) and middle ray proportional to
(-conj(b*c),-conj(a*d),conj(a*c)). For primitive outer pairs, the middle
coordinates have gcd conj(gcd(a,c)), up to a unit. The optional exact scan
therefore tests a necessary ray condition, not generation by one z gate.
Independent coordinate phases in {1,i,-1,-i} do not affect that condition.

The entire symmetric family c=a,d=b is excluded, not just the scan range.
Put A=Norm(a), B=Norm(b), N=A+B=2^epsilon*5^k, M=A+2B, with epsilon<=1
by primitive-pair parity and N<M<2N. If epsilon=1, A,B are odd and M=3
mod 4, impossible for a 2,5-smooth odd integer. Otherwise N=5^k. If A
is odd, B even, then M=5^s cannot lie between N and 2N. If A is even,
B odd, then 4|M would give the Gaussian norm B=M-N=3 mod 4, impossible;
M=2*5^s cannot lie in that interval either. The arbitrary asymmetric
prime-5-only problem, and reachability from just z=(3+4i)/5, remain OPEN
here. A two-prime (5 and 17) algebraic comparator prevents overextension.
Gaussian factorization gives every norm-one scalar in R5 as i^j*z^n:
the 2+i and 2-i exponents must be opposite, and the pi exponent zero.
The checked sandwich T diag(z,1) adjoint(T) gives [[2,-1],[1,2]]/(2-i).
Thus this added phase does supply exact
norm-5 two-mode mixing; it is not itself a qutrit contextuality witness.

General arguments in this docstring are mathematical arguments, not Lean
proofs. Default checks are bounded and exact, with no fits or float tests.
Run: python3 -B -O -m scripts.probe_native_rational_pentagon
Optional larger scan: add --prime5-exponent 5 (pair norm <= 6250).
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import isqrt, lcm
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    ONE,
    PI,
    ZERO,
    Gaussian,
    Matrix,
    Move,
    eye,
    g,
    isometry,
    run,
    synthesize_isometry,
)
from scripts.probe_exact_charge_sector_wall import four_squares

Ray = tuple[Gaussian, Gaussian, Gaussian]
GI = tuple[int, int]
Pair = tuple[GI, GI]


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def divide(a: Gaussian, b: Gaussian) -> Gaussian:
    z = a * b.star()
    return g(z.re / b.norm2(), z.im / b.norm2())


def adjoint(a: Matrix) -> Matrix:
    return tuple(tuple(row[j].star() for row in a) for j in range(len(a[0])))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * b[k][j] for k, x in enumerate(row)), ZERO)
            for j in range(len(b[0]))
        )
        for row in a
    )


def scale(a: Matrix, z: Gaussian) -> Matrix:
    return tuple(tuple(z * x for x in row) for row in a)


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(x + y for x, y in zip(row, other, strict=True))
        for row, other in zip(a, b, strict=True)
    )


def projector(v: Ray) -> Matrix:
    n = sum((z.norm2() for z in v), F(0))
    need(n > 0, "zero ray")
    return tuple(tuple(g(1 / n) * x * y.star() for y in v) for x in v)


def cross(v: Ray, w: Ray) -> Ray:
    return (
        (v[1] * w[2] - v[2] * w[1]).star(),
        (v[2] * w[0] - v[0] * w[2]).star(),
        (v[0] * w[1] - v[1] * w[0]).star(),
    )


def norm(v: Ray) -> F:
    return sum((z.norm2() for z in v), F(0))


def probability(p: Matrix, psi: Ray) -> F:
    col = tuple((z,) for z in psi)
    value = multiply(multiply(adjoint(col), p), col)[0][0]
    need(value.im == 0 and 0 <= value.re <= 1, "invalid probability")
    return value.re


def frame(v: Ray, w: Ray) -> tuple[Matrix, ...]:
    need(sum((x.star() * y for x, y in zip(v, w, strict=True)), ZERO) == ZERO, "edge")
    ps = (projector(v), projector(w), projector(cross(v, w)))
    zero = scale(eye(3), ZERO)
    need(add(add(ps[0], ps[1]), ps[2]) == eye(3), "incomplete context")
    for j, k in product(range(3), repeat=2):
        need(multiply(ps[j], ps[k]) == (ps[j] if j == k else zero), "sharp context")
    return ps


@dataclass(frozen=True)
class Retry:
    columns: Matrix
    success: F
    failures: tuple[Gaussian, ...]
    word: tuple[Move, ...]

    @property
    def physical_mixers(self) -> int:
        return sum(2 if tag == "T" else 1 for tag, _, _ in self.word)


def retry(blocks: tuple[Matrix, ...], denominator: int | None = None) -> Retry:
    """Compile sharp-projector blocks, or a single already-unitary block."""
    need(bool(blocks), "empty instrument")
    d = len(blocks[0])
    total = scale(eye(d), ZERO)
    for block in blocks:
        need(len(block) == d and all(len(row) == d for row in block), "block shape")
        total = add(total, multiply(adjoint(block), block))
    need(total == eye(d), "instrument completeness")
    natural = lcm(
        *(
            q
            for block in blocks
            for row in block
            for z in row
            for q in (z.re.denominator, z.im.denominator)
        )
    )
    denominator = natural if denominator is None else denominator
    need(denominator > 0 and denominator % natural == 0, "nonintegral presentation")
    m = denominator**2
    k = (m - 1).bit_length()
    a, b, c, d0 = four_squares((1 << k) - m)
    den = ONE
    for _ in range(k):
        den = den * PI
    coefficient = divide(g(denominator), den)
    failures = tuple(divide(z, den) for z in (g(a, b), g(c, d0)) if z != ZERO)
    grouped = tuple(scale(block, coefficient) for block in blocks) + tuple(
        scale(eye(d), z) for z in failures
    )
    columns = tuple(row for block in grouped for row in block)
    need(isometry(columns), "padded columns not isometric")
    word = synthesize_isometry(columns)
    seed = tuple(row[:d] for row in eye(len(columns)))
    need(run(seed, word) == columns, "native word mismatch")
    p = F(m, 1 << k)
    need(
        coefficient.norm2() == p and p + sum(z.norm2() for z in failures) == 1,
        "retry law",
    )
    for index, z in enumerate(failures, start=len(blocks)):
        block = columns[index * d : (index + 1) * d]
        need(block == scale(eye(d), z), "informative or disturbing failure")
        # Reset only the recorded ancilla label; preserve arbitrary data coherence.
        reset: tuple[Move, ...] = tuple(
            ("T", j, index * d + j) for j in range(d) for _ in range(2)
        )
        branch = tuple(row[:d] for row in scale(eye(len(columns)), ZERO))
        branch = branch[: index * d] + block + branch[(index + 1) * d :]
        reset_branch = run(branch, reset)
        need(reset_branch[:d] == scale(eye(d), z), "failure reset altered data")
        need(
            all(x == ZERO for row in reset_branch[d:] for x in row),
            "reset leaked branch",
        )
    return Retry(columns, p, failures, word)


def gaussian_norm_integer(n: int) -> bool:
    """Positive integer is a Q(i)-norm iff every 3-mod-4 prime exponent is even."""
    need(n > 0, "positive norm required")
    prime = 2
    while prime * prime <= n:
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if prime % 4 == 3 and exponent % 2:
            return False
        prime += 1
    return n % 4 != 3


def gn(z: GI) -> int:
    return z[0] ** 2 + z[1] ** 2


def gm(z: GI, w: GI) -> GI:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def gc(z: GI) -> GI:
    return z[0], -z[1]


def phase_class(z: GI) -> GI:
    x, y = z
    return min((x, y), (-y, x), (-x, -y), (y, -x))


@cache
def gcd_gaussian(z: GI, w: GI) -> GI:
    while w != (0, 0):
        n = gn(w)
        r = gm(z, gc(w))
        q = ((2 * r[0] + n) // (2 * n), (2 * r[1] + n) // (2 * n))
        qw = gm(q, w)
        z, w = w, (z[0] - qw[0], z[1] - qw[1])
    return phase_class(z)


def gd(z: GI, w: GI) -> GI:
    r, n = gm(z, gc(w)), gn(w)
    need(r[0] % n == 0 and r[1] % n == 0, "nonintegral Gaussian division")
    return r[0] // n, r[1] // n


def smooth25(n: int) -> bool:
    need(n > 0, "positive smoothness input")
    for prime in (2, 5):
        while n % prime == 0:
            n //= prime
    return n == 1


def pair_classes(exponent: int) -> tuple[Pair, ...]:
    pairs: set[Pair] = set()
    for power in range(exponent + 1):
        for n in (5**power, 2 * 5**power):
            bynorm: dict[int, set[GI]] = {}
            for x, y in product(range(-isqrt(n), isqrt(n) + 1), repeat=2):
                s = x * x + y * y
                if s <= n:
                    bynorm.setdefault(s, set()).add(phase_class((x, y)))
            for s, zs in bynorm.items():
                if not s or s == n:
                    continue
                for z, w in product(zs, bynorm.get(n - s, set())):
                    common = gcd_gaussian(z, w)
                    pairs.add((phase_class(gd(z, common)), phase_class(gd(w, common))))
    return tuple(sorted(pairs))


def middle_norm(first: Pair, second: Pair) -> int:
    a, b = first
    c, d = second
    raw = gn(b) * gn(c) + gn(a) * gn(d) + gn(a) * gn(c)
    divisor = gn(gcd_gaussian(a, c))
    need(raw % divisor == 0, "cross-gcd norm divisor")
    return raw // divisor


def scan_prime5(exponent: int) -> tuple[int, int, int]:
    pairs = pair_classes(exponent)
    hits = 0
    for index, first in enumerate(pairs):
        need(not smooth25(middle_norm(first, first)), "symmetric-family wall failed")
        for second in pairs[index:]:
            hits += smooth25(middle_norm(first, second))
    return len(pairs), len(pairs) * (len(pairs) + 1) // 2, hits


def phase5_controls() -> None:
    z = g(F(3, 5), F(4, 5))
    t = run(eye(2), (("T", 0, 1),))
    sandwich = multiply(multiply(t, ((z, ZERO), (ZERO, ONE))), adjoint(t))
    expected = tuple(
        tuple(divide(g(x), g(2, -1)) for x in row) for row in ((2, -1), (1, 2))
    )
    need(sandwich == expected and isometry(sandwich), "single-phase norm-5 mixer")
    need(z.norm2() == 1 and not z.dyadic(), "phase-5 resource boundary")
    power = ONE
    for _ in range(7):
        need(power.norm2() == 1, "circle phase norm")
        for coordinate in (power.re, power.im):
            rest = coordinate.denominator
            while rest % 5 == 0:
                rest //= 5
            need(rest == 1, "unexpected circle denominator")
        power = power * z


def controls() -> tuple[tuple[F, ...], tuple[int, ...]]:
    psi: Ray = (divide(ONE, PI), divide(ONE, PI), ZERO)
    seed = tuple((z,) for z in psi)
    word = synthesize_isometry(seed)
    need(run(tuple(row[:1] for row in eye(3)), word) == seed, "native preparation")
    need(norm(psi) == 1, "state normalization")
    rays: tuple[Ray, ...] = (
        (ONE, ZERO, ZERO),
        (ZERO, ONE, ZERO),
        (ONE, ZERO, ONE),
        (g(-1), g(-1), ONE),
        (ZERO, ONE, ONE),
    )
    probs = tuple(probability(projector(v), psi) for v in rays)
    need(
        probs == (F(1, 2), F(1, 2), F(1, 4), F(2, 3), F(1, 4)), "pentagon probabilities"
    )
    need(sum(probs) == F(13, 6), "pentagon sum")
    assignments = [
        bits
        for bits in product((0, 1), repeat=5)
        if all(bits[j] + bits[(j + 1) % 5] <= 1 for j in range(5))
    ]
    need(
        len(assignments) == 11 and max(map(sum, assignments)) == 2,
        "noncontextual bound",
    )
    costs: list[int] = []
    complements: list[F] = []
    for index, v in enumerate(rays):
        w = rays[(index + 1) % 5]
        ps = frame(v, w)
        need(sum(probability(p, psi) for p in ps) == 1, "context probabilities")
        complements.append(norm(cross(v, w)))
        compiled = retry(ps, denominator=6)
        need(compiled.success == F(9, 16), "common herald rate")
        need(len(compiled.columns) == 15, "outcome/data address accounting")
        costs.append(compiled.physical_mixers)
    need(
        tuple(complements) == (F(1), F(2), F(6), F(6), F(2)), "auxiliary norm boundary"
    )
    p = projector(rays[3])
    complement = add(eye(3), scale(p, g(-1)))
    binary = retry((p, complement))
    reflection = add(eye(3), scale(p, g(-2)))
    reflected = retry((reflection,))
    need(binary.success == reflected.success == F(9, 16), "binary/reflection retry")
    need(
        scale(add(eye(3), reflection), g(F(1, 2))) == complement, "reflection + outcome"
    )
    need(
        scale(add(eye(3), scale(reflection, g(-1))), g(F(1, 2))) == p,
        "reflection - outcome",
    )
    need(not gaussian_norm_integer(3) and gaussian_norm_integer(9), "norm obstruction")
    for m in range(1, 101):
        need(
            gaussian_norm_integer(m**3) == gaussian_norm_integer(m),
            "odd determinant valuation",
        )
    for j, k in product(range(-4, 5), repeat=2):
        if j or k:
            need(gaussian_norm_integer(j * j + k * k), "Gaussian norm control")
            need(
                not gaussian_norm_integer(3 * (j * j + k * k)), "norm-3 column control"
            )
    # The 5-and-17 comparator is an exact unitary-basis algebraic witness,
    # not a compiled word from only the single additional phase z_5.
    comparator: tuple[Ray, ...] = (
        rays[0],
        rays[1],
        (g(4), ZERO, g(3)),
        (g(-3), g(-3), g(4)),
        (ZERO, g(4), g(3)),
    )
    need(
        sum(probability(projector(v), psi) for v in comparator) == F(922, 425),
        "two-prime comparator",
    )
    for j, v in enumerate(comparator):
        w = comparator[(j + 1) % 5]
        ps = frame(v, w)
        need(len(ps) == 3, "comparator context")
        for r in (v, w, cross(v, w)):
            n = norm(r)
            need(
                n.denominator == 1 and gaussian_norm_integer(int(n)),
                "comparator normalization",
            )
            rest = int(n)
            for prime in (2, 5, 17):
                while rest % prime == 0:
                    rest //= prime
            need(rest == 1, "comparator introduced another prime")
    # Independent finite verification of the primitive cross-gcd formula.
    small = pair_classes(1)
    for (a, b), (c, d) in product(small, repeat=2):
        nums = (gc(gm(b, c)), gc(gm(a, d)), gc(gm(a, c)))
        common = gcd_gaussian(gcd_gaussian(nums[0], nums[1]), nums[2])
        actual = sum(gn(gd(z, common)) for z in nums)
        need(actual == middle_norm((a, b), (c, d)), "cross-gcd formula")
    q = F(7, 16)
    need(1 / (1 - q) == F(16, 9), "mean attempts")
    need(F(12, 13) * sum(probs) == 2, "uniform loss boundary")
    need((1 - q**3) * sum(probs) < 2 < (1 - q**4) * sum(probs), "cutoff count control")
    return probs, tuple(costs)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime5-exponent", type=int, choices=range(6), default=2)
    args = parser.parse_args()
    probs, costs = controls()
    phase5_controls()
    count, comparisons, hits = scan_prime5(args.prime5_exponent)
    expected_counts = (1, 7, 37, 187, 937, 4687)
    need(count == expected_counts[args.prime5_exponent], "finite enumeration count")
    need(
        hits == 0, "bounded prime-5 regression changed; inspect before claiming a wall"
    )
    print(f"Exact sharp-projector pentagon: probabilities={probs}, sum=13/6 > 2.")
    print(f"Five common-rate native instrument words: physical T counts={costs}.")
    print(
        "Resource: 15 logical outcome/data addresses (30 encoded physical rails), not three raw slots."
    )
    print(
        "Supplied neutral retry: p=9/16, mean attempts=16/9, tail=(7/16)^N; no bounded worst case."
    )
    print(
        "Three-slot projectively Q(i) unitary cannot send an axis to (1,1,1); rational sharp instruments can."
    )
    print(
        "Symmetric prime-5-only pentagon: excluded by parity and consecutive powers, not a general no-go."
    )
    print(
        f"Finite R5 scan: max primitive pair norm={2 * 5**args.prime5_exponent}, "
        f"coordinate-phase classes={count}, unordered comparisons={comparisons}, hits={hits}."
    )
    print(
        "Broader single-z/prime-5 route remains open here; two-prime algebraic comparator gives 922/425."
    )
    print(
        "No physical readout, fair sampling, generalized noncontextuality, or full-QM claim is derived."
    )


if __name__ == "__main__":
    main()
