"""A conditional carrier dichotomy, not a derivation of the ambient plane.

Let G be a nonzero additive subgroup of a real inner-product plane, closed
under the isometric quarter-turn J. Write Q for squared length in FIXED
stock units, and m=inf{Q(x):0≠x∈G}. If m>0, pick v∈G with 0<Q(v)<2m.
Use the real orthogonal coordinates in v,Jv to round each x∈G to a point
of Zv+ZJv. The difference is still in G and has Q≤Q(v)/2<m, so it is
zero. Thus G=Zv+ZJv; v turns out to be shortest. If m=0, the same square
meshes for arbitrarily short nonzero v approximate EVERY point of the
plane, with covering radius sqrt(Q(v)/2). Thus G is dense, not necessarily
the entire plane and not necessarily closed under exact halving.

Alternative formulation: start with an abelian group, a positive semidefinite
quadratic stock (e.g. from a real nonnegative parallelogram law by
polarization), and additive J preserving it with J²=-I. For a visible v,
B(v,Jv)=0. If the Gram determinant of (v,Jv,x) is zero for EVERY x,
Q(x)=[B(x,v)²+B(x,Jv)²]/Q(v). These two additive coordinates modulo the
dark kernel therefore embed the visible quotient into an inner-product
plane. This is a real rank premise, not a count of wires or a finite list of
Gram tests. Without faithfulness, positive visible floor does not identify
the underlying group. Rank four with ordinary squared length on Z[i]^2
likewise has a floor but need not be one Gaussian lattice of rank two.

Z[i], Z[i,1/2], and Q(i) agree on squared weights for common raw integer
circuits and inputs. The latter two carriers allow additional inputs/maps.
Finite rational rays admit common-denominator representatives, including
ONE scale for all maps of an instrument, arms to be recombined, and
sibling outcomes (including rejected outcomes). Local rational maps are
not thereby synthesized by a fixed native gate alphabet. Prefactors must
be carried across layers/unequal-depth branches. This projective comparison
does not preserve named stock units, absolute throughput or independent
phase/scale references by arbitrary branchwise rescaling.

In the Gaussian lattice the two subgroups z Z[i] and Zz+ZJz coincide.
In R=Z[i,1/2] at z=2 they do NOT: 2R=R, whereas 2Z+2iZ has infinite
index in R. Thus neither continuation of an integer-lattice index is
selected merely by seeing the port's squared weight 4 at that input.

All conclusions are mathematical under the stated hypotheses. One click,
one low-intensity run, or positive counts on tested preparations do not
supply a universal, faithful unnormalized stock gap. No experimental fit.

Run: python3 -O -m scripts.probe_carrier_resolution
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import lcm

Point = tuple[F, F]


def need(test: bool, reason: str) -> None:
    if not test:
        raise ValueError(reason)


def dot(x: Point, y: Point) -> F:
    return x[0] * y[0] + x[1] * y[1]


def mesh(x: Point, v: Point) -> tuple[Point, F]:
    """Nearest square-mesh point, exact on rational coordinates."""
    q = dot(v, v)
    need(q > 0, "nonzero mesh step")
    jv = (-v[1], v[0])
    m, n = round(dot(x, v) / q), round(dot(x, jv) / q)
    w = m * v[0] + n * jv[0], m * v[1] + n * jv[1]
    rem = x[0] - w[0], x[1] - w[1]
    need(dot(rem, rem) <= q / 2, "covering radius")
    return w, dot(rem, rem)


def gap_controls() -> None:
    v = F(2), F(1)
    for m, n in product(range(-3, 4), repeat=2):
        x = 2 * F(m) - n, F(m) + 2 * n
        need(dot(x, x) == 5 * (m * m + n * n), "example with stock gap five")
        need(mesh(x, v) == (x, F(0)), "gap closes residual")
        need(
            dot(x, v) ** 2 + dot(x, (-v[1], v[0])) ** 2 == dot(x, x) * dot(v, v),
            "Gram identity",
        )
    # Tight covering-radius control, not a point of this discrete carrier.
    _, err = mesh((F(1, 2), F(3, 2)), v)
    need(err == F(5, 2), "mid-cell corner")

    # Dark factor G=Z[i] ⊕ Z[i,1/2], J rotates both pairs. These are
    # genuinely distinct source elements but give identical visible Q.
    def visible(x: tuple[Point, Point]) -> F:
        return dot(x[0], x[0])

    z = F(0), F(0)
    concealed = (F(1, 16), F(0))
    need(visible((z, concealed)) == 0 and concealed != z, "dark kernel")
    need(
        visible((v, z)) == visible((v, concealed)) == F(5), "quotient, not hidden group"
    )


def positive_surd(a: int, b: int) -> bool:
    """Strict sign of a+b√2, using integer comparisons, no rounding."""
    if b == 0:
        return a > 0
    if b > 0:
        return a >= 0 or 2 * b * b > a * a
    return a > 0 and a * a > 2 * b * b


def dense_not_divisible() -> None:
    # H=Z[i]+√2 Z[i] is additive and J-invariant; 1/2 is NOT in H:
    # rational independence of 1,√2 would require 2a=1 in the real component.
    # δ=√2-1 lies in (0,1/2); δ^n∈Z[√2] never vanishes and tends to zero.
    # For even n, (1-δ^n)/2 is in H and tends to the missing half.
    a, b = 1, 0
    for n in range(1, 25):
        a, b = 2 * b - a, a - b
        need(a * a - 2 * b * b == (-1) ** n, "Pell norm")
        need(
            positive_surd(a, b) and positive_surd(1 - 2**n * a, -(2**n) * b),
            "0 < δ^n < 2^-n",
        )
        if n % 2 == 0:
            u, w = (1 - a) // 2, -b // 2
            need(
                (1 - 2 * u, -2 * w) == (a, b),
                "exact dense approximant to the missing half",
            )
    print(
        "Dense need not mean divisible: Z[i]+√2 Z[i] approximates 1/2 but does not contain it."
    )


def dyadic(x: F) -> bool:
    return x.denominator & (x.denominator - 1) == 0


def index_controls() -> None:
    # Four parity cosets in Z[i]/2Z[i]. In R, halving ANY dyadic pair is
    # again dyadic: hence R/2R has only one coset, not four.
    need(
        {(a % 2, b % 2) for a, b in product(range(-2, 3), repeat=2)}
        == set(product(range(2), repeat=2)),
        "Gaussian index 4",
    )
    reps = [F(1, 2**k) for k in range(1, 17)]
    need(all(dyadic(x / 2) and 2 * (x / 2) == x for x in reps), "2R=R")
    # ALL such representatives for distinct k>=1 differ by a nonzero
    # magnitude <1, hence not an even integer. This family is infinite.
    need(
        all((x - y).denominator > 1 for x, y in combinations(reps, 2)),
        "distinct modulo integer span",
    )
    print(
        "At z=2: squared stock 4; lattice index 4; dyadic ideal index 1; integer-span index infinite."
    )


def common_rays() -> None:
    maps = F(3, 5), F(16, 25), F(12, 25)
    norm_sum = sum((k * k for k in maps), F(0))
    need(norm_sum == 1, "complete sibling instrument incl. third outcome")
    common = lcm(*(k.denominator for k in maps))
    correct = tuple(int(k * common) for k in maps)
    wrong = tuple(k.numerator for k in maps)

    def shares(nums: tuple[int, ...]) -> tuple[F, ...]:
        total = sum(n * n for n in nums)
        return tuple(F(n * n, total) for n in nums)

    expected = tuple(k * k for k in maps)
    need(
        correct == (15, 16, 12) and shares(correct) == expected,
        "one multiplier for the whole instrument",
    )
    need(
        shares(wrong)[0] == F(9, 409) and shares(wrong) != expected,
        "branchwise clearing changes odds",
    )
    print(
        f"Sibling maps: shared scale 25 gives (15,16,12), first share {expected[0]}; separate scales give {shares(wrong)[0]}."
    )


def max_halvings(initial: F, floor: F) -> int:
    """Most *amplitude* halvings compatible with a fixed positive stock floor."""
    need(initial >= floor > 0, "initial visible stock must already meet the floor")
    n = 0
    while initial >= 4 * floor:
        initial /= 4
        n += 1
    return n


def halving_controls() -> None:
    q0, lower = F(64), F(1)
    n = max_halvings(q0, lower)
    need(n == 3 and q0 / 4**n >= lower > q0 / 4 ** (n + 1), "exact finite bound")
    for t in range(9):
        raw = q0 / 4**t
        need(raw * 4**t == q0, "increasing exposure can mask the raw decline")
    print(
        "Fixed units, Q0=64, floor=1: at most 3 successive amplitude halvings; a fourth gives 1/4."
    )
    print(
        "Multiplying exposure by 4 per step masks that drop; pooled counts are not a raw-stock floor."
    )


def run() -> None:
    gap_controls()
    print(
        "Visible rank-two plane with J: a positive fixed stock floor forces G=Zv+ZJv; without a gap G is dense."
    )
    print(
        "An invisible additive factor survives all visible measurements: only the quotient is recovered."
    )
    dense_not_divisible()
    index_controls()
    common_rays()
    halving_controls()


if __name__ == "__main__":
    run()
