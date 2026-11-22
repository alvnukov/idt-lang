"""Unsigned marks and contextual neutrality: conditional algebra, exact controls.

Start with a free commutative monoid of cyclic colors, not signed or complex
counts. A LOCAL vacuum equivalence must be a congruence under juxtaposition,
cyclic relabeling and every admitted dynamic context. Four colors with each
opposite pair neutral acquire additive inverses and form the free cyclic
Z[i]-module, before further relations. Three colors with the full triad
neutral similarly give Z[omega], omega^2+omega+1=0; the inverse of one
mark is the other two. An extra R-stable congruence on either resulting
group is an ideal quotient. Zero ideal gives the free rank-two lattice;
any nonzero ideal gives a finite carrier, since it contains the nonzero
integer norm of any nonzero element. The zero carrier is also possible.
These statements supply neither a physical norm nor serial multiplication.

Four-color FULL-ORBIT neutrality alone instead gives
Z[t]/(1+t+t^2+t^3), rank three. Coordinates are
z=(a-c)+i(b-d), h=a-b+c-d, with h == Re(z)-Im(z) modulo two.
R sends (z,h) to (i*z,-h); the rational alternating sector is not removed.
Conversely, (u,v,h) with that parity has representative
((h+u+v)/2, v, (h-u+v)/2, 0); common padding makes it unsigned.
Thus the integral image is index two in Z^3, not an unqualified direct sum.
The detector W=(1+h^2)|z|^2 is nonnegative and R-invariant. Opposite pairs
are dark, but W(a)=2 while W(a+a+c)=10. One additional UNSIGNED mark
therefore refutes additive-context neutrality without a new dynamic gate.
The full orbit really is neutral in this countermodel. Darkness is not
congruence. A finite test set cannot certify arbitrary-context equivalence
without a complete finite carrier, separating observations, or other
structural assumptions; finite hidden/periodic alternatives remain possible.

PHASE VERSUS POPULATION. A literal M^2=g*S, g!=0, on two scalar ports over
K=Q(omega), with K-linear dynamics, makes M commute with S. Its sum and
difference eigenvalues obey lambda_+^2=g, lambda_-^2=-g, so their ratio
would square to -1. But i is not in K: (a+b*omega)^2=-1 forces b=0 or
b=2a; the latter needs rational a^2=1/3, excluded by prime-three descent.
This algebraic argument is not a bounded search over possible mixers.

The real integer map M(x,y)=(x-y,x+y) is nevertheless Eisenstein-linear,
has norm-stock gain 2, square (-2y,2x), equal single-input splitting and
quarter shutter return. Its minus uses the triad-derived inverse, not an
initial signed primitive. It gives population echo, NOT labelled g*S.
Likewise a scalar Eisenstein norm cannot equal 1/2: clearing denominators
and Q(a,b)=a^2-ab+b^2 modulo two forces all three integers even. This
does not forbid half probabilities with common projective gain, a bypass
split into two retained outputs, or a larger internal carrier. Two copies
with J_eff(x,y)=(-y,x) give J_eff^2=-I and a literal Gaussian-style root.

The field obstruction requires a torsion-free scalar carrier. Modulo five,
i=2 exists and [[3,4],[4,3]]^2=4*S. Its fourth power is identity: no
nontrivial global stock with common gain h!=1 can follow that cycle.
No globally compatible positive common-gain readout is asserted for it.
The separate finite quotient controls agree with free-lattice intensities
on a fixed small window, but not on unlimited preparations. Such finite
agreement is not a proof of the free carrier or of a universal gain law.

Existing phase-color/composition probes start with signed coordinates and
stronger readout assumptions; they are not reimplemented here. Exact
finite regressions accompany the arguments, not Lean proofs, empirical
selection of colors, probability origins, or QM closure.
Run: python3 -B -O -m scripts.probe_unsigned_neutral_motifs
"""

from collections.abc import Callable
from fractions import Fraction as F
from itertools import product

Pair = tuple[int, int]
Double = tuple[Pair, Pair]
ZERO: Pair = (0, 0)
ONE: Pair = (1, 0)


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def lattice(start: int, stop: int) -> tuple[Pair, ...]:
    return tuple((a, b) for a in range(start, stop) for b in range(start, stop))


def add(x: Pair, y: Pair) -> Pair:
    return x[0] + y[0], x[1] + y[1]


def scale(k: int, x: Pair) -> Pair:
    return k * x[0], k * x[1]


def gaussian(x: tuple[int, ...]) -> Pair:
    a, b, c, d = x
    return a - c, b - d


def eisenstein(x: tuple[int, ...]) -> Pair:
    a, b, c = x
    return a - c, b - c


def turn_g(x: Pair) -> Pair:
    return -x[1], x[0]


def turn_e(x: Pair) -> Pair:
    return -x[1], x[0] - x[1]


def norm_g(x: Pair) -> int:
    return x[0] ** 2 + x[1] ** 2


def norm_e(x: Pair) -> int:
    a, b = x
    return a * a - a * b + b * b


def mul_g(x: Pair, y: Pair) -> Pair:
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c


def mul_e(x: Pair, y: Pair) -> Pair:
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c - b * d


def cycle(x: tuple[int, ...]) -> tuple[int, ...]:
    return x[-1:] + x[:-1]


def hidden(x: tuple[int, ...]) -> tuple[int, int, int]:
    a, b, c, d = x
    return a - c, b - d, a - b + c - d


def hidden_weight(x: tuple[int, ...]) -> int:
    a, b, h = hidden(x)
    return (1 + h * h) * (a * a + b * b)


def neutral_controls() -> None:
    for x in product(range(3), repeat=4):
        need(gaussian(cycle(x)) == turn_g(gaussian(x)), "four-color relabel induces i")
        need(
            gaussian(tuple(a + b for a, b in zip(x, (1, 0, 1, 0), strict=True)))
            == gaussian(x),
            "opposite motif is a Gaussian relation",
        )
    for x in product(range(3), repeat=3):
        need(
            eisenstein(cycle(x)) == turn_e(eisenstein(x)),
            "three-color relabel induces omega",
        )
        need(
            eisenstein(tuple(value + 1 for value in x)) == eisenstein(x),
            "full triad relation",
        )
    for u, v in lattice(-5, 6):
        unsigned_g = (max(u, 0), max(v, 0), max(-u, 0), max(-v, 0))
        padding = max(0, -u, -v)
        unsigned_e = (u + padding, v + padding, padding)
        need(
            gaussian(unsigned_g) == eisenstein(unsigned_e) == (u, v),
            "unsigned representatives of derived group coordinates",
        )
    need(
        gaussian((0, 0, 1, 0)) == eisenstein((0, 1, 1)) == (-1, 0),
        "inverses use unsigned motifs",
    )


def one_mark_hidden_control() -> int:
    classes: dict[tuple[int, int, int], tuple[int, ...]] = {}
    for x in product(range(4), repeat=4):
        a, b, h = hidden(x)
        need((h - a + b) % 2 == 0, "index-two parity condition")
        canonical = tuple(value - min(x) for value in x)
        key = hidden(x)
        need(
            classes.setdefault(key, canonical) == canonical,
            "only full-orbit translations disappear in this box",
        )
        need(hidden(cycle(x)) == (-b, a, -h), "alternating sector survives relabeling")
        need(hidden_weight(cycle(x)) == hidden_weight(x), "cyclic detector covariance")
        need(
            hidden_weight(tuple(value + 1 for value in x)) == hidden_weight(x),
            "full orbit truly neutral in additive context",
        )
    for u, v, h in product(range(-2, 3), repeat=3):
        if (h - u + v) % 2 == 0:
            representative = ((h + u + v) // 2, v, (h - u + v) // 2, 0)
            padding = max(0, -min(representative))
            unsigned = tuple(value + padding for value in representative)
            need(hidden(unsigned) == (u, v, h), "constructive rank-three parity image")
    opposite: tuple[int, ...] = (1, 0, 1, 0)
    for _ in range(4):
        need(hidden_weight(opposite) == 0, "every cyclic opposite pair is dark")
        opposite = cycle(opposite)
    need(hidden_weight((1, 0, 0, 0)) == 2, "one-mark baseline")
    need(
        hidden_weight((2, 0, 1, 0)) == 10,
        "one additional mark exposes non-neutral hidden sector",
    )
    need(len(classes) == 4**4 - 3**4, "bounded canonical full-orbit census")
    return len(classes)


def residue(x: Pair, modulus: int) -> Pair:
    return x[0] % modulus, x[1] % modulus


def quotient_weight(
    x: Pair,
    modulus: int,
    turn: Callable[[Pair], Pair],
    norm: Callable[[Pair], int],
    period: int,
) -> int:
    """An exact R-invariant finite readout; no global mixer gain is supplied."""
    values = []
    here = residue(x, modulus)
    for _ in range(period):
        a, b = ((value + modulus // 2) % modulus - modulus // 2 for value in here)
        values.append(norm((a, b)))
        here = residue(turn(here), modulus)
    return min(values)


def finite_quotient_controls() -> int:
    modulus = 37
    tests = 0
    for turn, norm, period in ((turn_g, norm_g, 4), (turn_e, norm_e, 3)):
        for x in lattice(0, modulus):
            need(
                quotient_weight(x, modulus, turn, norm, period)
                == quotient_weight(turn(x), modulus, turn, norm, period),
                "finite readout respects the whole cyclic relabeling",
            )
        for x in lattice(-8, 9):
            need(
                quotient_weight(x, modulus, turn, norm, period) == norm(x),
                "fixed bounded intensity window cannot distinguish quotient",
            )
            tests += 1
        need(
            quotient_weight((modulus, 0), modulus, turn, norm, period)
            == 0
            < norm((modulus, 0)),
            "large preparation reveals periodic identification",
        )
    return tests


def population_mixer(x: Pair, y: Pair) -> tuple[Pair, Pair]:
    return add(x, scale(-1, y)), add(x, y)


def scalar_phase_controls() -> None:
    points = lattice(-2, 3)
    for x, y in product(points, repeat=2):
        a, b = population_mixer(x, y)
        need(
            norm_e(a) + norm_e(b) == 2 * (norm_e(x) + norm_e(y)),
            "Eisenstein common stock gain two",
        )
        need(
            population_mixer(a, b) == (scale(-2, y), scale(2, x)),
            "population echo is a skew labelled swap",
        )
    for x in points:
        if x != ZERO:
            first, cross = population_mixer(x, ZERO)
            returned, _ = population_mixer(first, ZERO)
            need(
                norm_e(first) == norm_e(cross) == norm_e(x),
                "half of common-gain output stock",
            )
            need(
                F(norm_e(returned), 4 * norm_e(x)) == F(1, 4),
                "unconditional quarter shutter return",
            )
    need(
        add(scale(-2, ONE), scale(2, ONE)) == ZERO != add(scale(2, ONE), scale(2, ONE)),
        "coherent labelled reference distinguishes skew from positive exchange",
    )
    need(
        {(a, b) for a, b in product(range(2), repeat=2) if norm_e((a, b)) % 2 == 0}
        == {(0, 0)},
        "parity certificate for no rational norm one-half or integer norm two",
    )
    need({a * a % 3 for a in range(3)} == {0, 1}, "prime-three descent certificate")
    ga, gb = (1, 1), (1, -1)
    need(
        add(mul_g(ga, ga), mul_g(gb, gb)) == ZERO and scale(2, mul_g(ga, gb)) == (4, 0),
        "Gaussian scalar literal swap root exists",
    )
    for x, y, z in product(points[:3], repeat=3):
        a, b = population_mixer(x, y)
        need(
            norm_e(a) + norm_e(b) + 2 * norm_e(z)
            == 2 * (norm_e(x) + norm_e(y) + norm_e(z)),
            "split bypass keeps both outputs, not a scalar identity bypass",
        )


def finite_mod5_control() -> None:
    imaginary = (2, 0)
    need(
        residue(mul_e(imaginary, imaginary), 5) == (4, 0),
        "i exists in the finite quotient",
    )
    a, b = (3, 0), (4, 0)
    need(residue(add(mul_e(a, a), mul_e(b, b)), 5) == ZERO, "finite-root diagonal zero")
    need(residue(scale(2, mul_e(a, b)), 5) == (4, 0), "finite-root cross block four")
    for x, y in product(lattice(0, 5), repeat=2):

        def step(left: Pair, right: Pair) -> tuple[Pair, Pair]:
            return residue(add(mul_e(a, left), mul_e(b, right)), 5), residue(
                add(mul_e(b, left), mul_e(a, right)), 5
            )

        once = step(x, y)
        twice = step(*once)
        need(
            twice == (residue(scale(4, y), 5), residue(scale(4, x), 5)),
            "finite labelled echo on all 625 inputs",
        )
        need(
            step(*step(*twice)) == (x, y),
            "four-step finite cycle blocks nonunit global stock gain",
        )


def double_add(x: Double, y: Double) -> Double:
    return add(x[0], y[0]), add(x[1], y[1])


def double_turn(x: Double) -> Double:
    return scale(-1, x[1]), x[0]


def double_mixer(x: Double, y: Double) -> tuple[Double, Double]:
    total, difference = (
        double_add(x, y),
        double_add(x, (scale(-1, y[0]), scale(-1, y[1]))),
    )
    rotated = double_turn(difference)
    return double_add(total, rotated), double_add(
        total, (scale(-1, rotated[0]), scale(-1, rotated[1]))
    )


def larger_carrier_control() -> None:
    points = lattice(-1, 2)
    doubles = tuple(product(points, points))
    for x, y in product(doubles, repeat=2):
        a, b = double_mixer(x, y)
        need(
            sum(norm_e(z) for z in a + b) == 4 * sum(norm_e(z) for z in x + y),
            "two-copy common stock gain four",
        )
        four_y = (scale(4, y[0]), scale(4, y[1]))
        four_x = (scale(4, x[0]), scale(4, x[1]))
        need(
            double_mixer(a, b) == (four_y, four_x),
            "two Eisenstein copies restore literal positive swap",
        )


def main() -> None:
    neutral_controls()
    classes = one_mark_hidden_control()
    finite_tests = finite_quotient_controls()
    scalar_phase_controls()
    finite_mod5_control()
    larger_carrier_control()
    print(
        f"Unsigned motif controls: Gaussian opposite pairs, Eisenstein full triad; the rank-three full-orbit quotient has {classes} classes in the checked box."
    )
    print(
        "Hidden alternating detector: opposite pairs dark in every cyclic orientation; one-mark context gives 2 versus 10, disproving neutrality."
    )
    print(
        f"Finite modulus-37 readouts match {finite_tests} bounded free-lattice intensities but fail on 37 copies; finite tests do not establish freeness."
    )
    print(
        "Eisenstein scalar population mixer: gain 2, skew echo, quarter shutter return. Literal field-level swap needs i; norm-half scalar is unavailable."
    )
    print(
        "Controls: modulus 5 has an algebraic literal root (no claimed global gain stock); split bypass and two-copy carrier evade stronger exclusions."
    )
    print(
        "Contextual neutrality, dynamic scope and readout remain supplied. No complex probability law, physical primitive selection or QM derivation."
    )


if __name__ == "__main__":
    main()
