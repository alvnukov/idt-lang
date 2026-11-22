"""A population echo does not fix the internal frame of a balanced mixer.

Supplied model: two rank-two real ports, additive linear propagation,
port-separable squared-norm stock, a fixed orthogonal normalized mixer,
and coherent scalar shutters with no feedback or survival renormalization.
Integral raw mixers below have common stock gain 100. Graded shutters and
normalized propagation are rational calculations on the real extension;
their availability is not derived from the integral lattice.

Calibrated normal form, in any equal finite port rank: every single-port
input splits stock equally. This balance and unitarity allow
T = [U,V;W,Z]/sqrt(2), with unitary blocks. A two-step
port-subspace swap gives W = -V^-1 U^2. Column orthogonality then gives
Z = V^-1 U V. For G = diag(I,V^-1 U),

    G^-1 T G = diag(U,U) [I,I;-I,I]/sqrt(2).

This is a static joint change of coordinates, not a physically accessible
gate: preparation and any extra controls must be transformed as well.
Single-port scalar-shutter words cannot see U, and T^4 has port holonomy
conjugate to -U^4. Nothing here derives a metric, Born rule, or normal form
from arbitrary nonnegative stocks. The checks use unnormalized rational
blocks and avoid evaluating sqrt(2).

Stronger equal-word countercontrol: J^2=-I, M0=[I+J,I-J;I-J,I+J],
N=5*M0, K=3*I+4*J, M=diag(K,K)*M0. With R=K/5, M=diag(R,R)*N.
The common rotation commutes with N and all scalar port shutters. Thus
every chronological word S_n M ... S_1 M equals diag(R^n,R^n) times
the corresponding N word, by induction, for ALL inputs and word lengths.
The finite enumeration checks this identity and both port Gram matrices,
not just basis intensities. Yet M^4 is not 10000*I, so there is no static
joint conjugacy to N. Equal observable words do not require such conjugacy.

Two extra controls separate the models, with different supplied premises:
* A fixed reflection in port zero is anti-linear relative to J. It is not
  an ordinary complex-linear phase plate or a promised realizable device.
* A coherent four-pass/zero-pass reference comparator requires equal-time
  arrival, stable coherent splitting/recombination, and identity internal
  transport in the delayed reference arm. Padding that arm with the same
  four-step drift cancels the effect. Unequal device count alone does not
  certify a phase-stable clock or delay.

The existing probe_phase_comparison_links.py treats signed-permutation
link gauges; no such census is repeated here. This is an exact conditional
executable fixture, not a Lean artifact or evidence that QM is derived.

Run: python3 -B -O -m scripts.probe_echo_gauge_normal_form
"""

from fractions import Fraction as F
from itertools import product

Matrix = tuple[tuple[F, ...], ...]
Vector = tuple[F, ...]


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def matrix(rows: tuple[tuple[int, ...], ...]) -> Matrix:
    return tuple(tuple(F(value) for value in row) for row in rows)


def eye(rank: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(rank)) for i in range(rank))


def scale(value: F, a: Matrix) -> Matrix:
    return tuple(tuple(value * x for x in row) for row in a)


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(x + y for x, y in zip(row, other, strict=True))
        for row, other in zip(a, b, strict=True)
    )


def transpose(a: Matrix) -> Matrix:
    return tuple(zip(*a, strict=True))


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((x * y for x, y in zip(row, col, strict=True)), F(0))
            for col in transpose(b)
        )
        for row in a
    )


def power(a: Matrix, exponent: int) -> Matrix:
    need(exponent >= 0, "negative matrix power")
    result = eye(len(a))
    for _ in range(exponent):
        result = mul(a, result)
    return result


def block(a: Matrix, b: Matrix, c: Matrix, d: Matrix) -> Matrix:
    return tuple(x + y for x, y in zip(a, b, strict=True)) + tuple(
        x + y for x, y in zip(c, d, strict=True)
    )


I = eye(2)
ZERO = scale(F(0), I)
J = matrix(((0, -1), (1, 0)))
P0 = block(I, ZERO, ZERO, ZERO)
P1 = block(ZERO, ZERO, ZERO, I)
SWAP = block(ZERO, I, I, ZERO)


def common(a: Matrix) -> Matrix:
    return block(a, ZERO, ZERO, a)


def port_gram(word: Matrix, port: Matrix) -> Matrix:
    return mul(transpose(word), mul(port, word))


def apply(a: Matrix, x: Vector) -> Vector:
    return tuple(sum((u * v for u, v in zip(row, x, strict=True)), F(0)) for row in a)


def norm_square(x: Vector) -> F:
    return sum((value * value for value in x), F(0))


def port_yields(x: Vector) -> tuple[F, F]:
    return norm_square(x[:2]), norm_square(x[2:])


def models() -> tuple[Matrix, Matrix, Matrix]:
    base = block(add(I, J), add(I, scale(F(-1), J)), add(I, scale(F(-1), J)), add(I, J))
    reference = scale(F(5), base)
    k = add(scale(F(3), I), scale(F(4), J))
    rotated = mul(common(k), base)
    rotation = scale(F(1, 5), k)
    need(mul(J, J) == scale(F(-1), I), "quarter-turn convention")
    need(mul(transpose(rotation), rotation) == I, "common rotation is orthogonal")
    need(rotated == mul(common(rotation), reference), "common drift factorization")
    need(all(x.denominator == 1 for row in rotated for x in row), "raw integrality")
    return reference, rotated, rotation


def check_echo(reference: Matrix, rotated: Matrix) -> None:
    a = add(scale(F(-1), I), scale(F(7), J))
    b = add(scale(F(7), I), J)
    need(rotated == block(a, b, b, a), "explicit integral countercontrol")
    echo = add(scale(F(-28), I), scale(F(96), J))
    holonomy = add(scale(F(-8432), I), scale(F(-5376), J))
    need(power(reference, 2) == scale(F(100), SWAP), "literal reference echo")
    need(power(rotated, 2) == block(ZERO, echo, echo, ZERO), "twisting echo")
    need(power(rotated, 4) == common(holonomy), "four-step hidden holonomy")
    need(power(rotated, 4) != power(reference, 4), "not statically conjugate to N")
    # N^4=10000*I is invariant under EVERY invertible static conjugacy.
    need(power(reference, 4) == scale(F(10000), eye(4)), "scalar reference fourth")
    for raw in (reference, rotated):
        need(mul(transpose(raw), raw) == scale(F(100), eye(4)), "common stock gain")
        normalized = scale(F(1, 10), raw)
        twice = power(normalized, 2)
        need(port_gram(twice, P0) == P1, "all-state population echo")
        need(port_gram(twice, P1) == P0, "reverse population echo")
        for source_port in (P0, P1):
            first = mul(normalized, source_port)
            for output_port in (P0, P1):
                need(
                    port_gram(first, output_port) == scale(F(1, 2), source_port),
                    "every single-port preparation splits equally",
                )
            shuttered = mul(normalized, mul(source_port, first))
            need(
                port_gram(shuttered, source_port) == scale(F(1, 4), source_port),
                "unconditional same-port quarter return",
            )


def check_normal_form() -> int:
    """Rational scaled version; G is a coordinate change, not a new gate."""
    reflection = matrix(((1, 0), (0, -1)))
    rotations = (I, J, scale(F(1, 5), matrix(((3, -4), (4, 3)))))
    orthogonal = rotations + tuple(mul(r, reflection) for r in rotations)
    count = 0
    half_scale = F(2)  # Each raw block has A^t A = half_scale * I.
    seed = add(I, J)
    for u, v in product(orthogonal, repeat=2):
        a = mul(u, seed)
        b = mul(v, seed)
        inverse_b = scale(1 / half_scale, transpose(b))
        c = scale(F(-1), mul(inverse_b, power(a, 2)))
        d = mul(inverse_b, mul(a, b))
        raw = block(a, b, c, d)
        need(mul(transpose(raw), raw) == scale(F(4), eye(4)), "normal-form model gain")
        square = power(raw, 2)
        need(
            mul(P0, mul(square, P0)) == scale(F(0), eye(4)), "square leaves first port"
        )
        need(
            mul(P1, mul(square, P1)) == scale(F(0), eye(4)), "square leaves second port"
        )
        gauge = block(I, ZERO, ZERO, mul(inverse_b, a))
        need(mul(transpose(gauge), gauge) == eye(4), "orthogonal port-frame change")
        canonical = block(a, a, scale(F(-1), a), a)
        need(
            mul(transpose(gauge), mul(raw, gauge)) == canonical,
            "static joint normal form",
        )
        expected_fourth = scale(F(-4), common(power(a, 4)))
        need(power(canonical, 4) == expected_fourth, "scaled -U^4 holonomy")
        # A preparation must change coordinates too; this is not access to G.
        preparation = tuple(map(F, (1, 2, 3, 4)))
        renamed = apply(transpose(gauge), preparation)
        need(
            port_yields(apply(raw, preparation))
            == port_yields(apply(canonical, renamed)),
            "joint coordinate change preserves these measured yields",
        )
        count += 1
    return count


def check_words(reference: Matrix, rotated: Matrix, rotation: Matrix) -> int:
    shutters = tuple(
        block(scale(left, I), ZERO, ZERO, scale(right, I))
        for left, right in (
            (F(1), F(1)),
            (F(1), F(0)),
            (F(0), F(1)),
            (F(1), F(1, 2)),
            (F(1, 3), F(1)),
        )
    )
    drift = common(rotation)
    need(mul(drift, reference) == mul(reference, drift), "drift commutes with mixer")
    for shutter in shutters:
        need(mul(drift, shutter) == mul(shutter, drift), "drift commutes with shutter")
    count = 0
    for depth in range(1, 5):
        output_drift = common(power(rotation, depth))
        for indices in product(range(len(shutters)), repeat=depth):
            ordinary_word = twisted_word = eye(4)
            for index in indices:
                ordinary_word = mul(shutters[index], mul(reference, ordinary_word))
                twisted_word = mul(shutters[index], mul(rotated, twisted_word))
            need(
                twisted_word == mul(output_drift, ordinary_word), "exact word identity"
            )
            for port in (P0, P1):
                need(
                    port_gram(twisted_word, port) == port_gram(ordinary_word, port),
                    "all-preparation port-stock equality, including cross terms",
                )
            count += 1
    need(count == 780, "finite word census")
    return count


def check_extra_controls(reference: Matrix, rotated: Matrix, rotation: Matrix) -> None:
    reflection = matrix(((1, 0), (0, -1)))
    need(
        mul(reflection, J) == scale(F(-1), mul(J, reflection)),
        "J-antilinear reflection",
    )
    reflect_port = block(reflection, ZERO, ZERO, I)
    phase_port = block(J, ZERO, ZERO, I)
    source = tuple(map(F, (1, 0, 0, 0)))
    ordinary = scale(F(1, 10), reference)
    twisted = scale(F(1, 10), rotated)
    need(
        port_yields(apply(mul(ordinary, mul(reflect_port, ordinary)), source))
        == (F(1, 2), F(1, 2)),
        "reference with fixed reflection",
    )
    need(
        port_yields(apply(mul(twisted, mul(reflect_port, twisted)), source))
        == (F(49, 50), F(1, 50)),
        "twisted model with same fixed reflection",
    )
    phase_n = mul(ordinary, mul(phase_port, ordinary))
    phase_m = mul(twisted, mul(phase_port, twisted))
    need(
        phase_m == mul(common(power(rotation, 2)), phase_n),
        "ordinary phase plate stays blind",
    )
    for port in (P0, P1):
        need(
            port_gram(phase_m, port) == port_gram(phase_n, port),
            "phase-plate stock equality",
        )

    # External branch labels, not the original mixer ports. The supplied
    # splitter/recombiner gives (signal +/- delayed_reference)/2; both arms
    # arrive together and no conditional-on-survival normalization is used.
    def compare(signal: Vector, delayed: Vector) -> tuple[F, F]:
        plus = tuple((x + y) / 2 for x, y in zip(signal, delayed, strict=True))
        minus = tuple((x - y) / 2 for x, y in zip(signal, delayed, strict=True))
        return norm_square(plus), norm_square(minus)

    original_return = apply(power(ordinary, 4), source)
    twisted_return = apply(power(twisted, 4), source)
    need(
        compare(original_return, source) == (F(1), F(0)),
        "identity-delay reference baseline",
    )
    need(
        compare(twisted_return, source) == (F(49, 625), F(576, 625)),
        "unequal-depth contrast with identity internal delay",
    )
    same_drift_delay = apply(common(power(rotation, 4)), source)
    need(
        compare(twisted_return, same_drift_delay) == (F(1), F(0)),
        "synchronized same-drift padding cancels the contrast",
    )


def main() -> None:
    reference, rotated, rotation = models()
    check_echo(reference, rotated)
    normal_forms = check_normal_form()
    words = check_words(reference, rotated, rotation)
    check_extra_controls(reference, rotated, rotation)
    print(
        f"Exact calibrated checks: {normal_forms} rational normal forms; {words} shutter words, all-input Gram equality."
    )
    print(
        "Both integer mixers: gain 100, all single-port inputs split 1/2 and return 1/4 through a shutter; only the reference has literal positive echo."
    )
    print(
        "Fixed J-antilinear reflection: (1/2, 1/2) versus (49/50, 1/50). Ordinary J-phase control stays blind."
    )
    print(
        "Coherent four-pass/identity-delay reference: (1, 0) versus (49/625, 576/625); same-drift padding restores (1, 0)."
    )
    print(
        "All-word blindness follows from commuting common drift. Static joint conjugacy is not control access; no norm, clock, or QM derivation."
    )


if __name__ == "__main__":
    main()
