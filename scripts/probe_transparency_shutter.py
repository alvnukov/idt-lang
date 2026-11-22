"""Positive same-port transmission after a genuine coherent shutter tests transparency.

Supplied raw law: integral linear M=[[A,B],[B,A]], M²=g*swap literally,
g a positive integer. Assume separate nonnegative, nontrivial port stocks
with zero vacuum, universally scaled by h>0. No intermediate normalization:
start in one port, send the blocked port to an isolated dump, apply M again
to the surviving port; the original output sees A²x.

If T+=A+B is not scalar, T+²=gI and T-²=-gI (T-=A-B) give trace zero for
both matrices and A²=sI, B²=-sI. The case s=0 is immediate. For s!=0,
symmetrize signs and ports to the common even nonnegative stock E. Mixed
input differences of the gain law, evaluated at independently variable
outputs (gz,gw) in im(M), make the mixed differences of E flat on L*Z²,
L=g*abs(s): choose shifts r=g*sign(s)*A*u, t=-g*sign(s)*B*v to get
A*r=L*u, B*t=L*v. Hence E(Lz)=Q(z) is a nonnegative quadratic form
(constant second differences; even and zero at the origin). Since
E(T±x)=hE(x), nonzero Q would be positive definite (its kernel is
T--invariant), h=g, and T+/sqrt(g), T-/sqrt(g) a Q-orthogonal reflection
and quarter-turn. They anticommute, contradicting s!=0. Thus E(Lz)=0.
M² gives E(gz)=h²E(z), so every port assigns zero to A²x even when A²x
is a nonzero vector. This conclusion does not require pointwise faithfulness.

Thus positive same-port stock forces T+=rI, g=r². Because T-=rI mod 2,
odd r would give T-²=I mod 4 instead of -I. The minimum |r|=2 is attainable,
not forced as the actual gain. The fixtures below are finite checks, not a
universal formal proof or detector evidence. Run: python3 -O -m scripts.probe_transparency_shutter
"""

from collections.abc import Callable
from fractions import Fraction as F
from itertools import combinations, product

V = tuple[int, int]
Mat = tuple[V, V]
Ports = tuple[V, V]
Blocks = tuple[Mat, Mat, Mat, Mat]
I: Mat = ((1, 0), (0, 1))
J: Mat = ((0, -1), (1, 0))
ZERO: V = (0, 0)


def check(ok: bool, why: str) -> None:
    if not ok:
        raise ValueError(why)


def add(x: V, y: V) -> V:
    return x[0] + y[0], x[1] + y[1]


def scaled(k: int, x: V) -> V:
    return k * x[0], k * x[1]


def rows(a: Mat, b: Mat, k: int = 1) -> Mat:
    return add(a[0], scaled(k, b[0])), add(a[1], scaled(k, b[1]))


def apply(a: Mat, x: V) -> V:
    return (a[0][0] * x[0] + a[0][1] * x[1], a[1][0] * x[0] + a[1][1] * x[1])


def mix(a: Mat, b: Mat, pair: Ports) -> Ports:
    x, y = pair
    return add(apply(a, x), apply(b, y)), add(apply(b, x), apply(a, y))


def echo(a: Mat, b: Mat, g: int) -> None:
    for e in I:
        for x, y in ((e, ZERO), (ZERO, e)):
            check(
                mix(a, b, mix(a, b, (x, y))) == (scaled(g, y), scaled(g, x)),
                "literal state echo",
            )


def squares(z: V) -> int:
    return z[0] ** 2 + z[1] ** 2


def mod_three(z: V) -> int:
    x, y = z
    return int((x + y) % 3 != 0) + int((x - y) % 3 != 0)


def check_gain(
    a: Mat, b: Mat, source: list[V], stock: Callable[[V], int], h: int
) -> bool:
    return all(
        sum(map(stock, mix(a, b, (x, y)))) == h * (stock(x) + stock(y))
        for x, y in product(source, repeat=2)
    )


def no_quadratic(a: Mat, b: Mat, g: int) -> bool:
    # Necessary selection equations Q(T±v)=g Q(v), unknown 3 coefficients.
    def terms(v: V) -> tuple[int, int, int]:
        x, y = v
        return x * x, x * y, y * y

    eqs = [
        tuple(t - g * s for t, s in zip(terms(apply(m, v)), terms(v), strict=True))
        for m in (rows(a, b), rows(a, b, -1))
        for v in (*I, (1, 1))
    ]
    return any(
        x[0] * (y[1] * z[2] - z[1] * y[2])
        - x[1] * (y[0] * z[2] - z[0] * y[2])
        + x[2] * (y[0] * z[1] - z[0] * y[1])
        != 0
        for x, y, z in combinations(eqs, 3)
    )


def calibrated_echo_benchmark(a: Mat, b: Mat, c: Mat, d: Mat) -> None:
    """Separate finite-dimensional squared-norm assumption; full-emission yield.

    U is orthogonal/unitary and the observed open echo is U†² P0 U²=P1.
    Q=U† P0 U is a projector and also U P1 U†. For a port-zero input,
    ||P0 U P0 U x||=||P1 Q x||. The (0,0) block of Q²=Q gives
    C†C=B-B² for B=P0 Q P0 restricted to the input port and C=P1 Q P0.
    Thus a quarter return on spanning inputs makes B=I/2, not U²=swap.
    """

    def dot(x: V, y: V) -> int:
        return x[0] * y[0] + x[1] * y[1]

    def trans(m: Mat) -> Mat:
        return (m[0][0], m[1][0]), (m[0][1], m[1][1])

    def act(m: Blocks, xy: Ports) -> Ports:
        p, q, r, s = m
        x, y = xy
        return add(apply(p, x), apply(q, y)), add(apply(r, x), apply(s, y))

    def signal(m: Blocks, g: int, x: V) -> tuple[F, F]:
        # M=sqrt(g)*U. Use independent shutter propagation and compression.
        p, q, _, _ = m
        norm = squares(x)
        first = apply(p, x)
        shut = act(m, (first, ZERO))[0]
        bx, cx = apply(trans(p), first), apply(trans(q), first)  # gB*x, gC*x
        imbalance = add(scaled(2, bx), scaled(-g, x))
        ret = F(squares(shut), g * g * norm)
        check(
            ret
            == F(squares(cx), g * g * norm)
            == F(g * dot(x, bx) - squares(bx), g * g * norm)
            == F(1, 4) - F(squares(imbalance), 4 * g * g * norm),
            "calibrated shutter/Gram/deficit identity",
        )
        return F(squares(first), g * norm), ret

    p: Mat = ((4, 3), (-3, -4))
    q: Mat = ((4, -3), (3, -4))
    nq: Mat = (scaled(-1, q[0]), scaled(-1, q[1]))
    hidden: Blocks = (p, nq, q, p)
    axes: tuple[Ports, ...] = ((I[0], ZERO), (I[1], ZERO), (ZERO, I[0]), (ZERO, I[1]))
    controls: tuple[tuple[Blocks, int, F], ...] = (
        ((a, b, b, a), 4, F(1, 4)),
        ((c, d, d, c), 4, F(0)),
        (hidden, 50, F(49, 2500)),
    )
    for m, g, expected_return in controls:
        for i, x0 in enumerate(axes):
            x1 = act(m, x0)
            x2 = act(m, x1)
            if m == hidden:
                check(
                    x2 == (scaled(-g, x0[1]), scaled(g, x0[0])),
                    "hidden echo is skew, not literal swap",
                )
            for j, y0 in enumerate(axes):
                y1 = act(m, y0)
                y2 = act(m, y1)
                check(
                    dot(x1[0], y1[0]) + dot(x1[1], y1[1]) == g * int(i == j),
                    "orthogonal on full space",
                )
                check(
                    dot(x2[0], y2[0]) == g * g * dot(x0[1], y0[1]),
                    "all-state norm-level port echo",
                )
        axis_signals = [signal(m, g, e) for e in I]
        check(
            all(
                split == F(1, 2) and ret == expected_return
                for split, ret in axis_signals
            ),
            "individual axes split equally in all three benchmarks",
        )
        # ||B-I/2||_op² <= ||B-I/2||_HS² = sum of orthonormal-basis deficits.
        budget = sum((F(1, 4) - ret for _, ret in axis_signals), F(0))
        for x in product(range(-2, 3), range(-2, 3)):
            if x == ZERO:
                continue
            split, ret = signal(m, g, x)
            check(
                ret == expected_return and (split - F(1, 2)) ** 2 <= budget,
                "basis-deficit bound",
            )
    check(
        signal(hidden, 50, (1, 1))[0] == F(49, 50)
        and signal(hidden, 50, (1, -1))[0] == F(1, 50),
        "hidden diagonal imbalance",
    )


def main() -> None:
    sample = [(x, y) for x, y in product(range(-1, 2), repeat=2)]
    a, b = rows(I, J), rows(I, J, -1)
    reflection: Mat = ((1, 0), (0, -1))
    c, d = rows(reflection, J), rows(reflection, J, -1)
    for same, cross in (
        (a, b),
        (rows(J, I, -1), rows(((-1, 0), (0, -1)), J, -1)),
        (c, d),
    ):
        echo(same, cross, 4)
        check(check_gain(same, cross, sample, squares, 4), "common-metric native gain")
        for x in sample:
            returned = apply(same, apply(same, x))
            check(
                squares(returned) == (0 if same == c else 4 * squares(x)),
                "same-port shutter vs emitted stock",
            )
    # Full open sequence for the tested native coordinate, including the open echo.
    p: Ports = (I[0], ZERO)
    q = p
    for _ in range(8):
        p, q = mix(a, b, p), mix(c, d, q)
        check(
            tuple(map(squares, p)) == tuple(map(squares, q)),
            "open counts differ on test input",
        )
    check(
        squares(apply(c, I[0])) == squares(apply(d, I[0])) == 2,
        "reflection can split 50:50",
    )
    # The lower bound on |r| does not identify an observed mixer as primitive.
    wide_a, wide_b = rows(a, a), rows(b, b)
    echo(wide_a, wide_b, 16)
    check(check_gain(wide_a, wide_b, sample, squares, 16), "larger scalar echo")
    check(
        all(
            4 * squares(apply(wide_a, apply(wide_a, x))) == 16**2 * squares(x)
            for x in sample
        ),
        "same emitted fraction at r=4",
    )

    fake: Mat = ((1, 2), (0, -1))
    fa, fb = rows(fake, J), rows(fake, J, -1)
    echo(fa, fb, 4)
    check(
        all(apply(fa, apply(fa, x)) == scaled(2, x) for x in sample),
        "exact quarter-yield counterfeit",
    )
    check(
        not check_gain(fa, fb, sample, squares, 4) and no_quadratic(fa, fb, 4),
        "counterfeit conservation failure",
    )
    # Modulo three this shear becomes the standard reflection: two contrast
    # coordinates route independently. The full integer echo is still literal.
    modular: Mat = ((1, 3), (0, -1))
    ma, mb = rows(modular, J), rows(modular, J, -1)
    echo(ma, mb, 4)
    check(
        check_gain(ma, mb, sample, mod_three, 1), "all 3^4 residue inputs must conserve"
    )
    check(
        mod_three(I[0]) > 0 and apply(ma, apply(ma, I[0])) == (3, 0),
        "nonzero stock and nonzero raw double",
    )
    check(
        all(mod_three(apply(ma, apply(ma, x))) == 0 for x in sample),
        "nonfaithful modular dark double",
    )
    check(no_quadratic(ma, mb, 4), "nonzero residual quadratic unexpectedly survived")
    # Nonsquare g=2; (A±B)/2 need not be integral. Nonzero s=-1.
    na, nb = J, ((1, 0), (-2, -1))
    echo(na, nb, 2)
    check(
        no_quadratic(na, nb, 2) and apply(na, apply(na, I[0])) == (-1, 0),
        "nonsquare raw obstruction",
    )
    # Common quarter-turn after every mixer: all port counts are unchanged
    # in these tests, but the echo is NEGATIVE swap and T+ is not scalar.
    pa: Mat = (scaled(-1, a[1]), a[0])
    pb: Mat = (scaled(-1, b[1]), b[0])
    echo(pa, pb, -4)
    check(
        rows(pa, pb) == ((0, -2), (2, 0))
        and all(squares(apply(pa, apply(pa, x))) == 4 * squares(x) for x in sample),
        "port counts alone are not a literal positive echo",
    )
    print(
        "Same-port shutter, emitted fraction at minimal gain: normalized sum block ±I gives 1/4, orthogonal reflection 0 despite equal open counts on the tested input."
    )
    print(
        "Shear counterfeit gives 1/4 but fails conservation; a conserved modulo-three stock sees zero despite a nonzero returned vector."
    )
    print(
        "Nonsquare literal gain obstruction checked; negative phased swap can mimic counts. A coherent shutter, full-state echo and port gain are supplied."
    )
    calibrated_echo_benchmark(a, b, c, d)
    print(
        "Separate calibrated norm benchmark: both axes split 1/2, yet a skew echo returns 49/2500 after the shutter and sends 49/50 of a diagonal input to the first port on one pass."
    )


if __name__ == "__main__":
    main()
