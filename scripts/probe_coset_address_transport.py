"""Serial compatibility and translation boundary for Gaussian coset addresses.

Assign nonzero z the records Z[i]/z Z[i], and zero no records by convention.
The index is det(z, i*z)=|z|^2. For nonzero z,w, multiplication by z and
reduction modulo z give the short exact sequence

    0 -> Z[i]/(w) -> Z[i]/(zw) -> Z[i]/(z) -> 0.

A representative of q=u mod z gives the set encoding
(q, ((u-q)/z) mod w), decoded by q+z*r mod zw. The encoding depends on the
choice of representatives and need not be additive. At z=w=2 the middle
group is (Z/4)^2; a lift of (1,0) in (Z/2)^2 always has order four,
so there is no additive section.

The unnormalized mixer has diagonal A=1+i and off-diagonal B=1-i;
it multiplies total squared norm by four. Require a bijection from every
input record with a four-element seed stock to output records. Suppose
real and imaginary address translations act on each output quotient by
addition, preserve output ports, and act on the four seeds at a fixed
unit input port without changing that action when the other input changes.
In (1,0) the output is (1+i,1-i), two orbits of size two; in (1,1) it
is (2,2), two orbits of size four. The same invariant seed stock at port
zero cannot match both: an equivariant bijection preserves whole orbits.
This does not need the two input ports to use the same seed actions.

Dropping equivariance allows synthetic finite bijections. Pulling the
output action back along such a bijection allows equivariance if the
input action can change with the entire input. Other address structures
or translations that do not preserve those stocks are untested. This
counts supplied address records; it does not derive detector outcomes.
"""

from collections import Counter
from itertools import permutations, product

Gaussian = tuple[int, int]
Address = tuple[int, Gaussian]
Seeded = tuple[int, Gaussian, int]
Permutation = tuple[int, ...]

ZERO: Gaussian = (0, 0)
ONE: Gaussian = (1, 0)
I: Gaussian = (0, 1)


def check(condition: bool, message: str) -> None:
    """Keep all checks active under python -O."""
    if not condition:
        raise AssertionError(message)


def add(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] + b[0], a[1] + b[1]


def sub(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] - b[0], a[1] - b[1]


def mul(a: Gaussian, b: Gaussian) -> Gaussian:
    x, y = a
    u, v = b
    return x * u - y * v, x * v + y * u


def norm(a: Gaussian) -> int:
    return a[0] ** 2 + a[1] ** 2


def conjugate(a: Gaussian) -> Gaussian:
    return a[0], -a[1]


def reduce(u: Gaussian, z: Gaussian) -> Gaussian:
    """Canonical integer point in z*[0,1)^2, using exact floor coordinates."""
    n = norm(z)
    check(n > 0, "cannot reduce modulo zero here")
    x, y = mul(conjugate(z), u)
    return sub(u, mul(z, (x // n, y // n)))


def div_exact(u: Gaussian, z: Gaussian) -> Gaussian:
    n = norm(z)
    check(n > 0, "cannot divide by zero")
    x, y = mul(conjugate(z), u)
    check(x % n == y % n == 0, "not a multiple of the Gaussian generator")
    return x // n, y // n


def reps(z: Gaussian) -> tuple[Gaussian, ...]:
    if z == ZERO:
        return ()  # No records, not the infinite additive quotient by (0).
    vertices = (ZERO, z, mul(I, z), add(z, mul(I, z)))
    x, y = zip(*vertices, strict=True)
    box = product(range(min(x), max(x) + 1), range(min(y), max(y) + 1))
    out = tuple((a, b) for a, b in box if reduce((a, b), z) == (a, b))
    det = z[0] * vertices[2][1] - z[1] * vertices[2][0]
    check(det == len(out) == norm(z) and ZERO in out, "integer index")
    return out


def check_serial() -> int:
    cases: tuple[Gaussian, ...] = (ONE, I, (2, 0), (1, 1), (-2, 1), (3, -2))
    for z, w in product(cases, repeat=2):
        source, fiber, base = reps(mul(z, w)), reps(w), reps(z)
        zw = mul(z, w)
        injection = {reduce(mul(z, r), zw) for r in fiber}
        check(injection == {u for u in source if reduce(u, z) == ZERO}, "kernel")
        check(len(injection) == len(fiber), "injectivity")
        check(
            dict(Counter(reduce(u, z) for u in source))
            == dict.fromkeys(base, len(fiber)),
            "base and fiber sizes",
        )

        encode = {
            u: (q, reduce(div_exact(sub(u, q), z), w))
            for u in source
            for q in (reduce(u, z),)
        }
        decode = {
            (q, r): reduce(add(q, mul(z, r)), zw) for q, r in product(base, fiber)
        }
        check(
            len(encode) == len(decode) == len(base) * len(fiber)
            and encode == {v: k for k, v in decode.items()},
            "serial synthetic inverse",
        )
        check(
            all(
                reduce(add(u, v), z) == reduce(add(reduce(u, z), reduce(v, z)), z)
                for u in source
                for v in (ONE, I)
            ),
            "reduction additive on generating translations",
        )
    check(reps(ZERO) == (), "zero input has no records")
    return len(cases) ** 2


def check_nonsplit() -> None:
    two, four = (2, 0), (4, 0)
    lifts = tuple(u for u in reps(four) if reduce(u, two) == ONE)
    check(len(lifts) == 4 and reduce(add(ONE, ONE), two) == ZERO, "base order two")
    for u in lifts:
        doubled = reduce(add(u, u), four)
        check(
            doubled != ZERO and reduce(add(doubled, doubled), four) == ZERO,
            "every lift has order four",
        )
    # The choice of small representatives carries into the fiber under addition.
    check(reduce(add(ONE, ONE), four) == two, "nonadditive digit section")


def mixer(x: Gaussian, y: Gaussian) -> tuple[Gaussian, Gaussian]:
    a, b = (1, 1), (1, -1)
    out = add(mul(a, x), mul(b, y)), add(mul(b, x), mul(a, y))
    check(sum(map(norm, out)) == 4 * (norm(x) + norm(y)), "native mixer gain")
    return out


def addresses(values: tuple[Gaussian, Gaussian]) -> tuple[Address, ...]:
    return tuple((p, u) for p, z in enumerate(values) for u in reps(z))


def translation(
    labels: tuple[Address, ...], values: tuple[Gaussian, Gaussian], t: Gaussian
) -> Permutation:
    index = {label: i for i, label in enumerate(labels)}
    return tuple(index[p, reduce(add(u, t), values[p])] for p, u in labels)


def compose(x: Permutation, y: Permutation) -> Permutation:
    return tuple(x[j] for j in y)


def profile(x: Permutation, y: Permutation) -> tuple[int, ...]:
    check(compose(x, y) == compose(y, x), "Z^2 generator actions must commute")
    left = set(range(len(x)))
    sizes = []
    while left:
        frontier = [min(left)]
        reached: set[int] = set()
        while frontier:
            i = frontier.pop()
            if i not in reached:
                reached.add(i)
                frontier.extend((x[i], y[i]))
        left -= reached
        sizes.append(len(reached))
    return tuple(sorted(sizes))


def fixture(
    other: Gaussian,
) -> tuple[tuple[Seeded, ...], tuple[int, ...], tuple[int, ...]]:
    inputs = (ONE, other)
    outputs = mixer(*inputs)
    seeds = tuple((p, u, k) for p, u in addresses(inputs) for k in range(4))
    out = addresses(outputs)
    forward = dict(zip(seeds, out, strict=True))
    inverse = dict(zip(out, seeds, strict=True))
    check(
        all(inverse[forward[s]] == s for s in seeds), "synthetic inverse without action"
    )
    x, y = (translation(out, outputs, t) for t in (ONE, I))
    full_profile = profile(x, y)

    # Pull back output translation along the synthetic bijection. These
    # two fixtures happen to preserve the port-zero stock under pullback.
    stock = tuple(s for s in seeds if s[0] == 0)
    index = {s: i for i, s in enumerate(stock)}
    out_index = {a: i for i, a in enumerate(out)}
    actions = []
    for g in (x, y):
        pulled = {s: inverse[out[g[out_index[forward[s]]]]] for s in seeds}
        check(all(pulled[s] in index for s in stock), "port-zero stock invariant")
        actions.append(tuple(index[pulled[s]] for s in stock))
    return stock, full_profile, profile(actions[0], actions[1])


def check_actions() -> int:
    stock_one, out_one, first_one = fixture(ZERO)
    stock_two, out_two, first_two = fixture(ONE)
    check(stock_one == stock_two and len(stock_one) == 4, "same first-port stock")
    check(out_one == (2, 2) and out_two == (4, 4), "output action orbits")
    check(first_one == (2, 2) and first_two == (4,), "pulled-back action must change")

    # For the double-unit input an invariant subset of size four in a union
    # of two size-four transitive orbits is exactly one entire output orbit.
    actions = Counter(
        profile(x, y)
        for x, y in product(permutations(range(4)), repeat=2)
        if compose(x, y) == compose(y, x)
    )
    check(sum(actions.values()) == 120, "all commuting pairs on four seeds")
    check(
        actions[first_one] > 0 and actions[first_two] > 0,
        "each profile separately possible",
    )
    return sum(actions.values())


def main() -> None:
    serial = check_serial()
    check_nonsplit()
    actions = check_actions()
    print(f"{serial} serial quotients: exact count, fibers, synthetic inverse.")
    print("z=w=2: every lift of (1,0) has order four; no additive section.")
    print(
        f"{actions} commuting seed actions: no fixed one fits output profiles (2,2) and (4,4)."
    )
    print("Synthetic transport passes when the action can change with the input.")


if __name__ == "__main__":
    main()
