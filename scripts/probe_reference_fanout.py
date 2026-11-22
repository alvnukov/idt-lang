"""Exact controls for branching relative to a supplied reference b.

For a transparent square root of swap T, let T(x,b)=(A(x),B(x)).
Since T commutes with its square, it commutes with swap. Also T(b,b)=(b,b).
If x != b and B(x)=b, then T(A(x),b)=(b,x), so A(B(x))=b and B(A(x))=x.
If instead A(x)=b, then T(b,B(x))=(b,x); commuting with swap gives
T(B(x),b)=(x,b), so A(B(x))=x and B(A(x))=b. If no nonblank x leaks
to b in either port, both crossed paths preserve nonblankness; at b
both return b. Thus faithful single-level branching is equivalent to
agreement of the two crossed return-to-b predicates for every x. Raw
commutation of A and B suffices, but only the return predicates must agree.

This finite probe supplies fresh reference inputs, port routing and reference
comparators. It does not derive ready resources, physical records in disjoint
channels, exclusivity or outcome actualization, or establish a primitive.
Repeating finite classical labels is not cloning arbitrary quantum states.
Thresholded weights are model readouts, not experimental click statistics.
"""

from collections import Counter
from collections.abc import Callable, Iterator
from fractions import Fraction
from itertools import permutations, product

Pair = tuple[int, int]
Gate = dict[Pair, Pair]
GateSignature = tuple[Pair, ...]
Matching = tuple[tuple[Pair, Pair], ...]
ComplexRational = tuple[Fraction, Fraction]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def swap(pair: Pair) -> Pair:
    return pair[1], pair[0]


def matchings(edges: tuple[Pair, ...]) -> Iterator[Matching]:
    if not edges:
        yield ()
        return
    first, *rest = edges
    for index, partner in enumerate(rest):
        for tail in matchings(tuple(rest[:index] + rest[index + 1 :])):
            yield ((first, partner), *tail)


def transparent_roots(states: tuple[int, ...]) -> Iterator[Gate]:
    """Off-diagonal T-cycles have length four because T² is swap.

    Each cycle pairs two unordered edges. Fix the representative a of the
    first edge and choose either orientation c of the other: the cycle
    must be (a, c, swap(a), swap(c)). This gives each root once.
    """
    edges = tuple((x, y) for x in states for y in states if x < y)
    for matching in matchings(edges):
        for orientations in product((0, 1), repeat=len(matching)):
            gate = {(x, x): (x, x) for x in states}
            for (a, c), reverse_c in zip(matching, orientations, strict=True):
                if reverse_c:
                    c = swap(c)
                gate.update({a: c, c: swap(a), swap(a): swap(c), swap(c): a})
            yield gate


def routed_fanout(
    gate: Callable[[int, int], Pair], x: int, b: int, rounds: int
) -> tuple[Pair, tuple[int, ...]]:
    endpoints = gate(x, b)
    retained: list[int] = []
    for _ in range(rounds):
        left, right = gate(endpoints[0], b), gate(endpoints[1], b)
        endpoints = left[0], right[1]
        retained.extend((left[1], right[0]))
    return endpoints, tuple(retained)


def four_state_controls() -> None:
    # Two and three labels give one and three unordered edges, respectively.
    # Neither odd edge set can be partitioned into pairs.
    check(list(transparent_roots((0,))) == [{(0, 0): (0, 0)}], "bad trivial root")
    for size in (2, 3):
        check(not list(transparent_roots(tuple(range(size)))), "unexpected small root")

    states = tuple(range(4))
    pairs = tuple((x, y) for x in states for y in states)
    seen: set[GateSignature] = set()
    globally_faithful: list[tuple[Gate, list[int]]] = []
    outcomes: Counter[tuple[bool, bool]] = Counter()
    witness: tuple[int, int, int, Pair, Pair] | None = None

    for gate_index, gate in enumerate(transparent_roots(states), start=1):
        check(gate.keys() == set(pairs), "incomplete root table")
        signature = tuple(gate[pair] for pair in pairs)
        check(signature not in seen, "duplicate root table")
        seen.add(signature)
        check(
            all(gate[gate[pair]] == swap(pair) for pair in pairs), "not a square root"
        )
        check(all(gate[x, x] == (x, x) for x in states), "not transparent")
        faithful_refs = 0
        commuting_refs: list[int] = []
        for b in states:
            first = {x: gate[x, b][0] for x in states}
            second = {x: gate[x, b][1] for x in states}
            faithful, returns_agree, commute = True, True, True
            for x in states:
                children = (first[x], second[x])
                ab, ba = first[second[x]], second[first[x]]
                leak = x != b and b in children
                agree = (ab == b) == (ba == b)
                if leak:
                    expected = (b, x) if second[x] == b else (x, b)
                    check(
                        not agree and (ab, ba) == expected,
                        "incorrect crossed leak witness",
                    )
                    if witness is None:
                        witness = gate_index, b, x, children, (ab, ba)
                faithful = faithful and not leak
                returns_agree = returns_agree and agree
                commute = commute and ab == ba
            check(faithful == returns_agree, "return agreement differs from branching")
            outcomes[faithful, commute] += 1
            faithful_refs += faithful
            if commute:
                commuting_refs.append(b)
        if faithful_refs == len(states):
            globally_faithful.append((gate, commuting_refs))

    check(len(seen) == 120 and outcomes.total() == 480, "unexpected enumeration size")
    check(
        outcomes == {(False, False): 288, (True, True): 24, (True, False): 168},
        f"unexpected classification: {outcomes}",
    )
    if witness is None:
        raise ValueError("no leak witness")
    print("Four labels: 120 transparent roots, 480 gate/reference pairs.")
    print("Faithful branching: 192 pass (24 commute exactly; 168 do not); 288 fail.")
    gate_index, b, x, children, crossed = witness
    print(
        f"Leak witness at root {gate_index}: b={b}, x={x}, "
        f"(A(x), B(x))={children}, (A(B(x)), B(A(x)))={crossed}."
    )
    canonical_controls(states, pairs, globally_faithful)


def canonical_controls(
    states: tuple[int, ...],
    pairs: tuple[Pair, ...],
    candidates: list[tuple[Gate, list[int]]],
) -> None:
    """Test a gate-table reference selector, not a preparation procedure.

    For the unique commuting b, the output on (x,b), x != b, is the other
    two non-b labels y,z. For a conserved sum w(x)+w(b), subtract w(b)
    from each one-site term to get d_x=d_y+d_z for all three labels.
    Subtracting any two equations gives equality of those two deviations
    over the reals; then d=2d forces d=0. No positivity is needed.
    This rules out a nonconstant real additive one-site weight on a closed
    gate pair, not all conservation laws or larger substrates.
    """
    check(len(candidates) == 8, "wrong number of globally faithful roots")
    signatures = {tuple(gate[pair] for pair in pairs) for gate, _ in candidates}
    representative = candidates[0][0]
    orbit: set[GateSignature] = set()
    relabelings = tuple(permutations(states))
    check(len(relabelings) == 24, "wrong number of four-label relabelings")
    for relabel in relabelings:
        renamed = {
            (relabel[x], relabel[y]): (relabel[a], relabel[c])
            for (x, y), (a, c) in representative.items()
        }
        orbit.add(tuple(renamed[pair] for pair in pairs))
    check(orbit == signatures, "globally faithful roots are not exactly one orbit")

    labels = set(states)
    for gate, commuting_refs in candidates:
        check(len(commuting_refs) == 1, "canonical reference is not unique")
        b = commuting_refs[0]
        nonblank = labels - {b}
        for x, y in pairs:
            if x != y:
                outputs = gate[x, y]
                check(set(outputs) == labels - {x, y}, "wrong output complement")
                check(gate[y, x] == swap(outputs), "reversal did not swap output ports")
        first = {x: gate[x, b][0] for x in states}
        second = {x: gate[x, b][1] for x in states}
        for x in nonblank:
            check(
                {first[x], second[x]} == nonblank - {x},
                "wrong pair for real-weight wall",
            )
            check(
                first[second[x]] == second[first[x]] == x,
                "canonical port cycles are not inverse",
            )

        def apply(x: int, y: int, table: Gate = gate) -> Pair:
            return table[x, y]

        for x in states:
            endpoints, retained = routed_fanout(apply, x, b, rounds=2)
            check(
                endpoints == (x, x), "canonical port decoders did not recover the label"
            )
            check(
                len(retained) == 4
                and all((side == b) == (x == b) for side in retained),
                "canonical retained outputs are incorrect",
            )

    print("Four labels are minimal beyond the trivial one-label root.")
    print(
        "Eight roots branch faithfully for every reference and form one relabeling orbit."
    )
    print(
        "Each has one commuting reference with inverse three-cycles off that reference."
    )
    print(
        "Three applications per path recover x, with five fresh b inputs and four retained outputs."
    )
    # By induction over gate applications, an all-x stock remains all x.
    print(
        "The table selects b; gates and rewiring cannot prepare b from an all-x stock for x != b."
    )
    print("Two distinct nonblank inputs produce b once; reversing them swaps its port.")
    print(
        "No nonconstant real additive one-site weight is conserved by these closed pairs."
    )


def f5_gate(x: int, y: int) -> Pair:
    return (4 * x + 2 * y) % 5, (2 * x + 4 * y) % 5


def f5_fanout(x: int, b: int) -> tuple[Pair, tuple[int, ...]]:
    # Relative to b, repeat multiplier 4 on the left and 2 on the right.
    # Their fourth powers are both 1 mod 5.
    return routed_fanout(f5_gate, x, b, rounds=3)


def f5_controls() -> None:
    states = tuple(range(5))
    pairs = tuple(product(states, repeat=2))
    for x, b in pairs:
        outputs = f5_gate(x, b)
        check(f5_gate(*outputs) == (b, x), "F5 gate is not a square root")
        check(sum(outputs) % 5 == (x + b) % 5, "F5 gate changed the label sum")
        check(
            (outputs == (b, b)) if x == b else b not in outputs, "F5 reference leaked"
        )
        endpoints, retained = f5_fanout(x, b)
        check(endpoints == (x, x), "F5 port decoders did not recover the label")
        check(len(retained) == 6, "F5 retained outputs missing")
        # Inputs were x and seven copies of b. A clean copy would leave
        # six more b labels beside the two x endpoints, violating the sum.
        check((sum(retained) - 6 * b) % 5 == (b - x) % 5, "F5 ancilla sum is wrong")
        if x != b:
            check(retained != (b,) * 6, "F5 unexpected clean copy")

    orbit: set[Pair] = set()
    for multiplier, offset in product(range(1, 5), states):
        relabel = tuple((multiplier * x + offset) % 5 for x in states)
        orbit.add((relabel[0], relabel[1]))
        for x, y in pairs:
            a, c = f5_gate(x, y)
            check(
                f5_gate(relabel[x], relabel[y]) == (relabel[a], relabel[c]),
                "F5 affine relabeling changed the gate",
            )
    check(orbit == set(permutations(states, 2)), "F5 affine action is not transitive")
    print(
        "F5: all 25 label/reference inputs branch correctly; affine relabeling is transitive"
    )
    print(
        "on ordered distinct labels. Four gate applications along each path recover x;"
    )
    print(
        "six other outputs are retained. Conservation here is modulo 5, not physical energy."
    )

    for p, q in permutations(states, 2):
        for x, b in pairs:
            endpoints, retained = f5_fanout(x, b)
            left, right = f5_gate(endpoints[0], p), f5_gate(endpoints[1], q)
            active = (left[0] != p, right[0] != q)
            check(active == (x != p, x != q), "F5 mismatch channels are incorrect")
            check(
                sum(active) == (1 if x in (p, q) else 2),
                "F5 promised-pair control failed",
            )
            check(
                (sum(retained) + sum(left) + sum(right) - x - 7 * b - p - q) % 5 == 0,
                "F5 mismatch channels did not retain the full output sum",
            )
    print(
        "F5 mismatch channels: exactly one active for promised p or q; both active otherwise."
    )


def add(x: ComplexRational, y: ComplexRational) -> ComplexRational:
    return x[0] + y[0], x[1] + y[1]


def multiply(x: ComplexRational, y: ComplexRational) -> ComplexRational:
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c


HALF = Fraction(1, 2)
COEFFICIENT = (HALF, HALF)
CONJUGATE = (HALF, -HALF)
ZERO = (Fraction(), Fraction())
ONE = (Fraction(1), Fraction())


def complex_gate(
    x: ComplexRational, y: ComplexRational
) -> tuple[ComplexRational, ComplexRational]:
    return (
        add(multiply(COEFFICIENT, x), multiply(CONJUGATE, y)),
        add(multiply(CONJUGATE, x), multiply(COEFFICIENT, y)),
    )


def squared_norm(x: ComplexRational) -> Fraction:
    return x[0] ** 2 + x[1] ** 2


def complex_controls() -> None:
    for x, y in ((ONE, ZERO), (ZERO, ONE)):
        check(
            complex_gate(*complex_gate(x, y)) == (y, x),
            "complex gate is not a square root",
        )
    # The gate is complex-linear, so fixing (1,1) fixes the diagonal.
    check(complex_gate(ONE, ONE) == (ONE, ONE), "complex gate is not transparent")
    leaves = [ONE]
    for depth in range(1, 6):
        leaves = [child for leaf in leaves for child in complex_gate(leaf, ZERO)]
        weights = [squared_norm(leaf) for leaf in leaves]
        check(len(weights) == 2**depth, "complex tree lost an output")
        check(
            all(weight == Fraction(1, 2**depth) for weight in weights),
            "bad leaf weights",
        )
        check(sum(weights) == 1, "complex tree did not conserve total weight")
        detected = sum(weight >= Fraction(1, 16) for weight in weights)
        check(
            detected == (2**depth if depth <= 4 else 0),
            "unexpected detected leaf count",
        )
        if depth >= 4:
            print(
                f"Complex tree at depth {depth}: weight sum 1; "
                f"squared threshold 1/16 detects {detected}/{len(weights)}."
            )

    left, right = complex_gate(ONE, ZERO)
    ab, ba = complex_gate(right, ZERO)[0], complex_gate(left, ZERO)[1]
    threshold = Fraction(3, 4)
    # The crossed maps are complex-linear, so equality at 1 holds everywhere.
    check(ab == ba != ZERO, "complex crossed paths do not commute at the test input")
    check(
        squared_norm(ONE) >= threshold
        and squared_norm(left) == squared_norm(right) == HALF < threshold
        and squared_norm(ab) == squared_norm(ba) == Fraction(1, 4) < threshold,
        "complex coarse detector control failed",
    )
    print("Squared threshold 3/4: input detected, neither child detected.")
    print(
        "The crossed maps agree everywhere; this does not certify detector branching."
    )


def main() -> None:
    four_state_controls()
    f5_controls()
    complex_controls()


if __name__ == "__main__":
    main()
