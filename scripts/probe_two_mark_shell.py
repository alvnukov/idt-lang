"""Exact finite two-mark shell fixture, not a derivation of quantum mechanics.

The native input is two signed marks on distinct rails, with four ordered
rails grouped into two ports and two quadratures per port. Readout chooses
one mark uniformly exactly once and reports its port. The native dynamics
use signed rail permutations and a sign-dependent complement operation;
they never square amplitudes, postselect, or call the analytic oracle.

The separate oracle identifies this supplied finite gadget with six Pauli
axis rays. That dictionary is a comparison, not a native Hilbert primitive
or a physical identification of an exchange gate or device.

Conditional dimension note (not a machine-checked universal theorem): let an
orthogonal A preserve the FULL shell R_n = {+/-e_i +/-e_j : i != j}, n >= 2.
Writing A e_i = (u+v)/2 for orthogonal shell roots u=A(e_i+e_j),
v=A(e_i-e_j) shows that each column is either monomial or has four entries
+/-1/2. If one column has half entries on four coordinates, integrality of
A(e_i +/-e_j) forces every other column to have half entries on exactly
the same support. Unit norm excludes extra coordinates. Full rank then
forces n <= 4, while that support requires n >= 4. Thus only n=4 permits
a non-monomial orthogonal automorphism under these explicit premises.
The bounded exact controls below are not a proof for arbitrary n, nor a
statement about nonlinear, stochastic, or restricted-orbit dynamics.
"""

from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product
from typing import NamedTuple


class Mark(NamedTuple):
    rail: int
    sign: int


Record = tuple[Mark, Mark]
Vector = tuple[int, ...]
ComplexQ = tuple[Fraction, Fraction]
Amplitude = tuple[ComplexQ, ...]
Frequency = tuple[Fraction, ...]

H = ((1, -1, 1, 1), (1, 1, -1, 1), (1, 1, 1, -1), (-1, 1, 1, 1))


def require(condition: bool, failure: object) -> None:
    """Remain active under python -O."""
    if not condition:
        raise AssertionError(failure)


def canonical(first: Mark, second: Mark) -> Record:
    require(first.rail != second.rail, "marks require distinct rails")
    require(first.sign in (-1, 1) and second.sign in (-1, 1), "invalid sign")
    return (first, second) if first.rail < second.rail else (second, first)


def raw_shell(rails: int) -> tuple[Record, ...]:
    return tuple(
        canonical(Mark(i, a), Mark(j, b))
        for i, j in combinations(range(rails), 2)
        for a, b in product((-1, 1), repeat=2)
    )


def encode(record: Record, rails: int = 4) -> Vector:
    require(all(0 <= mark.rail < rails for mark in record), "rail out of bounds")
    return tuple(next((m.sign for m in record if m.rail == i), 0) for i in range(rails))


def native_gate(record: Record) -> Record:
    """Cyclic left shift; negate opposite signs, complement equal signs."""
    require(all(0 <= m.rail < 4 for m in record), "gate has exactly four rails")
    shifted = canonical(*(Mark((m.rail - 1) % 4, m.sign) for m in record))
    if shifted[0].sign != shifted[1].sign:
        return canonical(*(Mark(m.rail, -m.sign) for m in shifted))
    occupied = {m.rail for m in shifted}
    empty = tuple(i for i in range(4) if i not in occupied)
    return canonical(*(Mark(i, shifted[0].sign) for i in empty))


def native_quarter(record: Record, port: int, direction: int = 1) -> Record:
    """Local quarter rotation (re,im)->(-im,re), or its inverse."""
    require(port in (0, 1) and direction in (-1, 1), "invalid local plate")
    moved: list[Mark] = []
    for mark in record:
        if mark.rail // 2 != port:
            moved.append(mark)
        else:
            quadrature = mark.rail % 2
            sign = mark.sign * (1 if quadrature == 0 else -1) * direction
            moved.append(Mark(2 * port + 1 - quadrature, sign))
    return canonical(*moved)


def global_quarter(record: Record) -> Record:
    return native_quarter(native_quarter(record, 0), 1)


def draw_mark_port(record: Record, chosen_mark: int) -> int:
    """Single readout event; chosen_mark is one uniform bit supplied once."""
    require(chosen_mark in (0, 1), "readout requires one fair mark selection")
    return record[chosen_mark].rail // 2


def native_frequency(record: Record, ports: int = 2) -> Frequency:
    counts = Counter(draw_mark_port(record, choice) for choice in (0, 1))
    require(all(port < ports for port in counts), "port out of bounds")
    return tuple(Fraction(counts[port], 2) for port in range(ports))


def phase_class(record: Record) -> Vector:
    orbit = []
    for _ in range(4):
        orbit.append(encode(record))
        record = global_quarter(record)
    return min(orbit)


def native_orbit(start: Record) -> set[Record]:
    seen = {start}
    queue = deque([start])
    while queue:
        record = queue.popleft()
        for image in (
            native_gate(record),
            native_quarter(record, 0),
            native_quarter(record, 1),
        ):
            if image not in seen:
                seen.add(image)
                queue.append(image)
    return seen


def qcomplex(real: int, imag: int = 0) -> ComplexQ:
    return Fraction(real), Fraction(imag)


def add(a: ComplexQ, b: ComplexQ) -> ComplexQ:
    return a[0] + b[0], a[1] + b[1]


def multiply(a: ComplexQ, b: ComplexQ) -> ComplexQ:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def analytic_encoding(record: Record, ports: int = 2) -> Amplitude:
    vector = encode(record, 2 * ports)
    return tuple(qcomplex(vector[2 * p], vector[2 * p + 1]) for p in range(ports))


def analytic_gate(state: Amplitude, first: int = 0, second: int = 1) -> Amplitude:
    """Exact supplied complex comparison U, separate from native execution."""
    a, b = state[first], state[second]
    alpha, beta = (
        (Fraction(1, 2), Fraction(1, 2)),
        (
            Fraction(1, 2),
            Fraction(-1, 2),
        ),
    )
    image = list(state)
    image[first] = add(multiply(alpha, a), multiply(beta, b))
    image[second] = add(multiply(beta, a), multiply(alpha, b))
    return tuple(image)


def analytic_quarter(state: Amplitude, port: int) -> Amplitude:
    image = list(state)
    image[port] = multiply(qcomplex(0, 1), image[port])
    return tuple(image)


def norm_square(z: ComplexQ) -> Fraction:
    return z[0] ** 2 + z[1] ** 2


def analytic_frequency(state: Amplitude) -> Frequency:
    total = sum(map(norm_square, state), Fraction(0))
    require(total > 0, "zero analytic vector")
    return tuple(norm_square(z) / total for z in state)


def pauli_ray(state: Amplitude) -> str:
    """Labels in the comparison dictionary, not a device interpretation."""
    a, b = state
    if b == qcomplex(0):
        return "Z+"
    if a == qcomplex(0):
        return "Z-"
    for label, phase in (
        ("X+", qcomplex(1)),
        ("X-", qcomplex(-1)),
        ("Y+", qcomplex(0, 1)),
        ("Y-", qcomplex(0, -1)),
    ):
        if b == multiply(phase, a):
            return label
    raise AssertionError(("not an axis ray", state))


def analytic_oracle_check(shell: tuple[Record, ...], start: Record) -> dict[str, int]:
    """Exhaust all transitions, full orbit, frequencies and phase dictionary."""
    encoded = {analytic_encoding(record) for record in shell}
    for record in shell:
        state = analytic_encoding(record)
        require(
            analytic_frequency(state) == native_frequency(record), "frequency oracle"
        )
        require(
            analytic_gate(state) == analytic_encoding(native_gate(record)), "U oracle"
        )
        for port in (0, 1):
            require(
                analytic_quarter(state, port)
                == analytic_encoding(native_quarter(record, port)),
                "local quarter oracle",
            )
    seen = {analytic_encoding(start)}
    queue = deque(seen)
    while queue:
        state = queue.popleft()
        for image in (
            analytic_gate(state),
            analytic_quarter(state, 0),
            analytic_quarter(state, 1),
        ):
            if image not in seen:
                seen.add(image)
                queue.append(image)
    require(seen == encoded, "full oracle orbit differs from raw shell")
    labels: dict[Vector, set[str]] = {}
    for record in shell:
        labels.setdefault(phase_class(record), set()).add(
            pauli_ray(analytic_encoding(record))
        )
    require(
        all(len(group) == 1 for group in labels.values()), "phase-dependent ray label"
    )
    rays = Counter(pauli_ray(analytic_encoding(record)) for record in shell)
    require(set(rays) == {"X+", "X-", "Y+", "Y-", "Z+", "Z-"}, "six rays")
    require(set(rays.values()) == {4}, "four raw records per ray")
    return dict(sorted(rays.items()))


def native_checks(shell: tuple[Record, ...], start: Record) -> None:
    require(len(shell) == len(set(shell)) == 24, "24 distinct signed records")
    require(
        all(
            sum(a * b for a, b in zip(H[i], H[j], strict=True)) == (4 if i == j else 0)
            for i in range(4)
            for j in range(4)
        ),
        "H/2 is not orthogonal",
    )
    require(
        set(map(native_gate, shell)) == set(shell), "native gate is not a permutation"
    )
    require(native_orbit(start) == set(shell), "native orbit is not the full shell")
    classes = Counter(map(phase_class, shell))
    require(
        len(classes) == 6 and set(classes.values()) == {4}, "quarter-phase quotient"
    )
    for record in shell:
        vector = encode(record)
        image = encode(native_gate(record))
        total = sum(vector)
        require(
            tuple(2 * y for y in image)
            == tuple(total - 2 * vector[(i + 1) % 4] for i in range(4)),
            "integer check of y_i=S/2-x_(i+1)",
        )
        require(
            tuple(2 * y for y in image)
            == tuple(sum(a * b for a, b in zip(row, vector, strict=True)) for row in H),
            "native gate differs from supplied H/2",
        )
        require(
            encode(native_gate(native_gate(record))) == vector[2:] + vector[:2],
            "U squared is not the port swap",
        )
        require(
            native_quarter(native_quarter(record, 0), 0, -1) == record,
            "quarter inverse",
        )
        negative = canonical(*(Mark(m.rail, -m.sign) for m in record))
        require(native_frequency(negative) == native_frequency(record), "global sign")
        require(
            native_frequency(global_quarter(record)) == native_frequency(record),
            "phase",
        )
        require(
            native_gate(global_quarter(record)) == global_quarter(native_gate(record)),
            "gate does not descend to the common-quarter quotient",
        )


def corner_checks(start: Record) -> dict[str, Frequency]:
    split = native_gate(start)
    same = native_quarter(native_quarter(split, 0), 0)
    opposite = native_quarter(native_quarter(split, 0), 0, -1)
    relative_pi = native_quarter(native_quarter(split, 0), 1, -1)
    global_phase = global_quarter(split)
    rows = {
        "same-arm same-handed pair": native_frequency(native_gate(same)),
        "same-arm opposite-handed pair": native_frequency(native_gate(opposite)),
        "opposite-arm opposite-handed pair": native_frequency(native_gate(relative_pi)),
        "common quarter on both arms": native_frequency(native_gate(global_phase)),
    }
    port_zero = (Fraction(1), Fraction(0))
    port_one = (Fraction(0), Fraction(1))
    require(rows["same-arm same-handed pair"] == port_zero, "same-handed corner")
    require(rows["same-arm opposite-handed pair"] == port_one, "opposite-handed corner")
    require(rows["opposite-arm opposite-handed pair"] == port_zero, "relative pi")
    require(rows["common quarter on both arms"] == port_one, "common phase")
    return rows


def three_port_resource_wall() -> Frequency:
    """Only a single raw record is excluded; mixtures are explicitly allowed."""
    start = (qcomplex(1, 1), qcomplex(0), qcomplex(0))
    first = analytic_gate(start)
    require(first == (qcomplex(0, 1), qcomplex(1), qcomplex(0)), "first 3-port step")
    second = analytic_gate(first, 1, 2)
    require(
        second
        == (
            qcomplex(0, 1),
            (Fraction(1, 2), Fraction(1, 2)),
            (Fraction(1, 2), Fraction(-1, 2)),
        ),
        "second 3-port step",
    )
    target = analytic_frequency(second)
    require(target == (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)), "target")
    shell = raw_shell(6)
    require(
        all(native_frequency(record, 3) != target for record in shell),
        "single record wall",
    )
    first_record = canonical(Mark(0, 1), Mark(2, 1))
    second_record = canonical(Mark(0, 1), Mark(4, 1))
    mixture = tuple(
        (a + b) / 2
        for a, b in zip(
            native_frequency(first_record, 3),
            native_frequency(second_record, 3),
            strict=True,
        )
    )
    require(mixture == target, "equal mixture must realize the same marginal")
    return target


def dimension_controls() -> dict[int, int]:
    """Exact doubled-coordinate controls for n=2..6, not an all-n proof."""
    counts = {}
    for dimension in range(2, 7):
        roots = {encode(record, dimension) for record in raw_shell(dimension)}
        doubled_roots = {tuple(2 * x for x in root) for root in roots}
        candidates: list[Vector] = [
            tuple(2 * sign if i == j else 0 for i in range(dimension))
            for j in range(dimension)
            for sign in (-1, 1)
        ]
        for support in combinations(range(dimension), 4):
            for signs in product((-1, 1), repeat=4):
                entries = dict(zip(support, signs, strict=True))
                candidates.append(tuple(entries.get(i, 0) for i in range(dimension)))
        require(all(sum(x * x for x in v) == 4 for v in candidates), "unit columns")
        counts[dimension] = len(candidates)
        if dimension < 4:
            require(len(candidates) == 2 * dimension, "unexpected half column")
            continue
        half = (1, 1, 1, 1) + (0,) * (dimension - 4)
        compatible = []
        for other in candidates:
            if all(
                tuple(a + sign * b for a, b in zip(half, other, strict=True))
                in doubled_roots
                for sign in (-1, 1)
            ):
                compatible.append(other)
        require(len(compatible) == 6, "half-column partners")
        require(
            all(
                tuple(i for i, x in enumerate(v) if x) == (0, 1, 2, 3)
                for v in compatible
            ),
            "compatible column has different support",
        )
    return counts


def main() -> None:
    shell = raw_shell(4)
    start = canonical(Mark(0, 1), Mark(1, 1))
    native_checks(shell, start)
    rays = analytic_oracle_check(shell, start)
    corners = corner_checks(start)
    target = three_port_resource_wall()
    dimensions = dimension_controls()
    print("PASS: native 24-record orbit, permutation, H/2 identity, U^2 port swap")
    print(f"PASS: separate exact oracle; common-quarter quotient rays={rays}")
    for name, frequency in corners.items():
        print(f"PASS: {name}: port frequencies={tuple(map(str, frequency))}")
    print(
        f"WALL: one raw two-mark 3-port record cannot realize {tuple(map(str, target))}"
    )
    print("PASS: an equal mixture of two raw records DOES realize that same marginal")
    print(
        f"PASS: conditional dimension note; exact n=2..6 unit-column controls={dimensions}"
    )
    print(
        "BOUNDARY: supplied finite gadget; no physical device/exchange claim or full QM closure"
    )


if __name__ == "__main__":
    main()
