"""What active opposition cancellation does, and does not, supply as readout.

RECORD CONTRACT. Import the three oppositions/sheet of
probe_three_opposition_origin.py. For nonnegative species counts n_(i,+/-),
put d_i=n_(i,+)-n_(i,-), N=sum n. On one parity sheet, with sign rows V,
h=(N*1+Vd)/2. V^T V=4I and V^T 1=0, hence sum h^2=N^2+sum d^2.
Exhaustively deleting one opposite pair at a time has a unique COUNT normal
form: only |d_i| records of the appropriate sign survive. It requires exactly
sum_i min(n_i+,n_i-) serial deletion events. Which addressed records survive
need not be unique. A physical deletion rule and inaccessible/irrelevant
deletion products are extra resources, not consequences of a passive chart.

The surviving SAME-AXIS ordered address pairs, including self-pairs, have
cardinality Q=sum d_i^2. This is genuinely nonnegative and background-free
on this contrast quotient: no B is subtracted. It constructs a count without
assuming a dot product, but CHOOSES ordered pairs as the counted objects.
Single survivors give L1, and other tuple lengths give other positive counts.
The centered native T below is just a signed permutation, so those rival
counts survive too. No uniqueness/selection of the quadratic law follows.
Without self-pairs one gets sum |d_i|(|d_i|-1), not Q. A Cartesian ticket
set is not automatically a material stock of clicks or conserved particles.

ONE-ORIGIN TWO-PORT CONTRACT. The centered four real coordinates are
delta=Vd/2, only THREE dimensional. Split them as ports (delta0,delta1) and
(delta2,delta3). The earlier normalized native T=M/2 restricts to
d'=(d2,d1,-d0); selecting this active oriented operation is not supplied by
the primitive's unordered oppositions (whose natural unary maps were I/O).
The corresponding port weights are
 W0=[d0^2+(d1+d2)^2]/2, W1=[d0^2+(d1-d2)^2]/2.
Axis-square totals alone cannot recover these sign-sensitive cross terms:
d=(0,1,+/-1) gives identical axis tickets but opposite bright ports.
A POSITIVE CONSTRUCTION exists if extra sign-sensitive routing/fanout and
annihilation are supplied: make streams (d0,d1+d2)|(d0,d1-d2), cancel within
each, and count their pairs. This gives integer counts (2W0,2W1), with
common gain two. It is an active circuit, not passive leg sampling.
This is one sufficient circuit, not a minimal-resource theorem.

After cancellation the physical compatibility histogram is
h_min=(||d||_1*1+Vd)/2. Its common offset is signal-dependent, not a surviving
uniform DARK background. Nevertheless d=(0,1,1) has h_min=(2,0,1,1): the
desired second port is dark while its raw legs still contain two records.
Linear leg counts are (2,2), squared-leg counts (4,2), versus desired (2,0).
A complete histogram census reconstructs d; finite leg sampling does not
thereby supply an active cancellation/census device or the desired readout.

FOUR-QUADRATURE WALL AND ESCAPE. A balanced opposition stock can have
h=(k,k,k,k), arbitrarily large raw four-coordinate stock, yet cancel to
zero. If those four raw values/deviations are meant to be the earlier FULL
two-complex-port additive carrier, its uniform axis has been lost. In fact
z=(1,-1,1,-1) and its common complex quarter-turn Jz=(1,1,1,1) have the same
full port weights (2,2), but contrast-only Q changes 4 -> 0. One cannot
retain that carrier/phase contract while declaring this axis vacuum.
A nonlinear projective phase gauge is a different possible contract, not
excluded by dimension alone; it needs reference/gauge choices, is singular
where its reference vanishes, and does not preserve the supplied additive
superposition code automatically.

Two independently addressed origin copies are one sufficient additive
escape: use two contrasts per port and fix each third contrast to zero.
The old raw M has a positive integer lift to +/- species, with sign-dependent
fanout, and cancellation after that lift yields exactly the signed M output.
All 625 inputs in [-2,2]^4 below give port-ticket gain four. This imports
the cross-copy coupling and keeps an explicitly restricted four-dimensional
code; it does not select the code/spectator weights or derive that gate.
Squaring BEFORE combining loses interference: inputs (1,0)|(0,+/-1) have
the same initial port tickets (1,1), but after M give (8,0) versus (0,8).
Separate first-order routing would give (4,4). No fixed routing matrix on
the initial port-ticket totals can implement both outputs.

CONGRUENCE BOUNDARY. Cancellation commutes with all 48 opposition-preserving
species permutations, but only 48 of all 720 permutations preserve this
quotient. For a general positive additive substitution A, the precise
condition is q A(e_i+ + e_i-)=0 for every neutral pair. Reassociation that
preserves the SAME h automatically preserves N and d, so it is SAFE on this
quotient, even though hidden packet correlations differ. Do not assert the
opposite. Type-sensitive future maps or moving opposite partners to DIFFERENT
cells can break local neutrality; the latter preserves global d but changes
the sum of local Q from zero to two. Local neutral deletion is a dynamical
congruence only for an explicitly restricted context class.

READOUT WALL. Finite serial cancellation has unbounded cost at fixed d if
arbitrarily many neutral pairs may be added; bounded-rate parallelism trades
time for capacity. Generating/counting tickets is still not selecting one
outcome. Uniform ticket selection is a supplied rule; one reused uniform
seed can have the right one-shot share but correlated trials. No iid law,
observer/competition mechanism, unique outcome, Born rule or full QM follows.
This is an active escape/port-domain audit, not a repetition of the earlier
color-only finite-sampling bound or PORT_STOCK_ORIGIN's stronger gain theorem.

Run: python3 -B -O -m scripts.probe_opposition_readout
"""

from __future__ import annotations

import sys
from collections import defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import permutations, product
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_port_stock_origin import Quarter
from scripts.probe_three_opposition_origin import SHEET, hist

Vector = tuple[int, ...]
Stock = tuple[int, ...]
Matrix = tuple[Vector, ...]
Ticket = tuple[int, int, int, int]
V: Matrix = tuple(tuple(1 if x % 2 == 0 else -1 for x in row) for row in SHEET)
ROOT = Quarter(0, -1, 1)
READOUT: Matrix = ((1, 0, 0), (0, 1, 1), (1, 0, 0), (0, 1, -1))


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def contrast(stock: Stock) -> Vector:
    need(
        len(stock) % 2 == 0 and min(stock, default=0) >= 0, "nonnegative paired species"
    )
    return tuple(stock[i] - stock[i + 1] for i in range(0, len(stock), 2))


def canonical(vector: Vector) -> Stock:
    return tuple(count for d in vector for count in (max(d, 0), max(-d, 0)))


def reduced(stock: Stock) -> Stock:
    return canonical(contrast(stock))


def deletion_count(stock: Stock) -> int:
    return sum(min(stock[i], stock[i + 1]) for i in range(0, len(stock), 2))


@cache
def normal_forms(stock: Stock) -> frozenset[Stock]:
    answers: set[Stock] = set()
    for i in range(0, len(stock), 2):
        if stock[i] and stock[i + 1]:
            after = list(stock)
            after[i] -= 1
            after[i + 1] -= 1
            answers.update(normal_forms(tuple(after)))
    return frozenset(answers or {stock})


def tickets(vector: Vector) -> set[Ticket]:
    return {
        (axis, int(value < 0), i, j)
        for axis, value in enumerate(vector)
        for i, j in product(range(abs(value)), repeat=2)
    }


def dot(a: Vector, b: Vector) -> int:
    return sum(x * y for x, y in zip(a, b, strict=True))


def apply(matrix: Matrix, vector: Vector) -> Vector:
    return tuple(dot(row, vector) for row in matrix)


def permute(stock: Stock, permutation: Vector) -> Stock:
    answer = [0] * len(stock)
    for i, target in enumerate(permutation):
        answer[target] += stock[i]
    return tuple(answer)


def positive_lift(matrix: Matrix, stock: Stock) -> Stock:
    """Explicit additive signed-substitution resource; never negative counts."""
    need(all(len(row) * 2 == len(stock) for row in matrix), "lift dimensions")
    answer = [0] * (2 * len(matrix))
    for output, row in enumerate(matrix):
        for incoming, coefficient in enumerate(row):
            for sign in range(2):
                answer[2 * output + (sign ^ int(coefficient < 0))] += (
                    abs(coefficient) * stock[2 * incoming + sign]
                )
    return tuple(answer)


def native(vector: Vector) -> Vector:
    left, right = ROOT.mix((vector[0], vector[1]), (vector[2], vector[3]))
    return left + right


M: Matrix = tuple(
    zip(*(native(tuple(int(i == j) for i in range(4))) for j in range(4)), strict=True)
)


def chart_weights(vector: Vector) -> tuple[F, F]:
    delta = tuple(F(x, 2) for x in apply(V, vector))
    return sum((x * x for x in delta[:2]), F(0)), sum((x * x for x in delta[2:]), F(0))


def port_tickets(vector: Vector) -> tuple[int, int]:
    need(len(vector) == 4, "two real coordinates per port")
    return len(tickets(vector[:2])), len(tickets(vector[2:]))


def cancellation_and_chart_checks() -> tuple[int, int, int]:
    need(
        tuple(
            sum(V[k][i] * V[k][j] for k in range(4))
            for i, j in product(range(3), repeat=2)
        )
        == tuple(4 * int(i == j) for i, j in product(range(3), repeat=2)),
        "contrast frame",
    )
    need(all(sum(row[j] for row in V) == 0 for j in range(3)), "missing uniform axis")
    fibers: defaultdict[Vector, list[Stock]] = defaultdict(list)
    cases = 0
    for stock in product(range(4), repeat=6):
        d, n = contrast(stock), sum(stock)
        h, after = hist(stock, SHEET), reduced(stock)
        need(normal_forms(stock) == {after}, "count confluence")
        need(2 * deletion_count(stock) == n - sum(abs(x) for x in d), "serial cost")
        need(
            tuple(2 * value for value in h) == tuple(n + x for x in apply(V, d)),
            "compatibility chart",
        )
        need(
            sum(x * x for x in h) == n * n + len(tickets(d)),
            "raw versus contrast square",
        )
        need(
            tuple(a - b for a, b in zip(h, hist(after, SHEET), strict=True))
            == (deletion_count(stock),) * 4,
            "neutral deletion removes a uniform histogram layer",
        )
        fibers[h].append(stock)
        cases += 1
    for stocks in fibers.values():
        need(
            len({contrast(s) for s in stocks})
            == len({reduced(s) for s in stocks})
            == 1,
            "same-chart reassociation is safe on the quotient",
        )
    # Two possible addressed + survivors after deleting one of two + records.
    need(
        {tuple(j for j in range(2) if j != cancelled) for cancelled in range(2)}
        == {(0,), (1,)},
        "count confluence is not addressed confluence",
    )
    return cases, len(fibers), sum(len(stocks) > 1 for stocks in fibers.values())


def symmetry_and_context_checks() -> int:
    allowed = []
    for permutation in permutations(range(6)):
        neutral_images = []
        for axis in range(3):
            pair = tuple(int(i // 2 == axis) for i in range(6))
            neutral_images.append(contrast(permute(pair, permutation)))
        descends = all(not any(d) for d in neutral_images)
        need(
            descends
            == all(
                permutation[2 * i + 1] == (permutation[2 * i] ^ 1) for i in range(3)
            ),
            "neutral-generator criterion",
        )
        if descends:
            allowed.append(permutation)
            for stock in product(range(2), repeat=6):
                need(
                    reduced(permute(stock, permutation))
                    == permute(reduced(stock), permutation),
                    "opposition automorphisms commute with reduction",
                )
    need(len(allowed) == 48, "exact quotient-preserving permutation class")
    pair = (1, 1, 0, 0, 0, 0)
    bad = (0, 2, 1, 3, 4, 5)
    need(
        len(tickets(contrast(permute(pair, bad)))) == 2
        and reduced(permute(reduced(pair), bad)) == (0,) * 6,
        "type-sensitive context makes a neutral stock bright",
    )
    # Reversible transport of the minus record to the other cell. This is
    # not a same-local-chart signed permutation, despite global neutrality.
    two_cells = pair + (0,) * 6
    routing = list(range(12))
    routing[1], routing[7] = routing[7], routing[1]
    separated = permute(two_cells, tuple(routing))
    local = contrast(separated[:6]), contrast(separated[6:])
    need(
        tuple(x + y for x, y in zip(*local, strict=True)) == (0, 0, 0)
        and sum(len(tickets(d)) for d in local) == 2,
        "global cancellation does not imply local darkness",
    )
    need(
        not any(permute(reduced(two_cells), tuple(routing))), "delete before transport"
    )
    return len(allowed)


def centered_port_checks() -> int:
    cases = 0
    for d in product(range(-3, 4), repeat=3):
        turned = (d[2], d[1], -d[0])
        need(
            apply(M, apply(V, d)) == tuple(2 * x for x in apply(V, turned)),
            "native centered restriction",
        )
        need(
            sum(abs(x) for x in d) == sum(abs(x) for x in turned)
            and sum(x**4 for x in d) == sum(x**4 for x in turned),
            "nonquadratic rival stocks",
        )
        expected = (
            F(d[0] ** 2 + (d[1] + d[2]) ** 2, 2),
            F(d[0] ** 2 + (d[1] - d[2]) ** 2, 2),
        )
        need(
            chart_weights(d) == expected and sum(expected) == len(tickets(d)),
            "chart-specific port weights",
        )
        routed = positive_lift(READOUT, canonical(d))
        need(
            sum(routed) == 2 * sum(abs(x) for x in d),
            "readout circuit supplies two-fold fanout",
        )
        positive_counts = port_tickets(contrast(reduced(routed)))
        need(
            tuple(F(count) for count in positive_counts)
            == tuple(2 * weight for weight in expected),
            "positive active port readout",
        )
        cases += 1
    a, b = (0, 1, 1), (0, 1, -1)
    need(
        tuple(x * x for x in a) == tuple(x * x for x in b)
        and chart_weights(a) == (F(2), F(0))
        and chart_weights(b) == (F(0), F(2)),
        "axis totals forget port phase",
    )
    h = hist(canonical(a), SHEET)
    need(
        h == (2, 0, 1, 1) and (sum(h[:2]), sum(h[2:])) == (2, 2),
        "raw leg dark-port counterexample",
    )
    need(
        (sum(x * x for x in h[:2]), sum(x * x for x in h[2:])) == (4, 2),
        "raw square is not contrast-port square",
    )
    need(
        len(tickets((1, 0, 0))) == 1
        and not {
            (axis, sign, i, j) for axis, sign, i, j in tickets((1, 0, 0)) if i != j
        },
        "ordered self-pairs are an extra counting choice",
    )
    return cases


def four_quadrature_and_two_copy_checks() -> int:
    z = (1, -1, 1, -1)
    quarter = (-z[1], z[0], -z[3], z[2])

    def projected_q(value: Vector) -> F:
        return sum(
            (F(sum(V[k][j] * value[k] for k in range(4)), 2) ** 2 for j in range(3)),
            F(0),
        )

    need(
        port_tickets(z) == port_tickets(quarter) == (2, 2)
        and (projected_q(z), projected_q(quarter)) == (F(4), F(0)),
        "full complex-phase contract fails",
    )
    for k in range(1, 9):
        stock = (k, k, 0, 0, 0, 0)
        need(
            hist(stock, SHEET) == (k,) * 4
            and not any(reduced(stock))
            and sum(x * x for x in hist(stock, SHEET)) == 4 * k * k,
            "unbounded lost common axis",
        )
    active = (0, 1, 3, 4)
    matrix = tuple(
        tuple(
            M[active.index(i)][active.index(j)]
            if i in active and j in active
            else int(i == j)
            for j in range(6)
        )
        for i in range(6)
    )
    cases = 0
    for value in product(range(-2, 3), repeat=4):
        code = (value[0], value[1], 0, value[2], value[3], 0)
        source = canonical(code)
        out = contrast(reduced(positive_lift(matrix, source)))
        expected = native(value)
        need(
            native(expected) == tuple(4 * x for x in value[2:] + value[:2]),
            "full encoded raw two-pass port exchange",
        )
        phase_rotated = (-value[1], value[0], -value[3], value[2])
        need(
            port_tickets(phase_rotated) == port_tickets(value),
            "two-origin code retains the whole-port complex phase contract",
        )
        need(
            out == (expected[0], expected[1], 0, expected[2], expected[3], 0),
            "two-origin additive code",
        )
        need(
            sum(port_tickets(expected)) == 4 * sum(port_tickets(value)),
            "raw port ticket gain four",
        )
        # Add neutral records at every coordinate. The positive lift respects
        # this congruence; output reduction, not unreduced equality, is required.
        padded = tuple(x + 1 for x in source)
        need(
            reduced(positive_lift(matrix, padded))
            == reduced(positive_lift(matrix, reduced(padded))),
            "signed lift descends through neutral deletion",
        )
        cases += 1
    plus, minus = (1, 0, 0, 1), (1, 0, 0, -1)
    need(
        port_tickets(plus) == port_tickets(minus) == (1, 1)
        and port_tickets(native(plus)) == (8, 0)
        and port_tickets(native(minus)) == (0, 8),
        "interference requires signs before ticketization",
    )
    for value, expected_population in ((plus, (4, 0)), (minus, (0, 4))):
        population = positive_lift(M, canonical(value))
        need(
            (sum(population[:4]), sum(population[4:])) == (4, 4),
            "first-order unsigned output populations do not show this interference",
        )
        cancelled = reduced(population)
        need(
            (sum(cancelled[:4]), sum(cancelled[4:])) == expected_population,
            "opposition-sensitive output cancellation is the additional operation",
        )
    separately = tuple(
        sum(port_tickets(native(v))[j] for v in ((1, 0, 0, 0), (0, 0, 0, 1)))
        for j in range(2)
    )
    need(
        separately == (4, 4), "separate positive branches miss cancellation cross terms"
    )
    return cases


def time_and_sampling_controls() -> None:
    for padding in range(20):
        stock = (padding, padding, 1, 0, 1, 0)
        need(
            deletion_count(stock) == padding and contrast(stock) == (0, 1, 1),
            "unbounded serial work at fixed signal",
        )
    # A supplied uniform seed gives the counting share, but reusing it does
    # not supply independent trials; deterministic seed zero is biased.
    labels = (0, 0, 1)
    one = F(labels.count(0), len(labels))
    repeated_zero_pair = F(sum(label == 0 for label in labels), len(labels))
    need(
        one == repeated_zero_pair == F(2, 3) and repeated_zero_pair != one * one,
        "stock cardinalities do not imply iid outcomes",
    )
    need(labels[0] == 0 and one != 1, "fixed first-ticket selector is not uniform")


def main() -> None:
    stocks, fibers, hidden = cancellation_and_chart_checks()
    symmetries = symmetry_and_context_checks()
    centered = centered_port_checks()
    full = four_quadrature_and_two_copy_checks()
    time_and_sampling_controls()
    print(
        f"Count cancellation: {stocks} stocks, unique normal forms; {fibers} histogram fibers ({hidden} nontrivial) preserve the same contrast under reassociation."
    )
    print(
        f"Only {symmetries}/720 species permutations preserve neutral deletion; separated opposite records give global contrast zero but local Q=2."
    )
    print(
        f"Centered native T: {centered} cases, d'=(d2,d1,-d0). Positive routed/cancelled readout gives 2W0,2W1; bare axis squares or raw leg counts do not."
    )
    print(
        "Dark-port control: d=(0,1,1), compatible h=(2,0,1,1); intended weights(2,0), raw port counts(2,2), raw-square counts(4,2)."
    )
    print(
        f"Full-carrier phase control Q:4->0 exposes the missing common axis. Two supplied origin copies plus the old signed gate pass {full} four-quadrature gain checks; signs distinguish outputs(8,0)/(0,8) from incoherent(4,4)."
    )
    print(
        "Ordered-pair counting and active cancellation/routing are resources; no unique quadratic law, finite universal cancellation time, iid sampler, unique outcome or Born rule is derived."
    )


if __name__ == "__main__":
    main()
