"""Exact finite certificates for an operational unread-tick condition.

Supply finitely many nonnegative rational outcome matrices K_a and a row
distribution mu, with P=sum_a K_a row-stochastic. A record u has probability
mu K_u 1. An unread tick is the NONSELECTIVE instrument P, not an identity
operation. The strong premise is

    mu K_u (P-I) K_v 1 = 0    for every ordered prefix u and suffix v.

Reachable rows mu K_u and observable columns K_v 1 each span a space of
dimension <=d. Starting with mu and 1 and closing under the K_a produces
bases represented by words of length <=d-1. Testing the displayed bilinear
form on every basis pair is therefore a finite exact certificate of the
premise for this SUPPLIED matrix model, not an inference from finite data.

Why the premise implies a mixture of iid records:
1. P is a sum of the K_a. By linearity the premise remains valid with other
   unread gaps anywhere in either context. Telescoping permits arbitrary
   nonnegative numbers of unread ticks, independently in every gap, including
   the initial and final gaps.
2. Average each gap independently using A_N=(I+P+...+P^(N-1))/N. All finite
   averages still give the same record probability. The finite-state Cesaro
   limit Pi exists even for periodic P. Taking these finitely many limits
   gives mu Pi K_a Pi ... K_b Pi 1.
3. Pi's rows are mixtures of stationary rows pi_c on closed irreducible
   classes, with absorption probabilities as weights. Nonnegativity and
   sum K_a=P mean no K_a can leave a closed class. Consequently
   pi_c K_a Pi = p_c,a pi_c, where p_c,a=pi_c K_a 1. Each intervening Pi
   resets that class row; the result is a mixture of iid laws, with fixed
   weights w_c=mu h_c. These are the class masses of mu Pi, not its raw
   state-coordinate entries.
4. For h outcome labels, the SUM of same-label two-record probabilities is
   collision=sum_c w_c sum_a p_c,a^2. Its excess over 1/h is exactly
   sum_c w_c sum_a (p_c,a-1/h)^2. Thus collision=1/h forces uniform iid
   outcomes on every class with positive weight. Unvisited classes may be
   nonuniform. One selected label's pair probability does NOT suffice.

Neither mu P=mu nor pairwise chance collision alone implies the premise.
Raw K_a K_b need not commute, even when every observable record is iid.
This script checks rational basis/decomposition certificates and examples.
The general linear-span and Cesaro arguments above are analytical, not a
Lean proof; no empirical iid claim or microscopic randomness origin follows.
Operational iid does not identify shared versus refreshed hidden randomness.

Run: python3 -B -O -m scripts.probe_unread_tick_instruments
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from typing import Literal

Vector = tuple[F, ...]
Matrix = tuple[Vector, ...]
Word = tuple[int, ...]


def need(ok: bool, reason: str) -> None:
    """Executable checks remain enabled under -O."""
    if not ok:
        raise ValueError(reason)


def vector(*entries: int | F) -> Vector:
    return tuple(F(x) for x in entries)


def dot(row: Vector, column: Vector) -> F:
    return sum((x * y for x, y in zip(row, column, strict=True)), F(0))


def row_mul(row: Vector, matrix: Matrix) -> Vector:
    return tuple(
        sum((row[i] * matrix[i][j] for i in range(len(row))), F(0))
        for j in range(len(matrix))
    )


def col_mul(matrix: Matrix, column: Vector) -> Vector:
    return tuple(dot(row, column) for row in matrix)


def mat_mul(left: Matrix, right: Matrix) -> Matrix:
    return tuple(row_mul(row, right) for row in left)


def identity(size: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(size)) for i in range(size))


def mat_sub(left: Matrix, right: Matrix) -> Matrix:
    return tuple(
        tuple(x - y for x, y in zip(a, b, strict=True))
        for a, b in zip(left, right, strict=True)
    )


def sum_matrices(matrices: tuple[Matrix, ...]) -> Matrix:
    need(bool(matrices), "an outcome alphabet must be nonempty")
    size = len(matrices[0])
    return tuple(
        tuple(sum((m[i][j] for m in matrices), F(0)) for j in range(size))
        for i in range(size)
    )


@dataclass(frozen=True)
class Instrument:
    kernels: tuple[Matrix, ...]
    initial: Vector

    def __post_init__(self) -> None:
        size = len(self.initial)
        need(size > 0 and bool(self.kernels), "nonempty state space and alphabet")
        need(
            all(
                len(k) == size and all(len(row) == size for row in k)
                for k in self.kernels
            ),
            "matrix dimensions",
        )
        need(
            all(x >= 0 for k in self.kernels for row in k for x in row),
            "negative outcome entry",
        )
        need(
            all(x >= 0 for x in self.initial) and sum(self.initial, F(0)) == 1,
            "initial distribution",
        )
        need(
            all(sum(row, F(0)) == 1 for row in self.transition),
            "nonselective transition is not stochastic",
        )

    @property
    def transition(self) -> Matrix:
        return sum_matrices(self.kernels)


@dataclass(frozen=True)
class WordVector:
    word: Word
    value: Vector


class Span:
    """Exact echelon membership; retained word vectors are not modified."""

    def __init__(self) -> None:
        self.pivots: dict[int, Vector] = {}

    def add(self, value: Vector) -> bool:
        work = list(value)
        for pivot, row in sorted(self.pivots.items()):
            factor = work[pivot]
            work = [x - factor * y for x, y in zip(work, row, strict=True)]
        new_pivot = next((i for i, x in enumerate(work) if x), None)
        if new_pivot is None:
            return False
        scale = work[new_pivot]
        self.pivots[new_pivot] = tuple(x / scale for x in work)
        return True


def word_basis(
    initial: Vector, kernels: tuple[Matrix, ...], side: Literal["row", "column"]
) -> tuple[WordVector, ...]:
    span = Span()
    need(span.add(initial), "basis seed must be nonzero")
    basis = [WordVector((), initial)]
    cursor = 0
    while cursor < len(basis):
        item = basis[cursor]
        cursor += 1
        for label, kernel in enumerate(kernels):
            value = (
                row_mul(item.value, kernel)
                if side == "row"
                else col_mul(kernel, item.value)
            )
            word = item.word + (label,) if side == "row" else (label,) + item.word
            if span.add(value):
                basis.append(WordVector(word, value))
                need(len(basis) <= len(initial), "span dimension exceeds state count")
                need(
                    len(word) <= len(initial) - 1, "basis word exceeds dimension bound"
                )
    return tuple(basis)


@dataclass(frozen=True)
class GapWitness:
    prefix: Word
    suffix: Word
    difference: F


@dataclass(frozen=True)
class GapCertificate:
    rows: tuple[WordVector, ...]
    columns: tuple[WordVector, ...]
    failures: tuple[GapWitness, ...]

    @property
    def invariant(self) -> bool:
        return not self.failures


def unread_certificate(instrument: Instrument) -> GapCertificate:
    size = len(instrument.initial)
    rows = word_basis(instrument.initial, instrument.kernels, "row")
    columns = word_basis((F(1),) * size, instrument.kernels, "column")
    difference = mat_sub(instrument.transition, identity(size))
    failures = []
    for row in rows:
        for column in columns:
            value = dot(row_mul(row.value, difference), column.value)
            if value:
                failures.append(GapWitness(row.word, column.word, value))
    return GapCertificate(rows, columns, tuple(failures))


def solve(matrix: Matrix, rhs: Vector) -> Vector:
    """Unique rational square solve, checked again against the original input."""
    size = len(rhs)
    need(
        len(matrix) == size and all(len(row) == size for row in matrix),
        "linear solve dimensions",
    )
    work = [list(row) + [value] for row, value in zip(matrix, rhs, strict=True)]
    for j in range(size):
        pivot = next((i for i in range(j, size) if work[i][j]), None)
        need(pivot is not None, "singular stationary/absorption system")
        if pivot is None:
            raise ValueError("unreachable singular-system branch")
        work[j], work[pivot] = work[pivot], work[j]
        factor = work[j][j]
        work[j] = [x / factor for x in work[j]]
        for i in range(size):
            if i != j:
                factor = work[i][j]
                work[i] = [
                    x - factor * y for x, y in zip(work[i], work[j], strict=True)
                ]
    result = tuple(row[-1] for row in work)
    need(col_mul(matrix, result) == rhs, "linear solve replay")
    return result


def closed_classes(transition: Matrix) -> tuple[tuple[int, ...], ...]:
    size = len(transition)
    reach = [[i == j or transition[i][j] > 0 for j in range(size)] for i in range(size)]
    for k in range(size):
        for i in range(size):
            for j in range(size):
                reach[i][j] = reach[i][j] or (reach[i][k] and reach[k][j])
    seen: set[int] = set()
    result = []
    for i in range(size):
        if i in seen:
            continue
        component = tuple(j for j in range(size) if reach[i][j] and reach[j][i])
        seen.update(component)
        if all(
            transition[j][k] == 0
            for j in component
            for k in range(size)
            if k not in component
        ):
            result.append(component)
    need(bool(result), "finite stochastic graph has no closed class")
    return tuple(result)


@dataclass(frozen=True)
class Decomposition:
    classes: tuple[tuple[int, ...], ...]
    stationary: tuple[Vector, ...]
    absorption: tuple[Vector, ...]
    projector: Matrix


def cesaro_projector(transition: Matrix) -> Decomposition:
    """Construct from closed classes and transient hitting probabilities.

    This uses exact stationary/absorption equations, not a finite numerical
    convergence threshold. The identification with the Cesaro limit uses the
    finite Markov-chain decomposition argument stated in the module contract.
    """
    size = len(transition)
    classes = closed_classes(transition)
    recurrent = {i for component in classes for i in component}
    transient = tuple(i for i in range(size) if i not in recurrent)
    stationary = []
    absorption = []
    for component in classes:
        count = len(component)
        equations = tuple(
            tuple(transition[i][component[j]] - F(i == component[j]) for i in component)
            for j in range(count - 1)
        ) + ((F(1),) * count,)
        values = solve(equations, (F(0),) * (count - 1) + (F(1),))
        pi = tuple(
            values[component.index(i)] if i in component else F(0) for i in range(size)
        )
        need(all(x >= 0 for x in pi) and sum(pi, F(0)) == 1, "stationary probabilities")
        need(row_mul(pi, transition) == pi, "stationary row replay")
        stationary.append(pi)
        h = [F(i in component) for i in range(size)]
        if transient:
            equations = tuple(
                tuple(F(i == j) - transition[i][j] for j in transient)
                for i in transient
            )
            rhs = tuple(
                sum((transition[i][j] for j in component), F(0)) for i in transient
            )
            values = solve(equations, rhs)
            for i, value in zip(transient, values, strict=True):
                h[i] = value
        hit = tuple(h)
        need(all(0 <= x <= 1 for x in hit), "absorption probabilities")
        need(col_mul(transition, hit) == hit, "absorption harmonic replay")
        absorption.append(hit)
    need(
        all(sum((h[i] for h in absorption), F(0)) == 1 for i in range(size)),
        "eventual absorption normalization",
    )
    projector = tuple(
        tuple(
            sum(
                (h[i] * pi[j] for h, pi in zip(absorption, stationary, strict=True)),
                F(0),
            )
            for j in range(size)
        )
        for i in range(size)
    )
    need(mat_mul(transition, projector) == projector, "P Pi=Pi")
    need(mat_mul(projector, transition) == projector, "Pi P=Pi")
    need(mat_mul(projector, projector) == projector, "Pi idempotence")
    return Decomposition(classes, tuple(stationary), tuple(absorption), projector)


@dataclass(frozen=True)
class Mixture:
    weights: Vector
    responses: tuple[Vector, ...]
    collision: F
    uniform_on_support: bool


def mixture_certificate(
    instrument: Instrument, decomposition: Decomposition
) -> Mixture:
    """Always describes the Pi-averaged process; original law also needs gaps."""
    weights = tuple(dot(instrument.initial, hit) for hit in decomposition.absorption)
    responses = []
    for component, pi in zip(
        decomposition.classes, decomposition.stationary, strict=True
    ):
        chances = []
        for kernel in instrument.kernels:
            need(
                all(
                    kernel[i][j] == 0
                    for i in component
                    for j in range(len(pi))
                    if j not in component
                ),
                "outcome kernel escapes a closed class",
            )
            row = row_mul(pi, kernel)
            chance = sum(row, F(0))
            need(
                row_mul(row, decomposition.projector) == tuple(chance * x for x in pi),
                "closed-class reset identity",
            )
            chances.append(chance)
        need(
            all(x >= 0 for x in chances) and sum(chances, F(0)) == 1,
            "class outcome distribution",
        )
        responses.append(tuple(chances))
    need(all(x >= 0 for x in weights) and sum(weights, F(0)) == 1, "mixture weights")
    fair = F(1, len(instrument.kernels))
    collision = sum(
        (
            weight * sum((p * p for p in chance), F(0))
            for weight, chance in zip(weights, responses, strict=True)
        ),
        F(0),
    )
    excess = sum(
        (
            weight * sum(((p - fair) ** 2 for p in chance), F(0))
            for weight, chance in zip(weights, responses, strict=True)
        ),
        F(0),
    )
    uniform = all(
        weight == 0 or all(p == fair for p in chance)
        for weight, chance in zip(weights, responses, strict=True)
    )
    need(collision - fair == excess >= 0, "collision variance identity")
    need(
        (collision == fair) == uniform,
        "chance equality exactly means uniform on reached classes",
    )
    return Mixture(weights, tuple(responses), collision, uniform)


def record_probability(
    instrument: Instrument, word: Word, gaps: tuple[int, ...] | None = None
) -> F:
    actual_gaps = (0,) * (len(word) + 1) if gaps is None else gaps
    need(
        len(actual_gaps) == len(word) + 1 and all(g >= 0 for g in actual_gaps),
        "unread gap counts",
    )
    row = instrument.initial
    transition = instrument.transition
    for position, gap in enumerate(actual_gaps):
        for _ in range(gap):
            row = row_mul(row, transition)
        if position < len(word):
            need(0 <= word[position] < len(instrument.kernels), "unknown outcome label")
            row = row_mul(row, instrument.kernels[word[position]])
    return sum(row, F(0))


def inserted_probability(instrument: Instrument, word: Word, gap_matrix: Matrix) -> F:
    row = row_mul(instrument.initial, gap_matrix)
    for label in word:
        row = row_mul(row_mul(row, instrument.kernels[label]), gap_matrix)
    return sum(row, F(0))


def mixture_probability(mixture: Mixture, word: Word) -> F:
    total = F(0)
    for weight, response in zip(mixture.weights, mixture.responses, strict=True):
        value = weight
        for label in word:
            value *= response[label]
        total += value
    return total


def finite_cesaro(transition: Matrix, count: int) -> Matrix:
    need(count > 0, "positive averaging count")
    power = identity(len(transition))
    powers = []
    for _ in range(count):
        powers.append(power)
        power = mat_mul(power, transition)
    total = sum_matrices(tuple(powers))
    return tuple(tuple(x / count for x in row) for row in total)


def check_records(
    instrument: Instrument,
    gaps: GapCertificate,
    decomposition: Decomposition,
    mixture: Mixture,
) -> int:
    checked = 0
    for length in range(5):
        for word in product(range(len(instrument.kernels)), repeat=length):
            target = mixture_probability(mixture, word)
            need(
                inserted_probability(instrument, word, decomposition.projector)
                == target,
                "projected mixture replay",
            )
            if gaps.invariant:
                schedules = (
                    (0,) * (length + 1),
                    (1,) * (length + 1),
                    tuple(i % 3 for i in range(length + 1)),
                )
                for schedule in schedules:
                    need(
                        record_probability(instrument, word, schedule) == target,
                        "unread-gapped record replay",
                    )
                    checked += 1
            else:
                checked += 1
    for failure in gaps.failures:
        word = failure.prefix + failure.suffix
        schedule = tuple(int(i == len(failure.prefix)) for i in range(len(word) + 1))
        actual = record_probability(instrument, word, schedule) - record_probability(
            instrument, word
        )
        need(
            actual == failure.difference != 0, "basis witness as an operational record"
        )
    return checked


def analyse(
    name: str, instrument: Instrument
) -> tuple[GapCertificate, Decomposition, Mixture]:
    gaps = unread_certificate(instrument)
    decomposition = cesaro_projector(instrument.transition)
    mixture = mixture_certificate(instrument, decomposition)
    checked = check_records(instrument, gaps, decomposition, mixture)
    max_row = max(len(item.word) for item in gaps.rows)
    max_column = max(len(item.word) for item in gaps.columns)
    print(
        f"{name}: unread_invariant={gaps.invariant}; basis={len(gaps.rows)}x{len(gaps.columns)}, max_word_lengths={max_row},{max_column}; checked_records={checked}."
    )
    if gaps.invariant:
        print(
            f"  Original law is the certified class mixture; collision={mixture.collision}, uniform_on_reached_classes={mixture.uniform_on_support}."
        )
    else:
        witness = gaps.failures[0]
        print(
            f"  Visible unread tick: prefix={witness.prefix}, suffix={witness.suffix}, change={witness.difference}. Pi-mixture describes ONLY the averaged law."
        )
    return gaps, decomposition, mixture


def run() -> None:
    stationary = Instrument(
        ((vector(0, 1), vector(0, 0)), (vector(0, 0), vector(1, 0))),
        vector(F(1, 2), F(1, 2)),
    )
    need(
        row_mul(stationary.initial, stationary.transition) == stationary.initial,
        "stationary negative-control preparation",
    )
    gaps, decomposition, _ = analyse("stationary alternating", stationary)
    need(not gaps.invariant, "stationarity incorrectly accepted as the strong premise")
    need(record_probability(stationary, (0, 0)) == 0, "alternating adjacent record")
    need(
        record_probability(stationary, (0, 0), (0, 1, 0)) == F(1, 2),
        "visible middle gap",
    )
    need(
        finite_cesaro(stationary.transition, 2) == decomposition.projector,
        "exact two-tick Cesaro projector",
    )

    mixture_instrument = Instrument(
        (
            (vector(0, F(1, 8), F(3, 8)), vector(0, F(1, 4), 0), vector(0, 0, F(3, 4))),
            (vector(0, F(3, 8), F(1, 8)), vector(0, F(3, 4), 0), vector(0, 0, F(1, 4))),
        ),
        vector(1, 0, 0),
    )
    gaps, decomposition, mixture = analyse(
        "transient to biased closed classes", mixture_instrument
    )
    need(
        gaps.invariant and len(decomposition.classes) == 2, "reducible mixture premise"
    )
    need(mixture.weights == vector(F(1, 2), F(1, 2)), "absorption weights")
    need(
        mixture.collision == F(5, 8) and not mixture.uniform_on_support,
        "biased mixture not iid fair",
    )
    need(
        row_mul(mixture_instrument.initial, mixture_instrument.transition)
        != mixture_instrument.initial,
        "stationarity is not necessary",
    )
    need(
        decomposition.projector == mixture_instrument.transition,
        "one-step exact class reset",
    )

    noncommuting = Instrument(
        (
            (vector(F(1, 2), 0), vector(F(1, 2), 0)),
            (vector(0, F(1, 2)), vector(F(1, 2), 0)),
        ),
        vector(1, 0),
    )
    gaps, _, mixture = analyse("noncommuting observationally iid", noncommuting)
    first, second = noncommuting.kernels
    need(mat_mul(first, second) != mat_mul(second, first), "noncommuting raw kernels")
    need(gaps.invariant and mixture.uniform_on_support, "iid noncommuting control")
    need(
        len(gaps.columns) == 1 and mixture.collision == F(1, 2),
        "observable quotient control",
    )

    unreachable = Instrument(
        ((vector(F(1, 2), 0), vector(0, 1)), (vector(F(1, 2), 0), vector(0, 0))),
        vector(1, 0),
    )
    gaps, _, mixture = analyse("unvisited biased class", unreachable)
    need(
        gaps.invariant and mixture.uniform_on_support,
        "zero-weight classes must not spoil iid",
    )
    need(
        any(
            weight == 0 and chance != vector(F(1, 2), F(1, 2))
            for weight, chance in zip(mixture.weights, mixture.responses, strict=True)
        ),
        "unvisited nonuniform control",
    )

    rotor_kernels = tuple(
        tuple(
            tuple(F(j == (i + 1) % 4 and (i // 2) == label) for j in range(4))
            for i in range(4)
        )
        for label in range(2)
    )
    rotor = Instrument(rotor_kernels, (F(1, 4),) * 4)
    gaps, _, _ = analyse("stationary chance-pair rotor", rotor)
    need(row_mul(rotor.initial, rotor.transition) == rotor.initial, "stationary rotor")
    collision = sum((record_probability(rotor, (a, a)) for a in range(2)), F(0))
    need(
        collision == F(1, 2) and record_probability(rotor, (0, 0, 0)) == 0,
        "chance pairs do not imply iid",
    )
    need(not gaps.invariant, "rotor must fail unread-context premise")

    clock = Instrument(
        (
            tuple(tuple(F(i < 3 and j == i + 1) for j in range(4)) for i in range(4)),
            tuple(tuple(F(i == j == 3) for j in range(4)) for i in range(4)),
        ),
        vector(1, 0, 0, 0),
    )
    gaps, _, _ = analyse("basis-length saturation", clock)
    need(len(gaps.rows) == len(gaps.columns) == 4, "full basis dimensions")
    need(
        max(len(item.word) for item in gaps.rows)
        == max(len(item.word) for item in gaps.columns)
        == 3,
        "d-1 word bound attained",
    )
    try:
        Instrument(((vector(-1),), (vector(2),)), vector(1))
    except ValueError as exc:
        need(str(exc) == "negative outcome entry", "nonnegativity rejection reason")
    else:
        raise ValueError(
            "negative kernels accepted merely because their sum is stochastic"
        )
    print(
        "Exact finite certificates and controls passed. No physical iid, hidden-seed origin, or Lean-proof claim."
    )


if __name__ == "__main__":
    run()
