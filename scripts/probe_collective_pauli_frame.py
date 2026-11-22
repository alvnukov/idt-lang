"""Finite collective collision tests, without assuming an exchange sign.

SUPPLIED: an ordered m-copy tensor V^tensor(m), positive normalized states,
complete orthonormal one-copy modes, identical collective U^tensor(m), and
number-resolving unlabelled output occupations. Tensor structure, collective
control, norm probabilities, mode completeness and detector completeness
are not derived. Particle labels below only index the mathematical tensor;
the observable is sum_i binom(N_i,2), not particle-tagged coincidences.

Write Q_U=sum_i |u_i,u_i><u_i,u_i|. For native T on modes i,j the two
changed same-mode vectors span D_ij=(|ii>-|jj>)/sqrt(2) and
S_ij=(|ij>+|ji>)/sqrt(2). A bare basis plus complete-graph edge matchings
therefore has pair frame F >= Pi_sym. There are n settings for even n and
n+1 for odd n. Precisely,

    F = Pi_sym + (d0-1) Pi_diagonal + sum_{i<j} |D_ij><D_ij|,
    d0 = 1 for even n, 2 for odd n.

Off-diagonal symmetric eigenvalues are 1; diagonal-uniform eigenvalue is
d0; diagonal-traceless eigenvalues are d0+n/2. The kernel is Lambda^2 V.
For positive m-copy states, zero aggregate collisions in every setting
forces every pair symmetric projector to vanish, hence support in Lambda^m
V. This is a conditional inference from observations, not an assumed sign.

ROBUSTNESS: A_m=sum_{a<b} Pi_sym(ab) has kernel Lambda^m V. For n>=m>=2
its first nonzero eigenvalue is m/2. The transposition-class formula on
partition lambda is [binom(m,2)+sum_(i,j in lambda)(j-i)]/2; the sign
partition has eigenvalue zero and the next partition (2,1,...,1) gives
m/2. This representation-theoretic general argument is distinct from
the exact small regular-representation checks below. If E is the sum of
MEAN pair-collision counts over the settings, antisymmetric leakage <=2E/m.
For a setting average, multiply by the number of settings. If only the
probability of any collision is known, mean pair count is at most
binom(m,2) times that probability; it is not the same observable.

STRONGER FRAME, WITH AN IMPORTANT CONTROL BOUNDARY: for a fixed U let
A=(1/n)sum_ij |U_ij|^4. Twirling Q_U by independent fourth-root phases
and permutations gives A*Pi_diagonal + 2(1-A)/(n-1)*Pi_offdiag,sym.
If A<2/(n+1), a positive mixture with the bare basis gives exactly
2/(n+1)*Pi_sym. This is a weighted PROJECTIVE 2-design collision frame,
not a unitary 2-design of gate words. The short native words here have
A=5/12 for n=3 and 409/1280 for n=5, with bare weights 1/7 and 53/2613.

Raw native gates fix the uniform vector s. Therefore every raw native
basis has <s,s|Q_U|s,s>=1/n, not 2/(n+1). NO weighted raw-native basis
ensemble is this full design for n>1. Independent raw-mode phases are
not available. The exact design requires the explicit encoded construction:
logical mode j=(physical mode 2j - mode 2j+1)/sqrt(2). Within-pair T gives
logical phase i; parallel cross-pair T gates give logical native mixing;
their squares give logical permutations. The finite checks verify these
identities. Availability of this 2n-mode code, its preparation, and
complete logical-mode readout are additional supplied capabilities.
For that averaged design, leakage <= (n+1)*average_collision_count/m.

Controls: one bare-basis no-collision state can be symmetric; an orbital
antisymmetric state times an unobserved internal antisymmetric state is
TOTAL symmetric yet invisible to all orbital-only collision tests. Full
complete-mode control detects it. A single HBT dip or a click-only detector
does not establish the hypotheses. Existing PAULI_CHECKER_RESULT.md tests
a supplied declared exchange tensor; probe_two_particle_capacity.py gives
non-amplitude bunching controls. Neither is silently upgraded here.

This is finite exact evidence plus explicit mathematical arguments, not a
Lean proof, physical Pauli derivation, CAR, spin-statistics, or QM closure.
Run: python3 -B -O -m scripts.probe_collective_pauli_frame
"""

import sys
from collections import Counter
from collections.abc import Iterator
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.probe_raw_gate_reconstruction import (
    embed,
    eye,
    from_turn,
    matrix,
    mul,
    plus,
    rank,
    scale,
)

C = tuple[F, F]
Unitary = tuple[tuple[C, ...], ...]
Key = tuple[int, int, int, int]
Frame = dict[Key, C]
State = dict[tuple[int, ...], C]
ZERO: C = (F(0), F(0))
ONE: C = (F(1), F(0))
NATIVE = from_turn(((0, -1), (1, 0)))


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def add(x: C, y: C) -> C:
    return x[0] + y[0], x[1] + y[1]


def times(x: C, y: C) -> C:
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def scaled(a: F, x: C) -> C:
    return a * x[0], a * x[1]


def conjugate(x: C) -> C:
    return x[0], -x[1]


def weight(x: C) -> F:
    return x[0] ** 2 + x[1] ** 2


def put(frame: Frame, key: Key, value: C) -> None:
    total = add(frame.get(key, ZERO), value)
    if total == ZERO:
        frame.pop(key, None)
    else:
        frame[key] = total


def combine(a: Frame, b: Frame, factor: F = F(1)) -> Frame:
    result = dict(a)
    for key, value in b.items():
        put(result, key, scaled(factor, value))
    return result


def native_word(n: int, word: tuple[tuple[int, int], ...]) -> Unitary:
    raw = eye(2 * n)
    for edge in word:
        raw = mul(embed(n, edge, NATIVE), raw)
    denominator = 2 ** len(word)
    return tuple(
        tuple(
            (F(raw[2 * i][2 * j], denominator), F(raw[2 * i + 1][2 * j], denominator))
            for j in range(n)
        )
        for i in range(n)
    )


def pair_frame(u: Unitary) -> Frame:
    n = len(u)
    result: Frame = {}
    for row in u:
        vector = {
            (a, b): conjugate(times(row[a], row[b]))
            for a, b in product(range(n), repeat=2)
        }
        for (a, b), x in vector.items():
            for (c, d), y in vector.items():
                put(result, (a, b, c, d), times(x, conjugate(y)))
    return result


def symmetric_projector(n: int) -> Frame:
    result: Frame = {}
    for a, b in product(range(n), repeat=2):
        put(result, (a, b, a, b), (F(1, 2), F(0)))
        put(result, (a, b, b, a), (F(1, 2), F(0)))
    return result


def matchings(n: int) -> tuple[tuple[tuple[int, int], ...], ...]:
    size = n if n % 2 == 0 else n + 1
    labels = list(range(size))
    result = []
    for _ in range(size - 1):
        result.append(
            tuple(
                (a, b)
                for a, b in zip(
                    labels[: size // 2], reversed(labels[size // 2 :]), strict=True
                )
                if a < n and b < n
            )
        )
        labels = [labels[0], labels[-1], *labels[1:-1]]
    need(
        Counter(frozenset(edge) for row in result for edge in row)
        == Counter(frozenset(edge) for edge in combinations(range(n), 2)),
        "complete edge cover exactly once",
    )
    need(
        all(
            len({vertex for edge in row for vertex in edge}) == 2 * len(row)
            for row in result
        ),
        "parallel disjoint pairs",
    )
    return tuple(result)


def fast_frame(n: int) -> tuple[Frame, tuple[Unitary, ...]]:
    settings = (native_word(n, ()),) + tuple(
        native_word(n, row) for row in matchings(n)
    )
    actual: Frame = {}
    for u in settings:
        actual = combine(actual, pair_frame(u))
    expected = symmetric_projector(n)
    if n % 2:
        expected = combine(expected, pair_frame(settings[0]))
    for a, b in combinations(range(n), 2):
        for i, s in ((a, 1), (b, -1)):
            for j, t in ((a, 1), (b, -1)):
                put(expected, (i, i, j, j), (F(s * t, 2), F(0)))
    need(actual == expected, "exact native fast-frame PSD decomposition")
    need(
        all(
            value[1] == 0 and (2 * value[0]).denominator == 1
            for value in actual.values()
        ),
        "real half-integral frame",
    )
    twice = matrix(
        n * n, lambda i, j: int(2 * actual.get((i // n, i % n, j // n, j % n), ZERO)[0])
    )
    need(
        rank(twice) == n * (n + 1) // 2,
        "pair kernel is precisely the antisymmetric subspace",
    )
    return actual, settings


def partitions(total: int, ceiling: int) -> Iterator[tuple[int, ...]]:
    if total == 0:
        yield ()
    for first in range(min(total, ceiling), 0, -1):
        for rest in partitions(total - first, first):
            yield (first,) + rest


def class_gap_controls() -> None:
    for m in range(2, 10):
        values = {
            comb(m, 2) + sum(j - i for i, row in enumerate(shape) for j in range(row))
            for shape in partitions(m, m)
        }
        need(
            min(values) == 0 and min(value for value in values if value > 0) == m,
            "partition formula gap m for twice the symmetrizer sum",
        )
        if m > 4:
            continue
        words = tuple(permutations(range(m)))
        index = {word: i for i, word in enumerate(words)}
        moves = []
        for word in words:
            targets = []
            for a, b in combinations(range(m), 2):
                changed = list(word)
                changed[a], changed[b] = changed[b], changed[a]
                targets.append(index[tuple(changed)])
            moves.append(Counter(targets))
        operator = tuple(
            tuple(comb(m, 2) * int(i == j) + moves[j][i] for j in range(len(words)))
            for i in range(len(words))
        )
        polynomial = eye(len(words))
        for eigenvalue in sorted(values):
            polynomial = mul(
                polynomial, plus(operator, scale(-eigenvalue, eye(len(words))))
            )
        need(
            polynomial == scale(0, eye(len(words))),
            "regular-representation spectral polynomial",
        )
        need(
            rank(operator) == factorial(m) - 1,
            "only the sign vector has zero eigenvalue",
        )
        need(
            rank(plus(operator, scale(-m, eye(len(words))))) < len(words),
            "gap eigenvalue is attained",
        )


def collective(u: Unitary, state: State) -> State:
    copies = len(next(iter(state)))
    result: State = {}
    for output in product(range(len(u)), repeat=copies):
        amplitude = ZERO
        for source, value in state.items():
            term = value
            for a, b in zip(output, source, strict=True):
                term = times(term, u[a][b])
            amplitude = add(amplitude, term)
        if amplitude != ZERO:
            result[output] = amplitude
    return result


def mean_collisions(state: State, *, orbital: bool = False) -> F:
    norm = sum((weight(value) for value in state.values()), F(0))
    need(norm > 0, "nonzero positive-state control")
    return (
        sum(
            (
                sum(
                    comb(count, 2)
                    for count in Counter(
                        i // 2 if orbital else i for i in output
                    ).values()
                )
                * weight(value)
                for output, value in state.items()
            ),
            F(0),
        )
        / norm
    )


def readout_controls(settings: tuple[Unitary, ...]) -> None:
    symmetric: State = {(0, 1): ONE, (1, 0): ONE}
    need(mean_collisions(symmetric) == 0, "one basis does not exclude symmetric states")
    need(
        mean_collisions(collective(native_word(2, ((0, 1),)), symmetric)) == 1,
        "native mixed basis catches the false exclusion",
    )
    wedge: State = {}
    hook: State = {}
    for word in permutations(range(3)):
        sign = (-1) ** sum(word[a] > word[b] for a, b in combinations(range(3), 2))
        wedge[word] = (F(sign), F(0))
        coefficient = sign * (int(word[0] == 0) - int(word[0] == 1))
        if coefficient:
            hook[word] = (F(coefficient), F(0))
    wedge_total = sum((mean_collisions(collective(u, wedge)) for u in settings), F(0))
    hook_total = sum((mean_collisions(collective(u, hook)) for u in settings), F(0))
    need(
        wedge_total == 0 and hook_total == F(3, 2),
        "exact zero and sharp gap leakage controls",
    )
    leakage = F(1, 5)
    measured_sum = (1 - leakage) * wedge_total + leakage * hook_total
    need(F(2, 3) * measured_sum == leakage, "positive mixture saturates leakage <=2E/m")
    hidden: State = {
        (0, 3): ONE,
        (3, 0): ONE,
        (1, 2): (F(-1), F(0)),
        (2, 1): (F(-1), F(0)),
    }
    need(
        all(value == hidden[(b, a)] for (a, b), value in hidden.items()),
        "hidden-label control is total symmetric",
    )
    orbital_u = native_word(2, ((0, 1),))
    orbital_only = tuple(
        tuple(orbital_u[a // 2][b // 2] if a % 2 == b % 2 else ZERO for b in range(4))
        for a in range(4)
    )
    need(
        mean_collisions(collective(orbital_only, hidden), orbital=True) == 0,
        "unseen internal antisymmetry hides total symmetry",
    )
    need(
        mean_collisions(collective(native_word(4, ((0, 3),)), hidden)) == F(1, 2),
        "complete-mode native control detects it",
    )


def monomial_twirl(frame: Frame, n: int) -> Frame:
    # Fourth-root averaging kills every unequal occupation multiset: each
    # phase exponent difference is in {-2,-1,0,1,2}, with no nonzero multiple of 4.
    phases = (ONE, (F(0), F(1)), (F(-1), F(0)), (F(0), F(-1)))
    for exponent in range(-2, 3):
        total = ZERO
        for k in range(4):
            total = add(total, phases[(k * exponent) % 4])
        need(
            total == (F(4), F(0)) if exponent == 0 else total == ZERO,
            "exact phase character average",
        )
    retained = {
        key: value for key, value in frame.items() if sorted(key[:2]) == sorted(key[2:])
    }
    result: Frame = {}
    for permutation in permutations(range(n)):
        for (a, b, c, d), value in retained.items():
            put(
                result,
                (permutation[a], permutation[b], permutation[c], permutation[d]),
                scaled(F(1, factorial(n)), value),
            )
    return result


def encoded_controls(n: int) -> None:
    # Unnormalized difference embedding E; E^*E=2I. Coordinate operations
    # below certify an encoded implementation, not raw-mode phase availability.
    encoded = tuple(
        tuple(
            (1 if i // 2 % 2 == 0 else -1) * int(i // 4 == j // 2 and i % 2 == j % 2)
            for j in range(2 * n)
        )
        for i in range(4 * n)
    )
    for j in range(n):
        logical_phase = tuple(
            tuple(
                ((0, -1), (1, 0))[a % 2][b % 2]
                if a // 2 == b // 2 == j
                else int(a == b)
                for b in range(2 * n)
            )
            for a in range(2 * n)
        )
        physical = embed(2 * n, (2 * j, 2 * j + 1), NATIVE)
        need(
            mul(physical, encoded) == scale(2, mul(encoded, logical_phase)),
            "native encoded independent phase",
        )
    for a, b in combinations(range(n), 2):
        physical = mul(
            embed(2 * n, (2 * a, 2 * b), NATIVE),
            embed(2 * n, (2 * a + 1, 2 * b + 1), NATIVE),
        )
        logical = embed(n, (a, b), NATIVE)
        need(
            mul(physical, encoded) == scale(2, mul(encoded, logical)),
            "native encoded mixer and hence swap",
        )


def design_controls() -> tuple[tuple[int, F, F], ...]:
    results = []
    for n, word, expected_a, expected_bare in (
        (3, ((0, 1), (1, 2)), F(5, 12), F(1, 7)),
        (5, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0)), F(409, 1280), F(53, 2613)),
    ):
        u = native_word(n, word)
        a = sum((weight(value) ** 2 for row in u for value in row), F(0)) / n
        target = F(2, n + 1)
        need(a == expected_a and a < target, "fixed native IPR benchmark")
        frame = pair_frame(u)
        uniform_test = sum((value[0] for value in frame.values()), F(0)) / n**2
        need(
            uniform_test == F(1, n) and uniform_test != target,
            "raw uniform-sector no-design obstruction",
        )
        bare = pair_frame(native_word(n, ()))
        offdiag = combine(symmetric_projector(n), bare, F(-1))
        expected_twirl = combine(
            {key: scaled(a, value) for key, value in bare.items()},
            offdiag,
            2 * (1 - a) / (n - 1),
        )
        twirled = monomial_twirl(frame, n)
        need(twirled == expected_twirl, "exact monomial collision twirl")
        bare_weight = (target - a) / (1 - a)
        need(bare_weight == expected_bare, "positive exact bare-basis weight")
        mixed = combine(
            {key: scaled(bare_weight, value) for key, value in bare.items()},
            twirled,
            1 - bare_weight,
        )
        need(
            mixed
            == {
                key: scaled(target, value)
                for key, value in symmetric_projector(n).items()
            },
            "weighted projective two-design collision frame",
        )
        encoded_controls(n)
        results.append((n, a, bare_weight))
    return tuple(results)


def main() -> None:
    three_settings: tuple[Unitary, ...] = ()
    for n in range(2, 6):
        _, settings = fast_frame(n)
        need(len(settings) == n + n % 2, "fast setting count")
        if n == 3:
            three_settings = settings
    class_gap_controls()
    readout_controls(three_settings)
    designs = design_controls()
    print(
        "Exact fast pair frames n=2..5: bare plus n-1/even or n/odd matchings; F>=Pi_sym with precisely antisymmetric kernel."
    )
    print(
        "Gap controls: partition formula m=2..9 and regular spectra m=2..4; native three-copy positive mixture saturates leakage <=2E/m."
    )
    print(
        "Controls: one-basis symmetric false exclusion; orbital-hidden internal label; complete-mode access detects the hidden symmetric state."
    )
    print(
        f"Conditional encoded projective 2-designs (n, IPR A, bare weight): {designs}."
    )
    print(
        "Raw native bases cannot form that full design: uniform expectation 1/n !=2/(n+1); encoded independent phases are additional explicit control access."
    )
    print(
        "Ordered tensors, positive norm readout, collective action and complete modes are supplied. No physical Pauli, CAR, spin-statistics, or QM derivation."
    )


if __name__ == "__main__":
    main()
