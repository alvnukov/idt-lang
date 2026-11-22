"""Exact finite detector obstructions for a supplied cube-endpoint candidate.

Supplied: lambda in {+/-1}^3, mu_n(lambda)=(n dot lambda)_+/6 for
n in {+/-1}^3, and the tetrahedral target (1+n dot t_j/3)/4.
All four-outcome detectors here are preparation-independent stochastic rows on
the SAME eight endpoints. Extra history, refreshed randomness correlated with
preparation, and finer ontic state spaces are outside this obstruction.

This is an executable rational certificate, NOT a Lean formal proof, a new
physical prediction, or experimental evidence. Targets and geometry are input,
not derived. No parameters are fitted. Four-source minimality is not claimed.
The new face-diagonal YES/NO orientation is a separate extension problem from
the fixed four-outcome detector. Detection-conditioned agreement is explicitly
separated from normalized unconditional agreement.
"""

from fractions import Fraction
from itertools import combinations
from typing import TypeAlias

Vector: TypeAlias = tuple[int, int, int]
Matrix: TypeAlias = list[list[Fraction]]
Term: TypeAlias = tuple[int, int, Fraction]
Q = Fraction
TETRA: tuple[Vector, ...] = (
    (1, 1, 1),
    (1, -1, -1),
    (-1, 1, -1),
    (-1, -1, 1),
)
ENDPOINTS = TETRA + tuple(tuple(-x for x in t) for t in TETRA)


def check(condition: bool, message: str) -> None:
    """Checks deliberately survive python -O."""
    if not condition:
        raise RuntimeError(message)


def dot(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    return sum(x * y for x, y in zip(a, b, strict=True))


def zeros(rows: int, columns: int) -> Matrix:
    return [[Q(0) for _ in range(columns)] for _ in range(rows)]


PREPARATIONS: Matrix = [
    [Q(max(dot(n, endpoint), 0), 6) for endpoint in ENDPOINTS] for n in ENDPOINTS
]
TARGET: Matrix = [[(1 + Q(dot(n, t), 3)) / 4 for t in TETRA] for n in ENDPOINTS]


def predict(detector: Matrix) -> Matrix:
    columns = len(detector[0])
    check(len(detector) == 8, "detector must act on exactly eight endpoints")
    check(all(len(row) == columns for row in detector), "ragged detector")
    check(all(value >= 0 for row in detector for value in row), "negative response")
    return [
        [sum((mu[k] * detector[k][j] for k in range(8)), Q(0)) for j in range(columns)]
        for mu in PREPARATIONS
    ]


def normalized(detector: Matrix) -> None:
    check(all(sum(row) == 1 for row in detector), "non-normalized detector")


def value(table: Matrix, terms: list[Term]) -> Fraction:
    return sum((weight * table[n][j] for n, j, weight in terms), Q(0))


def coefficients(terms: list[Term]) -> Matrix:
    result = zeros(8, 4)
    for n, j, weight in terms:
        for k in range(8):
            result[k][j] += weight * PREPARATIONS[n][k]
    return result


def certify_minimum(terms: list[Term], expected: Fraction, label: str) -> Matrix:
    """Each stochastic row is a simplex: minimize each row independently.

    The displayed four coefficients per endpoint check every deterministic
    response locally. Their Cartesian product is all 4^8 deterministic
    detectors, and rowwise convexity covers every stochastic detector.
    """
    coeff = coefficients(terms)
    minimum = sum((min(row) for row in coeff), Q(0))
    check(minimum == expected, f"{label}: wrong exact minimum {minimum}")
    print(f"{label} coefficients by endpoint (four outcome choices each):")
    for endpoint, row in zip(ENDPOINTS, coeff, strict=True):
        print(f"  {endpoint}: {', '.join(map(str, row))}; min={min(row)}")
    print(f"  minimum={minimum}; covers 4^8=65536 deterministic vertices + convexity")
    return coeff


def max_error(table: Matrix, sources: list[int]) -> Fraction:
    return max(abs(table[n][j] - TARGET[n][j]) for n in sources for j in range(4))


def check_base() -> None:
    check(len(set(ENDPOINTS)) == 8, "cube endpoint enumeration")
    normalized(PREPARATIONS)
    normalized(TARGET)
    signs = [[Q(dot(t, endpoint) > 0) for t in TETRA] for endpoint in ENDPOINTS]
    actual = predict(signs)
    for n, prep in enumerate(ENDPOINTS):
        for j, t in enumerate(TETRA):
            check(actual[n][j] == (1 + Q(dot(prep, t), 3)) / 2, "fixed sign law")
    print(
        "Supplied endpoint law: eight normalized preparations; fixed tetra sign axes pass."
    )


def check_eight_source_obstruction() -> None:
    terms = [(i, i, Q(1, 4)) for i in range(4)] + [
        (4 + i, i, Q(3, 4)) for i in range(4)
    ]
    coeff = certify_minimum(terms, Q(2, 3), "eight-source D+ + 3D-")
    for k, row in enumerate(coeff):
        for j, entry in enumerate(row):
            expected = Q(1, 8) if k < 4 else Q(1, 24) + Q(k - 4 == j, 3)
            check(entry == expected, "D+ +3D- coefficient identity")
    check(value(TARGET, terms) == Q(1, 2), "eight-source target value")
    detector = [
        [Q(3, 4) if i == j else Q(1, 12) for j in range(4)] for i in range(4)
    ] + [[Q(0) if i == j else Q(1, 3) for j in range(4)] for i in range(4)]
    normalized(detector)
    table = predict(detector)
    error = max_error(table, list(range(8)))
    bound = (Q(2, 3) - value(TARGET, terms)) / sum(abs(w) for _, _, w in terms)
    check(error == bound == Q(1, 24), "sharp eight-source minimax control")
    check(value(table, terms) == Q(2, 3), "eight-source attaining inequality")
    print("  identity: D+ +3D- = 2/3 +(4/3) mean_diag(B) >=2/3; target=1/2")
    print(
        "  exact normalized all-entry minimax error on eight sources = 1/24 (attained)"
    )


def check_five_source_obstruction() -> None:
    terms = [(0, 0, Q(3)), (4, 0, Q(2))]
    terms += [(4 + j, j, Q(6)) for j in range(1, 4)]
    terms += [(4 + j, 0, Q(-1)) for j in range(1, 4)]
    certify_minimum(terms, Q(1), "five-source inequality")
    check(value(TARGET, terms) == Q(1, 2), "five-source target value")
    detector = [[Q(17, 26)] + [Q(3, 26)] * 3]
    for i in range(1, 4):
        detector.append(
            [Q(1, 26) if j == 0 else Q(25, 26) * (j == i) for j in range(4)]
        )
    detector.append([Q(0)] + [Q(1, 3)] * 3)
    for i in range(1, 4):
        detector.append(
            [Q(5, 13) if j == 0 else Q(0) if j == i else Q(4, 13) for j in range(4)]
        )
    normalized(detector)
    table = predict(detector)
    error = max_error(table, [0, 4, 5, 6, 7])
    bound = (1 - value(TARGET, terms)) / sum(abs(w) for _, _, w in terms)
    check(error == bound == Q(1, 52), "sharp five-source minimax control")
    check(value(table, terms) == 1, "five-source attaining inequality")
    print("  3P(0|+0)+2P(0|-0)+6 sum_j>0 P(j|-j)-sum_j>0 P(0|-j) >=1; target=1/2")
    print(
        "  exact normalized all-entry minimax error on these five sources =1/52 (attained)"
    )
    print("  No four-source feasibility or minimal-cardinality claim is made.")


def check_coarse_grainings() -> None:
    for merged in combinations(range(4), 2):
        singles = [j for j in range(4) if j not in merged]
        detector = zeros(8, 3)
        for k, endpoint in enumerate(ENDPOINTS):
            for j, original in enumerate(singles):
                detector[k][j] = Q(dot(TETRA[original], endpoint) > 0, 2)
            detector[k][2] = 1 - sum(detector[k][:2], Q(0))
        normalized(detector)
        table = predict(detector)
        expected = [
            [row[singles[0]], row[singles[1]], sum(row[j] for j in merged)]
            for row in TARGET
        ]
        check(table == expected, f"coarse-graining merge {merged}")
    print(
        "All six pair-merge three-outcome targets have normalized endpoint detectors."
    )
    print(
        "Every further proper outcome coarsening follows by merging these detector columns."
    )


def check_click_conditioning() -> None:
    raw = [[Q(dot(t, endpoint) > 0, 3) for t in TETRA] for endpoint in ENDPOINTS]
    detector = [row + [1 - sum(row, Q(0))] for row in raw]
    normalized(detector)
    table = predict(detector)
    for n, row in enumerate(table):
        efficiency = sum(row[:4])
        check(efficiency == Q(2, 3), "constant raw click efficiency")
        check([p / efficiency for p in row[:4]] == TARGET[n], "conditional target")

    # Common efficiency eta and exact conditional target imply raw=eta*TARGET.
    # P(j|-t_j)=0 and positivity force A[k,j]=0 (k!=j), B[j,j]=0.
    # With that support, plus-source probabilities determine the remaining row:
    # B[i,j]=3(P(j|+t_l)+P(j|+t_m)-P(j|+t_i)), i,l,m !=j;
    # A[j,j]=2P(j|+t_j)-(1/3)sum_i!=j B[i,j].
    # These linear identities are checked on every surviving response basis.
    for j in range(4):
        allowed = [j] + [4 + i for i in range(4) if i != j]
        for k in range(8):
            zero_coefficient = PREPARATIONS[4 + j][k]
            check((zero_coefficient == 0) == (k in allowed), "zero-target support")
        for basis in allowed:
            response = [Q(k == basis) for k in range(8)]
            plus = [
                sum((mu[k] * response[k] for k in range(8)), Q(0))
                for mu in PREPARATIONS[:4]
            ]
            recovered_b: dict[int, Fraction] = {}
            for i in range(4):
                if i == j:
                    continue
                other = [h for h in range(4) if h not in (i, j)]
                recovered_b[i] = 3 * (plus[other[0]] + plus[other[1]] - plus[i])
                check(recovered_b[i] == response[4 + i], "click B recovery identity")
            recovered_a = 2 * plus[j] - sum(recovered_b.values()) / 3
            check(recovered_a == response[j], "click A recovery identity")
        ideal_plus = [TARGET[i][j] for i in range(4)]
        for i in range(4):
            if i != j:
                other = [h for h in range(4) if h not in (i, j)]
                check(
                    3 * (ideal_plus[other[0]] + ideal_plus[other[1]] - ideal_plus[i])
                    == Q(1, 2),
                    "unit-efficiency B coefficient",
                )
        check(
            2 * ideal_plus[j] - 3 * Q(1, 2) / 3 == Q(1, 2),
            "unit-efficiency A coefficient",
        )
    check(Q(3, 2) * Q(2, 3) == 1, "common-efficiency ceiling")
    print(
        "No-click control: raw efficiency=2/3 on all eight preparations; conditional target exact."
    )
    print(
        "Exact common-efficiency ceiling=2/3: zero-target support forces B_off=eta/2,"
    )
    print("  hence each negative endpoint has click-row sum=3eta/2 <=1 (attained).")
    print(
        "This ceiling assumes exact conditional agreement AND one shared efficiency for all eight sources."
    )


def check_separate_binary_orientation() -> None:
    left, right = 0, 3  # (111), (--+); new m=(1,1,0)/sqrt(2).
    total_variation = (
        sum(
            abs(a - b)
            for a, b in zip(PREPARATIONS[left], PREPARATIONS[right], strict=True)
        )
        / 2
    )
    check(total_variation == Q(2, 3), "binary pair total variation")
    # Target difference sqrt(2/3) exceeds TV since 2/3 > (2/3)^2.
    check(Q(2, 3) > total_variation**2, "strict face-diagonal obstruction")
    response = [
        Q(1) if a > b else Q(0) if a < b else Q(1, 2)
        for a, b in zip(PREPARATIONS[left], PREPARATIONS[right], strict=True)
    ]
    table = predict([[p, 1 - p] for p in response])
    check(table[left][0] == Q(5, 6), "binary sharp left control")
    check(table[right][0] == Q(1, 6), "binary sharp right control")
    check(
        table[left][0] - table[right][0] == total_variation, "binary sharp contraction"
    )
    print("SEPARATE new binary axis m=(1,1,0)/sqrt(2): source pair (111),(--+).")
    print(
        "  TV=2/3 < target difference sqrt(2/3); sharp pair max-error=(sqrt(2/3)-2/3)/2."
    )
    print(
        "  Attaining fixed binary response gives probabilities 5/6,1/6; no numerical tolerance."
    )


def main() -> None:
    check_base()
    check_eight_source_obstruction()
    check_five_source_obstruction()
    check_coarse_grainings()
    check_click_conditioning()
    check_separate_binary_orientation()
    print(
        "PASS: exact finite supplied-model certificates only; finer histories may escape."
    )


if __name__ == "__main__":
    main()
