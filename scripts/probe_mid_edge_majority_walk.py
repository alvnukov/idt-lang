"""Exact finite cube probe for a supplied midpoint-killed majority walk.

Original vertices are in {-1,+1}**d for odd d. A preparation supplies a
vertex normal n and the bright region n.v > 0. One block chooses an incident
edge uniformly, visits its midpoint, kills at n.midpoint <= 0, and otherwise
chooses either endpoint with probability 1/2. Readout is the supplied fixed
sign of m.v at an original-vertex terminal snapshot.

These are finite rational checks, not a universal proof or a QM derivation.
Normals/readouts, fair random choices, killing, terminal timing, and any
repreparation rule are specified inputs. No parameters are fitted. In
particular, the affine-dot response also occurs at d=5: this probe does not
select d=3 or establish arbitrary continuous measurement directions.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from typing import Literal

Vertex = tuple[int, ...]
Mass = dict[Vertex, Fraction]
Rows = dict[Vertex, Counter[Vertex]]
Protocol = Literal["midpoint", "endpoint_only"]


def check(condition: bool, message: str) -> None:
    """Checks deliberately remain enabled under python -O."""
    if not condition:
        raise RuntimeError(message)


def vertices(dimension: int) -> tuple[Vertex, ...]:
    return tuple(product((-1, 1), repeat=dimension))


def dot(left: Vertex, right: Vertex) -> int:
    return sum(a * b for a, b in zip(left, right, strict=True))


def flip(vertex: Vertex, axis: int) -> Vertex:
    return tuple(-x if index == axis else x for index, x in enumerate(vertex))


def block_rows(normal: Vertex, protocol: Protocol = "midpoint") -> Rows:
    """Count equiprobable (edge, endpoint) paths; each has weight 1/(2d)."""
    dimension = len(normal)
    check(dimension % 2 == 1, "this protocol check is restricted to odd d")
    rows: Rows = {}
    for start in vertices(dimension):
        if dot(normal, start) <= 0:
            continue
        row: Counter[Vertex] = Counter()
        for axis in range(dimension):
            neighbor = flip(start, axis)
            if protocol == "midpoint":
                # Twice n.midpoint, with no floating-point coordinates.
                if dot(normal, start) + dot(normal, neighbor) <= 0:
                    continue
                for endpoint in (start, neighbor):
                    check(dot(normal, endpoint) > 0, "live edge escaped odd bright set")
                    row[endpoint] += 1
            elif protocol == "endpoint_only":
                # Independent control: no test at the intermediate midpoint.
                for coin in (0, 1):
                    endpoint = start if coin == 0 else neighbor
                    if dot(normal, endpoint) > 0:
                        row[endpoint] += 1
            else:
                raise ValueError(protocol)
        check(sum(row.values()) <= 2 * dimension, "row is not substochastic")
        rows[start] = row
    return rows


def advance(mass: Mass, rows: Rows, dimension: int) -> Mass:
    result = dict.fromkeys(rows, Fraction(0))
    for start, weight in mass.items():
        for end, count in rows[start].items():
            result[end] += weight * Fraction(count, 2 * dimension)
    return result


def normalize(mass: Mass) -> tuple[Fraction, Mass]:
    total = sum(mass.values(), Fraction(0))
    check(total > 0, "cannot condition an extinct population")
    return total, {vertex: weight / total for vertex, weight in mass.items()}


def qsd(normal: Vertex) -> Mass:
    weights = {
        vertex: Fraction(dot(normal, vertex))
        for vertex in vertices(len(normal))
        if dot(normal, vertex) > 0
    }
    return normalize(weights)[1]


def response(mass: Mass, readout: Vertex) -> Fraction:
    return sum(
        (weight for vertex, weight in mass.items() if dot(readout, vertex) > 0),
        Fraction(0),
    )


def check_eigenvector(dimension: int) -> None:
    """Exhaust all supplied preparation normals in this finite dimension."""
    eigenvalue = Fraction(dimension - 1, dimension)
    for normal in vertices(dimension):
        rows = block_rows(normal)
        weights = {vertex: dot(normal, vertex) for vertex in rows}
        # Check K f = lambda f with integer arithmetic, independently of advance.
        for start, row in rows.items():
            check(
                sum(count * weights[end] for end, count in row.items())
                == 2 * (dimension - 1) * weights[start],
                f"integer eigenvector identity failed at d={dimension}",
            )
            for end, count in row.items():
                check(rows[end][start] == count, "kernel is not symmetric")
        mass = qsd(normal)
        updated = advance(mass, rows, dimension)
        check(
            updated == {vertex: eigenvalue * weight for vertex, weight in mass.items()},
            "fraction-valued left eigenvector check failed",
        )
        if dimension > 1:
            survival, conditioned = normalize(updated)
            check(survival == eigenvalue and conditioned == mass, "QSD check failed")
        else:
            check(not any(updated.values()), "d=1 should have no survivors")


def check_responses(dimension: int, exhaustive_normals: bool) -> int:
    cube = vertices(dimension)
    normals = cube if exhaustive_normals else ((1,) * dimension,)
    count = 0
    for normal in normals:
        mass = qsd(normal)
        for readout in cube:
            expected = Fraction(dimension + dot(normal, readout), 2 * dimension)
            check(response(mass, readout) == expected, "affine-dot response failed")
            count += 1
    return count


def uniform_bright(normal: Vertex) -> Mass:
    bright = tuple(
        vertex for vertex in vertices(len(normal)) if dot(normal, vertex) > 0
    )
    return dict.fromkeys(bright, Fraction(1, len(bright)))


def margin_profile(mass: Mass, normal: Vertex) -> str:
    """Per-vertex masses by n.v, not the total mass in a shell."""
    shells: dict[int, set[Fraction]] = {}
    for vertex, weight in mass.items():
        shells.setdefault(dot(normal, vertex), set()).add(weight)
    check(
        all(len(values) == 1 for values in shells.values()), "nonuniform margin shell"
    )
    return ", ".join(
        f"margin {margin}: {next(iter(shells[margin]))}"
        for margin in sorted(shells, reverse=True)
    )


def check_transients_and_control() -> None:
    normal = (1, 1, 1)
    initial = uniform_bright(normal)
    midpoint_rows = block_rows(normal)
    center = normal
    leaves = tuple(flip(center, axis) for axis in range(3))
    check(
        midpoint_rows[center] == Counter({center: 3, **dict.fromkeys(leaves, 1)}),
        "center row",
    )
    for leaf in leaves:
        check(midpoint_rows[leaf] == Counter({leaf: 1, center: 1}), "midpoint leaf row")
    survival, after = normalize(advance(initial, midpoint_rows, 3))
    check(survival == Fraction(1, 2), "wrong d=3 one-block survival")
    check(after == qsd(normal), "d=3 did not reach QSD in one block")
    check(after[center] == Fraction(1, 2), "wrong d=3 center mass")
    check(all(after[leaf] == Fraction(1, 6) for leaf in leaves), "wrong d=3 leaf mass")

    endpoint_rows = block_rows(normal, "endpoint_only")
    check(endpoint_rows[center] == midpoint_rows[center], "endpoint center row")
    for leaf in leaves:
        check(endpoint_rows[leaf] == Counter({leaf: 3, center: 1}), "endpoint leaf row")
    endpoint_survival, endpoint_after = normalize(advance(initial, endpoint_rows, 3))
    check(endpoint_survival == Fraction(3, 4), "wrong endpoint-only survival")
    check(endpoint_after[center] == Fraction(1, 3), "wrong endpoint-only center mass")
    check(
        all(endpoint_after[leaf] == Fraction(2, 9) for leaf in leaves),
        "endpoint leaf mass",
    )
    check(endpoint_after != after, "endpoint-only control failed to separate")
    print(
        f"d=3 midpoint: survival={survival}; conditional per vertex: {margin_profile(after, normal)}"
    )
    print(
        "d=3 endpoint-only control: "
        f"survival={endpoint_survival}; conditional per vertex: {margin_profile(endpoint_after, normal)}"
    )

    holdout = (1,) * 5
    holdout_survival, holdout_after = normalize(
        advance(uniform_bright(holdout), block_rows(holdout), 5)
    )
    check(holdout_survival == Fraction(5, 8), "wrong d=5 one-block survival")
    expected_masses = {5: Fraction(1, 10), 3: Fraction(1, 10), 1: Fraction(1, 25)}
    check(
        all(
            weight == expected_masses[dot(holdout, vertex)]
            for vertex, weight in holdout_after.items()
        ),
        "wrong d=5 one-block masses",
    )
    check(holdout_after != qsd(holdout), "d=5 unexpectedly reached QSD in one block")
    holdout_readout = flip(holdout, 0)
    transient_response = response(holdout_after, holdout_readout)
    stationary_response = response(qsd(holdout), holdout_readout)
    check(
        transient_response == Fraction(19, 25)
        and stationary_response == Fraction(4, 5),
        "wrong d=5 transient readout discrepancy",
    )
    print(
        f"d=5 one-block holdout: survival={holdout_survival}; "
        f"conditional per vertex: {margin_profile(holdout_after, holdout)}; "
        f"QSD per vertex: {margin_profile(qsd(holdout), holdout)}; not equal"
    )
    print(
        "d=5 readout differing in one coordinate: "
        f"one-block response={transient_response}, QSD response={stationary_response}"
    )


def antipodal_mixture(normal: Vertex) -> Mass:
    opposite = tuple(-coordinate for coordinate in normal)
    positive, negative = qsd(normal), qsd(opposite)
    return {
        vertex: (positive.get(vertex, Fraction(0)) + negative.get(vertex, Fraction(0)))
        / 2
        for vertex in vertices(len(normal))
    }


def check_instruments_and_mixtures() -> None:
    normal = (1, 1, 1)
    readout = (-1, 1, 1)
    original = qsd(normal)
    selected = {
        vertex: weight
        for vertex, weight in original.items()
        if dot(readout, vertex) > 0
    }
    branch_probability, passive = normalize(selected)
    passive_return = response(passive, normal)
    reprepare_return = response(qsd(readout), normal)
    check(branch_probability == Fraction(2, 3), "wrong branch probability")
    check(
        passive_return == 1 and reprepare_return == Fraction(2, 3),
        "instrument separation failed",
    )
    print(
        "d=3 sequence n+, m+, n+: P(m+)=2/3; "
        f"conditional final P(n+) passive={passive_return}, reprepare={reprepare_return}; "
        "repreparation is an additional supplied instrument"
    )

    first, second = antipodal_mixture(normal), antipodal_mixture(readout)
    check(first != second, "antipodal mixtures unexpectedly identical")
    for sign in vertices(3):
        check(
            response(first, sign) == response(second, sign) == Fraction(1, 2),
            "biased sign mixture",
        )
    first_poles = first[normal] + first[tuple(-x for x in normal)]
    second_poles = second[normal] + second[tuple(-x for x in normal)]
    check(
        first_poles == Fraction(1, 2) and second_poles == Fraction(1, 6),
        "hidden pole event",
    )
    print(
        "d=3 two antipodal mixtures: all 8 single-sign responses=1/2, "
        "but hidden event v in {n,-n} has probabilities 1/2 vs 1/6; "
        "single-sign equivalence does not identify hidden distributions"
    )


def main() -> None:
    for dimension in (1, 3, 5, 7):
        check_eigenvector(dimension)
        print(
            f"d={dimension}: all {2**dimension} normals checked; "
            f"Kf={(Fraction(dimension - 1, dimension))} f"
            + ("; extinct, no surviving QSD" if dimension == 1 else "; exact QSD")
        )
    for dimension in (3, 5, 7):
        exhaustive = dimension != 7
        pairs = check_responses(dimension, exhaustive)
        scope = (
            "exhaustive (n,m)"
            if exhaustive
            else "one n, all m; other n by cube symmetry, not enumerated here"
        )
        print(f"d={dimension}: {pairs} affine-dot response pairs checked; {scope}")
    check_transients_and_control()
    check_instruments_and_mixtures()
    print(
        "Scope: finite prescribed walks and vertex directions only; "
        "no continuous-angle closure, dimension selection, primitive derivation, "
        "or QM claim. d=3 directions are the cube vertices (a tetrahedron and its negatives)."
    )


if __name__ == "__main__":
    main()
