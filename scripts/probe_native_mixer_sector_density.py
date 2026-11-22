"""Exact finite evidence for the centered native-mixer density route.

Supplied: N complex ports in a common frame, their usual norm/topology,
arbitrarily long finite words, and the same native T_ij on a connected
address graph with identity bypass. T_ij = I + (i-1) P_ij, where P_ij is
the projector onto (e_i-e_j)/sqrt(2). T fixes the uniform vector, has
determinant i, T^2 is the address swap, and T^-1=T^3. No independent phase
gate, continuous control, tensor factorization, or source is added here.

GENERAL ARGUMENT, not a Lean proof or a conclusion from finite rank alone:
On three ports put V=1^perp and D=T_12 T_01. On V, tr(D)=3i/2 and
det(D)=-1, so its eigenvalues are i*exp(+/-i theta), cos(theta)=3/4.
If theta/pi were rational, exp(i theta) and its inverse would be roots
of unity, making their sum 3/2 a rational algebraic integer: impossible.
Thus powers of D^4 are dense in a circle in SU(V). Multiplying D by -i
is only an eigenvalue calculation, NOT an extra accessible phase gate.

Let H=D+D^dagger-2*P_uniform, zero on the uniform line. Exact calculations
below give H^2=(7/4)P_V and, for H'=T_01 H T_01^dagger,
tr_C(H^2)=7/2, tr_C(H H')=1/2: the axes have cosine 1/7. Their two
skew-Hermitian generators and bracket span su(2). In the usual compact
matrix-group topology, the closed native-word subgroup therefore contains
SU(V). The circle-density and closed-subgroup/Lie steps are mathematical
arguments, not established by the finite enumeration.

For N>=3, native words on each triple {0,1,k} supply the same SU(2) in
closure on W_k={supported on that triple, coordinate sum zero}. These
planes share e=e_0-e_1. The orthogonal directions v_k=e_0+e_1-2e_k span
e^perp within V but are NOT mutually orthogonal. Each triple Lie algebra
contains |v_k><e|-|e><v_k| and i(|v_k><e|+|e><v_k|). Real linear
combinations and Gram-Schmidt provide these couplings for an orthonormal
basis of e^perp. Their brackets give every off-diagonal su(N-1) pair and
all traceless diagonals. This proves the general spanning step separately
from the finite N=3..8 checks below. Lie combinations are operations in
the closed subgroup, not independently supplied exact physical gates.

Every native word has determinant in mu_4; continuity retains that upper
bound. Once SU(V) is contained, the native T_01 supplies all four cosets:

    closure = union_{r=0}^3 T_01^r SU(V), with the uniform line fixed.

This is a coset union, NOT generally the direct product SU(N-1) x C4.
It gives encoded SU(2) on three ports and SU(3) on four ports in closure,
not exact finite reachability of arbitrary matrices or a resource bound.
Connected-graph address swaps conjugate an available gate onto every pair;
the exact path controls below check that transport without extra gates.
N=2 is only C4. A disconnected graph fixes every component-uniform vector
and cannot have the stated full centered action; two isolated pairs give
the finite C4 x C4 control below.

Neighboring NativeGaussianDyadicDensity.lean proves scalar allocated-program
density in supplied complex topology. It does not prove this fixed-size
lossless gate-group claim. No gauge-field dynamics, physical universality,
Born rule, or full QM closure follows from this conditional route.

Run: python3 -B -O -m scripts.probe_native_mixer_sector_density
"""

import sys
from collections import deque
from fractions import Fraction
from itertools import combinations, product
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
    tr,
    wires,
)

Matrix = tuple[tuple[int, ...], ...]
Vector = tuple[int, ...]
Edge = tuple[int, int]
J: Matrix = ((0, -1), (1, 0))
NATIVE = from_turn(J)


def need(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def flatten(a: Matrix) -> Vector:
    return tuple(value for row in a for value in row)


def power(a: Matrix, exponent: int) -> Matrix:
    need(exponent >= 0, "nonnegative matrix exponent")
    result = eye(len(a))
    for _ in range(exponent):
        result = mul(a, result)
    return result


def trace(a: Matrix) -> int:
    return sum(a[i][i] for i in range(len(a)))


def bracket(a: Matrix, b: Matrix) -> Matrix:
    return plus(mul(a, b), mul(b, a), -1)


def complex_turn(n: int) -> Matrix:
    return matrix(2 * n, lambda i, j: int(i // 2 == j // 2) * J[i % 2][j % 2])


def uniform_sum(n: int) -> Matrix:
    """N times the projector onto the complex uniform line."""
    return matrix(2 * n, lambda i, j: int(i % 2 == j % 2))


def realify(real: Matrix, imag: Matrix) -> Matrix:
    return matrix(
        2 * len(real),
        lambda i, j: (
            real[i // 2][j // 2]
            if i % 2 == j % 2
            else (1 if i % 2 else -1) * imag[i // 2][j // 2]
        ),
    )


def outer(a: Vector, b: Vector) -> Matrix:
    return tuple(tuple(x * y for y in b) for x in a)


def check_native_projector(n: int, edge: Edge) -> None:
    a, b = edge
    root = tuple(int(i == a) - int(i == b) for i in range(n))
    twice_projector = realify(outer(root, root), scale(0, eye(n)))
    need(
        mul(twice_projector, twice_projector) == scale(2, twice_projector),
        "rank-one complex difference projector",
    )
    need(rank(twice_projector) == 2, "one complex difference direction")
    expected = plus(
        scale(2, eye(2 * n)),
        mul(plus(complex_turn(n), eye(2 * n), -1), twice_projector),
    )
    need(embed(n, edge, NATIVE) == expected, "native I+(i-1)P formula")


def triple_couplings(n: int, k: int) -> tuple[Matrix, Matrix, Matrix]:
    need(2 <= k < n, "triple needs a third port")
    e = tuple(int(i == 0) - int(i == 1) for i in range(n))
    v = tuple(int(i in (0, 1)) - 2 * int(i == k) for i in range(n))
    zero = scale(0, eye(n))
    ev, ve = outer(e, v), outer(v, e)
    a = realify(plus(ve, ev, -1), zero)
    b = realify(zero, plus(ve, ev))
    c = realify(zero, plus(outer(v, v), scale(-3, outer(e, e))))
    return a, b, c


def check_three_port_axes() -> None:
    a = embed(3, (0, 1), NATIVE)  # 2*T_01
    b = embed(3, (1, 2), NATIVE)  # 2*T_12
    d = mul(b, a)  # 4*D, D chronological T_01 then T_12
    turn, uniform = complex_turn(3), uniform_sum(3)
    centered = plus(scale(3, eye(6)), uniform, -1)  # 3*P_V
    need(sum(d[i][i] for i in range(0, 6, 2)) == 4, "full complex trace real numerator")
    need(
        sum(d[i + 1][i] for i in range(0, 6, 2)) == 6,
        "full complex trace imag numerator",
    )
    need(mul(d, uniform) == scale(4, uniform), "D fixes the uniform complex line")
    # On V: D^2 - (3i/2)D - I = 0, with eigenvalues (3i +/- sqrt(7))/4.
    characteristic = plus(plus(mul(d, d), scale(-6, mul(turn, d))), scale(-16, eye(6)))
    need(
        mul(characteristic, centered) == scale(0, eye(6)),
        "centered characteristic identity",
    )
    # H12=12*H is integral in the realification; no irrational eigenbasis.
    h12 = plus(scale(3, plus(d, tr(d))), scale(-8, uniform))
    need(h12 == tr(h12), "Hermitian axis")
    need(mul(h12, uniform) == scale(0, eye(6)), "axis zero on uniform line")
    need(mul(h12, h12) == scale(84, centered), "H^2 = 7/4 P_V")
    hp48 = mul(a, mul(h12, tr(a)))  # 48*T_01 H T_01^dagger
    need(trace(mul(h12, h12)) == 1008, "real trace of (12H)^2")
    need(trace(mul(h12, hp48)) == 576, "real trace of (12H)(48H')")
    need(7 * trace(mul(h12, hp48)) == 4 * trace(mul(h12, h12)), "axis cosine 1/7")
    comm = bracket(h12, hp48)
    need(
        sum(x * x for x in flatten(comm)) == 48 * 576**2,
        "complex commutator norm square 24",
    )
    x, y = mul(turn, h12), mul(turn, hp48)
    axes = (x, y, bracket(x, y))
    need(rank(map(flatten, axes)) == 3, "native circle axes and bracket span su(2)")
    couplings = triple_couplings(3, 2)
    need(
        rank(map(flatten, axes + couplings)) == 3,
        "common-line generators lie in native triple span",
    )


def check_centered_lie_spans() -> tuple[int, ...]:
    dimensions: list[int] = []
    for n in range(3, 9):
        couplings = [item for k in range(2, n) for item in triple_couplings(n, k)[:2]]
        generators = couplings + [bracket(a, b) for a, b in combinations(couplings, 2)]
        turn, uniform = complex_turn(n), uniform_sum(n)
        zero = scale(0, eye(2 * n))
        for generator in generators:
            need(plus(generator, tr(generator)) == zero, "skew-Hermitian realification")
            need(bracket(generator, turn) == zero, "complex-linearity")
            need(mul(generator, uniform) == zero, "uniform sector fixed")
            need(
                sum(generator[2 * i + 1][2 * i] for i in range(n)) == 0,
                "zero complex trace",
            )
        dimension = rank(map(flatten, generators))
        need(
            dimension == (n - 1) ** 2 - 1, "full centered special-unitary Lie dimension"
        )
        dimensions.append(dimension)
    return tuple(dimensions)


def path_edges(n: int, edges: tuple[Edge, ...], start: int, finish: int) -> list[Edge]:
    neighbors: list[list[int]] = [[] for _ in range(n)]
    for a, b in edges:
        neighbors[a].append(b)
        neighbors[b].append(a)
    previous: dict[int, int] = {start: start}
    pending = deque([start])
    while pending and finish not in previous:
        here = pending.popleft()
        for there in neighbors[here]:
            if there not in previous:
                previous[there] = here
                pending.append(there)
    need(finish in previous, "requested address transport is disconnected")
    result: list[Edge] = []
    vertex = finish
    while vertex != start:
        parent = previous[vertex]
        result.append((parent, vertex))
        vertex = parent
    return list(reversed(result))


def endpoint_swap(n: int, edges: tuple[Edge, ...], a: int, b: int) -> list[Edge]:
    path = path_edges(n, edges, a, b)
    return path + path[-2::-1]


def swap_permutation(n: int, word: list[Edge]) -> Matrix:
    labels = list(range(n))
    for a, b in word:
        labels[a], labels[b] = labels[b], labels[a]
    return wires(tuple(2 * labels[i // 2] + i % 2 for i in range(2 * n)))


def transposed(vertex: int, a: int, b: int) -> int:
    return b if vertex == a else a if vertex == b else vertex


def check_connected_transport() -> int:
    count = 0
    for n in range(3, 8):
        graphs = (
            tuple((i, i + 1) for i in range(n - 1)),
            tuple((0, i) for i in range(1, n)),
        )
        for edges in graphs:
            source_a, source_b = edges[0]
            source_gate = embed(n, edges[0], NATIVE)
            allowed = {frozenset(edge) for edge in edges}
            for edge in edges:
                check_native_projector(n, edge)
                swap = swap_permutation(n, [edge])
                gate = embed(n, edge, NATIVE)
                need(
                    mul(gate, gate) == scale(4, swap),
                    "edge swap compiled as two native gates",
                )
                need(
                    power(gate, 4) == scale(16, eye(2 * n)),
                    "native inverse is its cube",
                )
            for target_a, target_b in combinations(range(n), 2):
                first = endpoint_swap(n, edges, source_a, target_a)
                current_b = transposed(source_b, source_a, target_a)
                second = endpoint_swap(n, edges, current_b, target_b)
                word = first + second
                need(
                    all(frozenset(edge) in allowed for edge in word),
                    "only available edge swaps",
                )
                rename = swap_permutation(n, word)
                expected = embed(n, (target_a, target_b), NATIVE)
                need(
                    mul(rename, mul(source_gate, tr(rename))) == expected,
                    "native pair transported on connected graph",
                )
                # Every swap is T_edge^2; inverse transport uses reversed swaps.
                need(
                    mul(rename, swap_permutation(n, list(reversed(word))))
                    == eye(2 * n),
                    "inverse address transport",
                )
                count += 1
    need(count == 110, "connected line/star transport census")
    return count


def normalized_key(raw: Matrix, word_length: int) -> tuple[Fraction, ...]:
    return tuple(Fraction(value, 2**word_length) for value in flatten(raw))


def check_finite_and_disconnected_controls() -> None:
    check_native_projector(2, (0, 1))
    pair_gate = embed(2, (0, 1), NATIVE)
    pair_group = {normalized_key(power(pair_gate, k), k) for k in range(4)}
    need(
        len(pair_group) == 4 and power(pair_gate, 4) == scale(16, eye(4)),
        "N=2 is only C4",
    )
    a, b = embed(4, (0, 1), NATIVE), embed(4, (2, 3), NATIVE)
    need(bracket(a, b) == scale(0, eye(8)), "disconnected pair gates commute")
    disconnected = {
        normalized_key(mul(power(a, j), power(b, k)), j + k)
        for j, k in product(range(4), repeat=2)
    }
    need(len(disconnected) == 16, "two disconnected pairs give exactly C4 x C4")
    component_uniform = matrix(8, lambda i, j: int(i // 4 == j // 4 and i % 2 == j % 2))
    need(rank(component_uniform) == 4, "two complex component-uniform directions")
    for gate in (a, b):
        need(
            mul(gate, component_uniform) == scale(2, component_uniform),
            "disconnected uniform directions stay fixed",
        )


def main() -> None:
    check_three_port_axes()
    dimensions = check_centered_lie_spans()
    transports = check_connected_transport()
    check_finite_and_disconnected_controls()
    print(
        "Three-port exact axis: cos(theta)=3/4; conjugate-axis cosine 1/7; complex commutator norm square 24."
    )
    print(f"Centered special-unitary Lie spans for N=3..8: {dimensions}.")
    print(
        f"Connected line/star graphs: {transports} exact pair transports using native squares only."
    )
    print(
        "Controls: N=2 has four elements; two disconnected pairs have 16 and fix two complex uniform directions."
    )
    print(
        "General closure route uses irrational-circle and closed-Lie-subgroup arguments; finite checks alone do not prove density."
    )
    print(
        "Conditional target: four determinant cosets of SU(N-1), not a direct product or gauge dynamics; no exact arbitrary-gate/resource claim."
    )


if __name__ == "__main__":
    main()
