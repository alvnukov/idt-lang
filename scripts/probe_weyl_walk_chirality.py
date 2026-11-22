"""Exact chirality fixture for one supplied two-component lattice walk.

Let e_j = -i sigma_j for the ordered Pauli axes x, y, z, so e_x e_y = e_z,
and U(k) = F_x(k_x) F_y(k_y) F_z(k_z), F_j(t) = cos(t) + e_j sin(t).
This convention fixes the orientation of the cone sign. A central U=aI
has quasienergy 0 (a=+1) or pi (a=-1), in units of one tick.

Continuous exhaustion: put A=sin(k_x)cos(k_y), B=cos(k_x)sin(k_y).
The x, y coefficients are (A cos(k_z)+B sin(k_z), B cos(k_z)-A sin(k_z)).
This rotation is invertible, so at a central point A=B=0. Either x and y
are both integer pi angles, or both odd half-pi angles. The remaining
z coefficient then forces z to be in the same family. Thus the quarter-
turn grid includes every central point on the raw (2*pi)^3 torus.

At the integer-pi points U(Q+q)=a U(q). At the odd half-pi points write
F_j(Q_j)=eta_j e_j (eta_j=+/-1); moving all three e_j factors to the left
across the F factors reverses y only, with a=-eta_x eta_y eta_z. Hence
U(Q+q)=a U(q_x,-q_y,q_z) on the full torus, not just to linear order.

Position support: each F supplies a +/-1 shift times its corresponding
Pauli eigenprojector. Products P_x P_y P_z are nonzero for all eight signs:
the squared overlap of successive eigenvectors on distinct Pauli axes is
1/2. These displacements generate L, where x, y and z have the same parity:
(1,1,1), (2,0,0), (0,2,0) generate L and are displacements or differences
of displacements.
There are four invariant cosets of L. On any connected component the
reciprocal torus identifies even pi shifts: testing the three generators
above forces reciprocal coordinates to be multiples of pi with even sum
in pi units. An odd pi shift negates U, rather than identifying the same
one-tick evolution. Each component has one cone of each sign per energy.

Spin and three distinct axes are supplied inputs. These opposite cone signs
and the disconnected copies are not counts of independent quark/lepton
species; a single origin cone does not establish Standard Model chirality.
This is a statement about this walk, not a general lattice no-go theorem
or a physical derivation. For related work on lattice automata, see
D'Ariano and Perinotti, https://arxiv.org/abs/1306.1934.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from typing import Literal

Quaternion = tuple[F, F, F, F]
Phase = tuple[F, F]
Phases = tuple[Phase, Phase, Phase]
Vector = tuple[F, F, F]
Matrix = tuple[Vector, Vector, Vector]
GridPoint = tuple[int, int, int]  # units of pi/2, modulo four
Sign = Literal[-1, 1]

ONE: Quaternion = (F(1), F(0), F(0), F(0))
NEG_ONE: Quaternion = (-F(1), F(0), F(0), F(0))
EX: Quaternion = (F(0), F(1), F(0), F(0))
EY: Quaternion = (F(0), F(0), F(1), F(0))
EZ: Quaternion = (F(0), F(0), F(0), F(1))
UNIT_PHASE: Phase = (F(1), F(0))
J_PLUS: Matrix = (EX[1:], EY[1:], EZ[1:])
J_MINUS: Matrix = (EX[1:], (F(0), F(-1), F(0)), EZ[1:])


def check(condition: bool, message: str) -> None:
    """Keep checks active under python -O."""
    if not condition:
        raise AssertionError(message)


def mul(left: Quaternion, right: Quaternion) -> Quaternion:
    """Multiply in the exact real basis (I,-i sigma_x,-i sigma_y,-i sigma_z)."""
    a, b, c, d = left
    w, x, y, z = right
    return (
        a * w - b * x - c * y - d * z,
        a * x + b * w + c * z - d * y,
        a * y - b * z + c * w + d * x,
        a * z + b * y - c * x + d * w,
    )


def scale(s: F, q: Quaternion) -> Quaternion:
    w, x, y, z = q
    return s * w, s * x, s * y, s * z


def shift(phase: Phase, turns: int) -> Phase:
    c, s = phase
    return ((c, s), (-s, c), (-c, -s), (s, -c))[turns % 4]


def factors(
    phases: Phases, axes: tuple[Quaternion, Quaternion, Quaternion]
) -> tuple[Quaternion, Quaternion, Quaternion]:
    def factor(phase: Phase, axis: Quaternion) -> Quaternion:
        c, s = phase
        _, x, y, z = scale(s, axis)
        return c, x, y, z

    px, py, pz = phases
    ex, ey, ez = axes
    return factor(px, ex), factor(py, ey), factor(pz, ez)


def walk(
    phases: Phases, axes: tuple[Quaternion, Quaternion, Quaternion] = (EX, EY, EZ)
) -> Quaternion:
    ux, uy, uz = factors(phases, axes)
    return mul(mul(ux, uy), uz)


def formula(phases: Phases) -> Quaternion:
    """Independent coordinate form used by the continuous exhaustion."""
    (cx, sx), (cy, sy), (cz, sz) = phases
    a, b = sx * cy, cx * sy
    return (
        cx * cy * cz - sx * sy * sz,
        a * cz + b * sz,
        b * cz - a * sz,
        sx * sy * cz + cx * cy * sz,
    )


def central_sign(u: Quaternion) -> Sign | None:
    if u == ONE:
        return 1
    if u == NEG_ONE:
        return -1
    return None


def jacobian(
    phases: Phases,
    a: Sign,
    axes: tuple[Quaternion, Quaternion, Quaternion] = (EX, EY, EZ),
) -> Matrix:
    """Columns are (i*a/2) Tr(sigma_l partial_j U), with partial_j F=e_j F."""
    ux, uy, uz = factors(phases, axes)
    ex, ey, ez = axes
    check(central_sign(mul(mul(ux, uy), uz)) == a, "Jacobian away from aI")
    # The vector part already extracts (i/2) Tr(sigma_l partial_j U).
    dx = scale(F(a), mul(mul(mul(ex, ux), uy), uz))
    dy = scale(F(a), mul(mul(ux, mul(ey, uy)), uz))
    dz = scale(F(a), mul(mul(ux, uy), mul(ez, uz)))
    check(dx[0] == dy[0] == dz[0] == 0, "central tangent is traceless")
    return (dx[1], dy[1], dz[1]), (dx[2], dy[2], dz[2]), (dx[3], dy[3], dz[3])


def det(j: Matrix) -> F:
    (a, b, c), (d, e, f), (g, h, i) = j
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def shifted(phases: Phases, q: GridPoint) -> Phases:
    return shift(phases[0], q[0]), shift(phases[1], q[1]), shift(phases[2], q[2])


def check_grid() -> dict[GridPoint, tuple[Sign, Sign]]:
    nodes: dict[GridPoint, tuple[Sign, Sign]] = {}
    all_phases: Phases = (UNIT_PHASE, UNIT_PHASE, UNIT_PHASE)
    for x, y, z in product(range(4), repeat=3):
        point = (x, y, z)
        phases = shifted(all_phases, point)
        u = walk(phases)
        check(u == formula(phases), f"continuous formula at {point}")
        a = central_sign(u)
        family = {p % 2 for p in point}
        if a is None:
            check(len(family) == 2, f"missed central point at {point}")
            continue
        check(len(family) == 1, f"extra central point at {point}")
        j = jacobian(phases, a)
        h: Sign = 1 if family == {0} else -1
        check(j == (J_PLUS if h == 1 else J_MINUS), f"Jacobian at {point}")
        check(det(j) == h, f"chirality at {point}")
        nodes[point] = (a, h)

    check(len(nodes) == 16 and 64 - len(nodes) == 48, "raw torus count")
    check(
        Counter(nodes.values()) == {(1, 1): 4, (1, -1): 4, (-1, 1): 4, (-1, -1): 4},
        "raw energy/chirality histogram",
    )
    # The 2^3 mesh uses just integer-pi angles and sees no negative cones.
    coarse = Counter(
        (a, h) for point, (a, h) in nodes.items() if all(p % 2 == 0 for p in point)
    )
    check(coarse == {(1, 1): 4, (-1, 1): 4}, "coarse mesh blind spot")
    return nodes


def check_quotient(nodes: dict[GridPoint, tuple[Sign, Sign]]) -> None:
    step_parities = {
        ((x - z) % 2, (y - z) % 2) for x, y, z in product((-1, 1), repeat=3)
    }
    check(step_parities == {(0, 0)}, "position components are invariant")
    coset_labels = {((x - z) % 2, (y - z) % 2) for x, y, z in product((0, 1), repeat=3)}
    check(len(coset_labels) == 4, "expected four position cosets")

    even_shifts = tuple(
        (a, b, c) for a, b, c in product((0, 2), repeat=3) if (a + b + c) % 4 == 0
    )
    orbits: dict[GridPoint, tuple[Sign, Sign]] = {}
    for (x, y, z), labels in nodes.items():
        orbit = {((x + a) % 4, (y + b) % 4, (z + c) % 4) for a, b, c in even_shifts}
        check(len(orbit) == 4, "reciprocal orbit size")
        check(all(nodes.get(p) == labels for p in orbit), "orbit mixes labels")
        orbits[min(orbit)] = labels
        check(
            nodes.get(((x + 2) % 4, y, z)) == (-labels[0], labels[1]),
            "odd shift should flip energy only",
        )
    check(
        Counter(orbits.values()) == {(1, 1): 1, (1, -1): 1, (-1, 1): 1, (-1, -1): 1},
        "connected-component energy/chirality histogram",
    )


def check_off_grid() -> int:
    px = F(3, 5), F(4, 5)
    py = F(5, 13), F(12, 13)
    pz = F(7, 25), F(24, 25)
    tested = 0
    for flips in product((-1, 1), repeat=3):
        x, y, z = flips
        phases: Phases = ((px[0], x * px[1]), (py[0], y * py[1]), (pz[0], z * pz[1]))
        for c, s in phases:
            check(c * c + s * s == 1 and c * s != 0, "off-grid rational unit phase")
        reflected: Phases = (phases[0], (phases[1][0], -phases[1][1]), phases[2])
        u = walk(phases)
        ur = walk(reflected)
        check(u == formula(phases) and ur == formula(reflected), "off-grid formula")
        check(u != ur and u != scale(F(-1), ur), "reflection must be discriminating")
        for i, j, k in product((0, 2), repeat=3):
            a = F((-1) ** ((i + j + k) // 2))
            check(walk(shifted(phases, (i, j, k))) == scale(a, u), "pi shift identity")
            tested += 1
        for i, j, k in product((1, 3), repeat=3):
            a = -F((-1) ** ((i + j + k - 3) // 2))
            check(
                walk(shifted(phases, (i, j, k))) == scale(a, ur),
                "odd half-pi reflection identity",
            )
            tested += 1
    return tested


def check_coincident_axes() -> None:
    # F_z(x) F_z(y) F_z(z) = F_z(x+y+z): the planes x+y+z in pi*Z
    # are central, each with a two-dimensional tangent kernel.
    axes = (EZ, EZ, EZ)
    px = F(3, 5), F(4, 5)
    py = F(5, 13), F(12, 13)
    cx, sx = px
    cy, sy = py
    pz = cx * cy - sx * sy, -sx * cy - cx * sy
    check(all(c * s != 0 for c, s in (px, py, pz)), "degeneracy plane off-grid")
    cases: tuple[tuple[Sign, int], ...] = ((1, 0), (-1, 2))
    rank_one: Matrix = ((F(0),) * 3, (F(0),) * 3, (F(1),) * 3)
    for a, turns in cases:
        phases: Phases = (px, py, shift(pz, turns))
        check(central_sign(walk(phases, axes)) == a, "central degeneracy plane")
        check(
            jacobian(phases, a, axes) == rank_one,
            "coincident-axis rank-one Jacobian",
        )
        check(
            central_sign(walk((px, py, shift(pz, turns + 1)), axes)) is None,
            "normal displacement leaves the plane",
        )


def main() -> None:
    nodes = check_grid()
    check_quotient(nodes)
    off_grid = check_off_grid()
    check_coincident_axes()
    print("4x4x4 raw torus: 48 noncentral; 4 per (quasienergy, chirality) bin.")
    print("2x2x2 raw torus: the mesh misses every negative-chirality cone.")
    print("Four position components: 1 of each chirality per energy per component.")
    print(f"{off_grid} exact off-grid shift/reflection checks; odd pi shift negates U.")
    print("Coincident axes: central planes and rank-one Jacobian, no isolated cone.")
    print("Supplied spin and axes: no species count, physical derivation or no-go.")


if __name__ == "__main__":
    main()
