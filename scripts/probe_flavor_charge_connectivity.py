"""Conditional flavor-charge equalities from two measured appearance links.

Do NOT assume off-diagonal Yukawa entries, Majorana masses or a complete
mixing graph. Instead supply (1) an exactly conserved, unbroken U(1), (2)
source and detection flavor states of definite charges x_alpha and x_beta,
(3) propagation with no transfer of this charge to an unobserved environment,
and (4) the usual interpretation of the reported backgrounds, calibrated
source and charged-current tags. For a neutral-transfer channel each Kraus
operator K preserves the charge blocks: (x_beta-x_alpha) K[beta,alpha]=0.
Since P(beta|alpha) is a sum of nonnegative |K[beta,alpha]|², nonzero
support requires equal charges. This is a selection rule, not an inference
from conserved mean charge or covariance of a reduced channel alone.

Historical inputs from different collaborations, beams, detectors and
appearance channels (not two replications of the same transition):

  T2K, Phys. Rev. Lett. 112, 061802 (2014), mu -> e. 28 final candidates
  from 377 fully contained fiducial-volume events at Super-Kamiokande,
  6.57 x 10^20 protons on target. The no-appearance comparison (theta13=0)
  expects 4.92 +/- 0.55 events. Reported significance: 7.3 sigma.
  https://doi.org/10.1103/PhysRevLett.112.061802
  https://arxiv.org/html/1311.4750 (event selection and background comparison)

  OPERA, Phys. Rev. Lett. 115, 121802 (2015), mu -> tau. Five candidates
  among 5,408 analyzed interactions in the CNGS sample, including tau decay
  topology. Total background expectation 0.25 +/- 0.05; reported 5.1 sigma.
  https://doi.org/10.1103/PhysRevLett.115.121802
  https://arxiv.org/html/1507.01417 (Tables 1 and 3; significance analysis)

The candidate/selection counts are not incident neutrino counts; their
ratios are not transition probabilities. Significances are the authors',
not reconstructed or combined here. Real beams are ensembles: the two
conditional positive-support inputs follow the published signal-vs-background
interpretations, not a claim that every candidate was an oscillated neutrino.

The two links connect all three active neutrinos. A common W charge and
charge-conserving calibrated vertex then transfer equality to their active
charged-lepton partners. This removes family *differences in these charges*,
not a common shift (e.g. B-L in a theory admitting it), nor does it classify
sterile fields or all gauge symmetries. Broken U(1)s, additional detection
interactions, mis-tagged or non-charge-sharp states, and charge exchange
with a reservoir are outside the implication. Exact finite controls below
exhibit a conserving exchange and inequivalent same-charge propagation with
identical flavor tables. They do not fit rates or derive neutrino dynamics.
The quantum-channel rule, sector dictionary and empirical links are supplied,
not derived from IDT primitives. Run: python3 -B -O -m scripts.probe_flavor_charge_connectivity
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F

E, MU, TAU = range(3)
Vector = tuple[F, ...]
Matrix = tuple[Vector, ...]
Charges = tuple[int, ...]
Edge = tuple[int, int]


def require(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


@dataclass(frozen=True)
class Appearance:
    name: str
    edge: Edge
    candidates: int
    selection_parent: int
    background: str
    significance: str


REPORTS = (
    Appearance("T2K", (MU, E), 28, 377, "4.92 ± 0.55", "7.3"),
    Appearance("OPERA", (MU, TAU), 5, 5408, "0.25 ± 0.05", "5.1"),
)


def components(edges: tuple[Edge, ...]) -> set[frozenset[int]]:
    """Equality propagates in both directions, even for a directed appearance."""
    parts = [{k} for k in (E, MU, TAU)]
    for a, b in edges:
        matches = [p for p in parts if a in p or b in p]
        parts = [p for p in parts if p not in matches] + [set().union(*matches)]
    return {frozenset(p) for p in parts}


def constant_on(charges: Charges, edges: tuple[Edge, ...]) -> bool:
    return all(charges[a] == charges[b] for a, b in edges)


def graph_controls() -> None:
    edges = tuple(report.edge for report in REPORTS)
    require(components(edges) == {frozenset((E, MU, TAU))}, "disconnected data graph")
    require(
        components(edges[:1]) == {frozenset((E, MU)), frozenset((TAU,))},
        "missing tau link",
    )
    require(
        components(edges[1:]) == {frozenset((E,)), frozenset((MU, TAU))},
        "missing electron link",
    )
    require(
        not constant_on((0, 1, -1), edges), "L_mu-L_tau is not active-flavor universal"
    )
    require(
        constant_on((0, 0, 1), edges[:1]) and not constant_on((0, 0, 1), edges),
        "edge ablation",
    )
    for nu, common_w_minus in (((0, 0, 0), -1), ((-1, -1, -1), 0)):
        charged = tuple(x + common_w_minus for x in nu)
        require(
            constant_on(nu, edges) and constant_on(charged, edges), "common W vertex"
        )
    # Both electromagnetism and universal B-L assignments pass this *equality* test.


def identity(n: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def mm(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum((v * w for v, w in zip(row, col, strict=True)), F(0))
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def swap_with_superposition(initial: int, target: Vector) -> Matrix:
    """Real Householder swap of |initial> and a disjoint unit target."""
    n = len(target)
    require(target[initial] == 0 and sum(v * v for v in target) == 1, "bad target")
    d = tuple(F(i == initial) - v for i, v in enumerate(target))
    matrix = tuple(tuple(F(i == j) - d[i] * d[j] for j in range(n)) for i in range(n))
    require(
        matrix == tuple(zip(*matrix, strict=True))
        and mm(matrix, matrix) == identity(n),
        "not an orthogonal involution",
    )
    require(tuple(row[initial] for row in matrix) == target, "swap failed")
    return matrix


def preserves(k: Matrix, charges: Charges) -> bool:
    return all(
        x == y or k[i][j] == 0
        for i, x in enumerate(charges)
        for j, y in enumerate(charges)
    )


def probabilities(channel: tuple[Matrix, ...]) -> Matrix:
    """P[i][j] for the fixture's definite-flavor inputs and ordinary flavor readout."""
    n = len(channel[0])
    table = tuple(
        tuple(sum((k[i][j] ** 2 for k in channel), F(0)) for j in range(n))
        for i in range(n)
    )
    require(
        all(sum(col) == 1 for col in zip(*table, strict=True)), "column normalization"
    )
    return table


def same_charge_controls() -> None:
    unitary = swap_with_superposition(MU, (F(3, 5), F(0), F(4, 5)))
    require(
        preserves(unitary, (-1, -1, -1)) and not preserves(unitary, (0, 1, -1)),
        "system-only selection rule",
    )
    # K_i = P_i U: dephase in the flavor basis AFTER the same coherent step.
    dephased = tuple(
        tuple(
            tuple(v if row_index == i else F(0) for v in row)
            for row_index, row in enumerate(unitary)
        )
        for i in range(3)
    )
    p = probabilities((unitary,))
    require(probabilities(dephased) == p, "one-step flavor tables differ")
    require(p[E][MU] == F(9, 25) and p[TAU][MU] == F(16, 25), "unequal appearances")
    # Compare two uses without intermediate readout, composing the actual channels.
    coherent_return = probabilities((mm(unitary, unitary),))[MU][MU]
    mixed_return = probabilities(tuple(mm(a, b) for a in dephased for b in dephased))[
        MU
    ][MU]
    require(
        coherent_return == 1 and mixed_return == F(337, 625), "two-step distinction"
    )


def exchange_control() -> None:
    # Basis index 3*f+r, system charges (0,1,-1), reservoir charges r=(0,1,2).
    system = (0, 1, -1)
    system_only = tuple(q for q in system for _ in range(3))
    total = tuple(q + r for q in system for r in range(3))
    initial = 3 * MU  # |mu,0>, including a fixed definite initial reservoir charge
    target = tuple(
        F(3, 5) if j == 3 * E + 1 else F(4, 5) if j == 3 * TAU + 2 else F(0)
        for j in range(9)
    )
    joint = swap_with_superposition(initial, target)
    require(
        preserves(joint, total) and not preserves(joint, system_only),
        "charge transfer control",
    )
    # Reservoir-resolved Kraus matrices <r|joint|0>; marginalize, do not postselect.
    reduced = tuple(
        tuple(tuple(joint[3 * i + r][3 * j] for j in range(3)) for i in range(3))
        for r in range(3)
    )
    p = probabilities(reduced)
    # Each K_r has a single charge shift -r: conjugating by the U(1) only
    # multiplies it by a phase, which cancels in K_r rho K_r^dagger. Thus the
    # reduced channel is U(1)-covariant even though it transfers system charge.
    require(
        all(
            k[i][j] == 0 or system[i] - system[j] == -r
            for r, k in enumerate(reduced)
            for i in range(3)
            for j in range(3)
        ),
        "reservoir-resolved charge shift",
    )
    require(
        p[E][MU] == F(9, 25) and p[TAU][MU] == F(16, 25),
        "appearance without equal charges",
    )
    require(
        not all(preserves(k, system) for k in reduced),
        "forbidden neutral-transfer inference",
    )


def main() -> None:
    graph_controls()
    same_charge_controls()
    exchange_control()
    for r in REPORTS:
        print(
            f"{r.name}: {r.candidates} candidates from {r.selection_parent} selected parent events; "
            f"background {r.background}, reported significance {r.significance} sigma."
        )
    print(
        "No system-environment charge exchange and definite flavor charges: mu->e and mu->tau force equal active charges."
    )
    print(
        "A universal B-L shift survives; charge exchange defeats the inference; support does not determine mass dynamics."
    )


if __name__ == "__main__":
    main()
