"""What diagonal charges survive one signed five-slot *pairing* law?

Prerequisites: five addressed hard-core slots with exterior signs (CAR), the
even sector, a top-form readout and degree reversal. None is derived here.
Given even masks a,b, set B_i^±(a,b)=[rev(a) wedge gamma_i^±(b)]_top,
with gamma_i^± ordinary exterior creation/contraction. This is a bilinear
pair channel, not a one-particle End operator. One CAR letter does NOT make
the entire readout local. We enumerate the signs, symmetry and support before
assigning charges, sector labels, a family dictionary or anomaly equations.
This is the familiar spinor/vector construction, not a proposed new GUT;
compare the 16-16-10 coupling (and other tensors) in Nath & Syed,
https://arxiv.org/abs/hep-ph/0103165 . We do not assume or derive a physical
Spin(10) gauge group, unified scale, elementary scalar or Lorentz spin.

Additional selection hypothesis: EACH entire oriented matrix is one channel
of definite scalar charge, with opposite charges +g_i,-g_i for dual letters.
A nonzero entry must make a neutral trilinear. For continuous real/rational
charges, the five crossed-complement edges fix all sixteen fermion charges
uniquely for any given g. The result is centered and additive without an
affine fermion ansatz: f(m)=sum_i (m_i-1/2)g_i. Compact U(1) requires checking
the charge lattice separately (integer g_i give integer f iff sum g_i is even).
For fixed g, the minimal sufficient oriented subsets have six channels, one
orientation per slot and its opposite on one slot. Weak-only, independent
orientation charges or an even-order cyclic charge group allow alternatives.
Crucially, an unsigned symmetric array on this same complementary support
gives the IDENTICAL charge result. The signs have a separate finite test:
three alternating square ratios multiply to -1 (unsigned +1), invariant
under diagonal rephasing of all 16 states and independent rephasing of the
ten channel components. This is a coefficient invariant, not an experiment.

Only afterward supply block symmetry (g_c,g_c,g_c,g_w,g_w), conventional
nonabelian representations and four-dimensional left Weyl interpretation.
The two free charges give the matched one-family charge plane, not unique
hypercharge. Conventional local and ordinary weak-doublet anomaly tests
are holdouts, not selection rules. Opposite internal parity and extra copies
also pass them. No spacetime chirality or generation count has been selected.

Flavor holdout requires EXTRA assumptions: common generation tensor for the
up- and down-type couplings, flavor-universal kinetic metrics (or the same aligned
canonical normalization), universal weak charged current and no other mass
source. Nonzero up/down effective coefficients then give proportional mass
matrices in that basis and simultaneously diagonalizable left mass squares.
External data test this *effective* identification at the measurement scale,
not an unspecified high-scale boundary condition or a theory with new currents.
Observed charged-current support, not a fit to rates or a joint significance:
Pocanic et al. found BR(pi+ -> pi0 e+ nu)=(1.036 +/- .004 stat +/- .004 syst
+/- .003 normalization)*10^-8, relative to the electronic leptonic mode.
https://arxiv.org/abs/hep-ex/0312030
KLOE found the photon-inclusive BR(K^± -> pi0 e^± nu)=.04965 +/- .00038 stat
+/- .00037 syst. https://arxiv.org/abs/0712.3841 . Independently NA48/2 found
the ratio Ke3/K2pi=.2470 +/- .0009 stat +/- .0004 syst, a different
normalization of the kaon channel. https://arxiv.org/abs/hep-ex/0702015 .
The pion and kaon rates are different transitions, not mutual replications.
With the standard hadronic/weak-current identification they respectively
require V_ud and V_us support. Nondegenerate masses and a monomial CKM cannot
give both in a common up row. No numerical CKM entry is extracted here.
Run: python3 -B -O -m scripts.probe_chiral_carrier_holdout
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product

SLOTS = tuple(range(5))
TOP = 31
EVEN = tuple(m for m in range(32) if m.bit_count() % 2 == 0)
ODD = tuple(m ^ TOP for m in EVEN)
Key = tuple[int, bool]
Entry = tuple[int, int]
Tensor = dict[Key, dict[Entry, int]]
Matrix = tuple[tuple[int, ...], ...]


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise ArithmeticError(reason)


def phase(n: int) -> int:
    return 1 - 2 * (n % 2)


def coefficient(a: int, b: int, i: int, create: bool, grades: tuple[int, ...]) -> int:
    bit = 1 << i
    if bool(b & bit) == create:  # impossible CAR letter
        return 0
    moved = b ^ bit
    if a & moved or (a | moved) != TOP:
        return 0
    swaps = (b & (bit - 1)).bit_count()  # move c_i or a_i past earlier modes
    swaps += sum((moved & ((1 << j) - 1)).bit_count() for j in SLOTS if a >> j & 1)
    return grades[a.bit_count() // 2] * phase(swaps)


def tensor(grades: tuple[int, ...]) -> Tensor:
    return {
        (i, create): {
            (a, b): c
            for a, b in product(EVEN, repeat=2)
            if (c := coefficient(a, b, i, create, grades))
        }
        for i, create in product(SLOTS, (True, False))
    }


def symmetric(t: Tensor) -> bool:
    return all(row.get((b, a)) == c for row in t.values() for (a, b), c in row.items())


def crossed(m: int, i: int) -> int:
    return m ^ TOP ^ (1 << i)


def signed_pair_channels() -> Tensor:
    # Reversion signs are (-1)^(k(k-1)/2) for even degree k=0,2,4.
    rv = tuple(phase(k * (k - 1) // 2) for k in (0, 2, 4))
    t = tensor(rv)
    need(symmetric(t) and not symmetric(tensor((1, 1, 1))), "reversal matters")
    need(
        [g for g in product((1, -1), repeat=3) if g[0] == 1 and symmetric(tensor(g))]
        == [rv],
        "unique normalized real grade-sign choice in this ansatz",
    )
    support: set[Entry] = set()
    for (i, create), row in t.items():
        pairs = {(m, crossed(m, i)) for m in EVEN if bool(m >> i & 1) != create}
        need(len(row) == 8 and set(row) == pairs, "crossed-complement support")
        need(support.isdisjoint(row), "distinct directions must not overlap")
        support.update(row)
    need(len(support) == 80, "forty undirected pair edges")
    return t


def phase_holdout(t: Tensor) -> None:
    # Occupations alone define an all-positive pair tensor; does not assume
    # antisymmetric exterior signs or an experimentally available phase gate.
    unsigned = {
        (i, c): {(m, crossed(m, i)): 1 for m in EVEN if bool(m >> i & 1) != c}
        for i, c in t
    }
    need(
        symmetric(unsigned) and all(t[k].keys() == unsigned[k].keys() for k in t),
        "the unsigned rival passes every support/charge test",
    )
    # For a four-edge cycle with slot sequence i,j,i,j multiply the i
    # entries and divide by the j entries. Every state rephasing cancels;
    # arbitrary channel rephasings leave P_i/P_j, P_i=phase(i+)phase(i-).
    # Three such cycles telescope even the unrestricted independent P_i.
    # +/-1 coefficients equal their own inverses. This fixed-basis data
    # could discriminate tensors only with a separate coherent protocol.
    for candidate, target in ((t, -1), (unsigned, 1)):
        for m in EVEN:
            for i, j, k in combinations(SLOTS, 3):
                state_powers: Counter[int] = Counter()
                channel_powers: Counter[Key] = Counter()
                signs: list[int] = []
                for a, b in ((i, j), (j, k), (k, i)):
                    x = m
                    sign = 1
                    for slot, power in ((a, 1), (b, -1), (a, 1), (b, -1)):
                        y = crossed(x, slot)
                        key = slot, not bool(x >> slot & 1)
                        sign *= candidate[key][x, y]
                        state_powers[x] += power
                        state_powers[y] += power
                        channel_powers[key] += power
                        x = y
                    need(x == m, "square closure")
                    signs.append(sign)
                need(
                    signs == [target] * 3
                    and not any(state_powers.values())
                    and not any(channel_powers.values()),
                    "three-square rephasing invariant",
                )


def homogeneous(t: Tensor, keys: tuple[Key, ...]) -> list[dict[int, int]]:
    """One free alternating amplitude per connected *bipartite* component."""
    adjacent: dict[int, set[int]] = {m: set() for m in EVEN}
    for key in keys:
        for m, n in t[key]:
            adjacent[m].add(n)  # the signed matrices were already checked symmetric
    remaining = set(EVEN)
    basis: list[dict[int, int]] = []
    while remaining:
        root = min(remaining)
        signs = {root: 1}
        queue = [root]
        consistent = True
        while queue:
            m = queue.pop()
            for n in adjacent[m]:
                if n not in signs:
                    signs[n] = -signs[m]
                    queue.append(n)
                elif signs[n] != -signs[m]:
                    consistent = False
        remaining.difference_update(signs)
        if consistent:
            basis.append(signs)
    return basis


def weight(m: int, i: int) -> int:
    """Coefficient of g_i in TWICE the proposed charge, no charge unit chosen."""
    return 2 * ((m >> i) & 1) - 1


def diagonal_holdout(t: Tensor) -> None:
    # For each nonzero entry, verify an identity of linear forms in FIVE
    # independent g's, not selected numerical coefficients or a finite fit.
    for (i, create), row in t.items():
        for a, b in row:
            need(
                all(
                    weight(a, j) + weight(b, j)
                    == (2 * (-1 if create else 1) if j == i else 0)
                    for j in SLOTS
                ),
                "charge neutrality of every entry",
            )
    for r in range(6):
        for dirs in combinations(SLOTS, r):
            need(
                len(homogeneous(t, tuple(k for k in t if k[0] in dirs)))
                == (0 if r == 5 else 2 ** (4 - r)),
                "exhaustive real nullity for fixed component charges",
            )
    # No heuristic minimality: enumerate each oriented subset. All five slots
    # must occur, and at least one needs both orientations, for uniqueness.
    locked: Counter[int] = Counter()
    for count in range(11):
        for keys in combinations(t, count):
            unique = not homogeneous(t, keys)
            need(
                unique == (len({i for i, _ in keys}) == 5 and count >= 6),
                "minimal oriented reach",
            )
            if unique:
                locked[count] += 1
    need(locked == {6: 80, 7: 80, 8: 40, 9: 10, 10: 1}, "all oriented subsets")
    for start in EVEN:
        cycle = [start]
        for i in SLOTS:
            cycle.append(crossed(cycle[-1], i))
        need(len(set(cycle[:-1])) == 5 and cycle[-1] == start, "closed odd walk")
    # Set every g_i=0 and shift from the zero solution to the all-one solution
    # in Z/2. Over the reals it works ONLY if both scalar orientations may
    # have the same compensating charge -2, instead of being opposite.
    shifted = {m: 1 for m in EVEN}
    for key, row in t.items():
        sums = {shifted[a] + shifted[b] for a, b in row}
        need(sums == {2} and {z % 2 for z in sums} == {0}, "2-torsion control")
        need(all(z - 2 == 0 for z in sums), f"independent orientation escape {key}")


def block(m: int) -> tuple[int, int]:
    return (m & 7).bit_count(), (m >> 3).bit_count()


LABELS = {
    (1, 1): "Q",
    (2, 0): "u",
    (2, 2): "d",
    (3, 1): "L",
    (0, 2): "e",
    (0, 0): "N",
}  # u,d,e,N are the conjugate singlet fields


def sector_holdout(t: Tensor) -> None:
    # Read support with external labels AFTER constructing the tensor.
    expected = {
        (True, True): {"QQ", "eu", "Nd"},
        (True, False): {"LQ", "du"},
        (False, True): {"Qu", "LN"},
        (False, False): {"Qd", "Le"},
    }
    for (i, create), row in t.items():
        labels = {"".join(sorted((LABELS[block(a)], LABELS[block(b)]))) for a, b in row}
        need(labels == expected[i < 3, create], "holdout pair-channel dictionary")
    # In the 3+2 specialization set q=-g_c/2, h=g_w. Fermion charge is
    # (3-2p)q + (r-1)h. The prior anomaly/Yukawa plane is the comparison.
    forms = {
        LABELS[block(m)]: (
            -sum(weight(m, i) for i in SLOTS[:3]),
            sum(weight(m, i) for i in SLOTS[3:]) // 2,
        )
        for m in EVEN
    }
    need(
        forms
        == {
            "Q": (1, 0),
            "u": (-1, -1),
            "d": (-1, 1),
            "L": (-3, 0),
            "e": (3, 1),
            "N": (3, -1),
        },
        "matched plane from the pair rule",
    )
    for j in (0, 1):
        q, u, d, l = (forms[s][j] for s in ("Q", "u", "d", "L"))
        need(2 * q + u + d == 3 * q + l == 0, "color and weak mixed local anomalies")
    mult = Counter(LABELS[block(m)] for m in EVEN)
    need(mult == {"Q": 6, "u": 3, "d": 3, "L": 2, "e": 1, "N": 1}, "multiplets")
    need(mult["Q"] // 3 - mult["u"] // 3 - mult["d"] // 3 == 0, "pure color anomaly")
    need(((mult["Q"] + mult["L"]) // 2) % 2 == 0, "ordinary weak-doublet parity")
    # Trace of every odd degree-1 or degree-3 Cartan monomial vanishes, on
    # BOTH internal parities. This implies linear gravitational and cubic U(1)
    # tests for every rational h,q, without finite sampling or anomalies as input.
    for masks in (EVEN, ODD):
        for i in SLOTS:
            need(sum(weight(m, i) for m in masks) == 0, "linear coefficient")
        for i, j, k in product(SLOTS, repeat=3):
            need(
                sum(weight(m, i) * weight(m, j) * weight(m, k) for m in masks) == 0,
                "cubic coefficient",
            )
    # Explicit anomalous weak-only alternative: assign -1 to the two quark
    # singlet types, +1 to Q, 0 to leptons; both weak scalar charges zero.
    baryon = {m: {"Q": 1, "u": -1, "d": -1}.get(LABELS[block(m)], 0) for m in EVEN}
    neutral = {
        key for key, row in t.items() if all(baryon[a] + baryon[b] == 0 for a, b in row)
    }
    need(
        neutral == set(product((3, 4), (True, False)))
        and sum(baryon[m] for m in EVEN if block(m)[1] == 1) == 6,
        "weak-only independent charge with nonzero mixed weak anomaly",
    )


def mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum(x * y for x, y in zip(row, col, strict=True))
            for col in zip(*b, strict=True)
        )
        for row in a
    )


def flavor_controls() -> None:
    # For an arbitrary complex common tensor G, H_u=|v_u|² GG† and
    # H_d=|v_d|² GG†. No fit, three-copy selection or mass prediction.
    # Distinct spectra force monomial mixing; with degeneracy, rotations
    # within the shared degenerate block are a basis ambiguity. A single
    # zero eigenvalue need not produce any degeneracy. A vanishing v leaves
    # an entire sector massless, NOT a prediction for physical mixing angles.
    g: Matrix = ((1, 0, 0), (0, 2, 0), (0, 0, 3))
    h = mul(g, g)
    down = tuple(tuple(9 * x for x in row) for row in h)
    need(mul(h, down) == mul(down, h), "proportional invariant control")
    # Allow a different positive inverse right-handed kinetic metric: even
    # equal unnormalized couplings need not lead to common left eigenvectors.
    metric: Matrix = ((2, 1, 0), (1, 2, 0), (0, 0, 1))  # eigenvalues 1,3,1
    changed = mul(mul(g, metric), g)
    need(mul(h, changed) != mul(changed, h), "kinetic-metric escape")
    # Independent symmetric channel tensors also evade alignment. Different
    # overall normalizations of ONE tensor do not (already checked above).
    second: Matrix = ((1, 1, 0), (1, 2, 0), (0, 0, 3))
    other = mul(second, second)
    need(mul(h, other) != mul(other, h), "independent channel escape")
    # Permutations and rephasings of nondegenerate mass eigenvectors cannot
    # hide a second charged current in the same up row. No branching ratio
    # is predicted: only the support test follows for this effective model.
    measured_links = {(0, 0), (0, 1)}
    need(
        all(not measured_links.issubset(enumerate(p)) for p in permutations(range(3))),
        "pion and kaon electron modes cannot both fit a monomial",
    )


def main() -> None:
    t = signed_pair_channels()
    phase_holdout(t)
    diagonal_holdout(t)
    sector_holdout(t)
    flavor_controls()
    print("16 even states, 10 signed symmetric channels, 40 undirected support edges.")
    print(
        "Unsigned support gives the same charges; three-square ratio: signed -1, unsigned +1."
    )
    print(
        "For fixed dual real characters: unique centered charge; leave one slot out: nullity 1; weak only: 4."
    )
    print(
        "All 1024 oriented subsets: none with five channels suffice; 80 of the 210 six-channel subsets suffice."
    )
    print(
        "3+2 leaves two free weights. One-family anomaly checks pass; no preferred hypercharge, chirality or family count."
    )
    print(
        "One common canonically normalized generation tensor gives aligned masses; independent tensors or metrics evade it."
    )


if __name__ == "__main__":
    main()
