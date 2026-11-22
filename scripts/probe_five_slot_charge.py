"""Exact finite benchmark for a supplied five-slot exterior model.

Inputs: five slots split into named color/weak blocks of sizes 3/2, an even
sector, the exterior permutation sign, strict additivity, and traceless
integer block-constant slot charges with the weak charge positive. The
continuous complex exterior representation, block gauge action and its SM
interpretation are separate inputs, not outputs of counting subsets.
"""

from collections import Counter
from collections.abc import Mapping, Sequence
from fractions import Fraction
from itertools import combinations, product
from math import comb, prod

Subset = tuple[int, ...]
Occupation = tuple[int, int]
Edge = tuple[int, int]
SLOTS = tuple(range(5))
EVEN = tuple(s for k in (0, 2, 4) for s in combinations(SLOTS, k))
ODD = tuple(s for k in (1, 3, 5) for s in combinations(SLOTS, k))
PAIRS = tuple(combinations(SLOTS, 2))
QUADS: tuple[Subset, ...] = tuple(combinations(SLOTS, 4))

# Imported left-Weyl representation/field dictionary; the finite enumeration
# checks occupations, multiplicities and charges, not physical identification.
BENCHMARK: dict[Occupation, tuple[str, str, int, int, int]] = {
    # name, supplied exterior block representation, dimension, 6Y, 3(B-L)
    (0, 0): ("sterile neutral basis label", "(1,1)", 1, 0, 3),
    (2, 0): ("u^c", "(3bar,1)", 3, -4, -1),
    (1, 1): ("Q", "(3,2)", 6, 1, 1),
    (0, 2): ("e^c", "(1,1)", 1, 6, 3),
    (3, 1): ("L", "(1,2)", 2, -3, -3),
    (2, 2): ("d^c", "(3bar,1)", 3, 2, -1),
}


def require(condition: bool, failure: object) -> None:
    if not condition:
        raise AssertionError(failure)


def complement(state: Subset) -> Subset:
    return tuple(slot for slot in SLOTS if slot not in state)


def occupation(state: Subset, left: int) -> Occupation:
    k_left = sum(slot < left for slot in state)
    return k_left, len(state) - k_left


def charge(state: Subset, weights: Sequence[int]) -> int:
    return sum(weights[slot] for slot in state)


def primitive_weights(left: int) -> tuple[int, ...]:
    """For these 3+2 and 4+1 coprime sizes, the primitive direction is unique."""
    right = len(SLOTS) - left
    return (-right,) * left + (left,) * right


def moments(states: Sequence[Subset], weights: Sequence[int]) -> tuple[int, ...]:
    return tuple(sum(charge(state, weights) ** n for state in states) for n in range(6))


def trace_controls(weights: Sequence[int], expected: tuple[int, ...]) -> None:
    p1, p2, p4 = sum(weights), sum(x * x for x in weights), sum(x**4 for x in weights)
    even, odd = moments(EVEN, weights), moments(ODD, weights)
    require(even == expected, ("even moments", even, expected))
    if p1 == 0:
        require(odd == tuple((-1) ** n * v for n, v in enumerate(even)), "odd moments")
    # Uniform even occupation has independent fair bits on any proper subset.
    # For epsilon_i = 2*occupied_i - 1, the five-fold parity product is -1.
    centered_fourth = 3 * p2**2 - 2 * p4
    require(
        (even[:5], 2 * even[5])
        == (
            (
                16,
                8 * p1,
                4 * (p1**2 + p2),
                2 * (p1**3 + 3 * p1 * p2),
                p1**4 + 6 * p1**2 * p2 + centered_fourth,
            ),
            p1**5 + 10 * p1**3 * p2 + 5 * p1 * centered_fourth - 120 * prod(weights),
        ),
        "diagonal trace identities through fifth order",
    )


def charge_rows(weights: tuple[int, ...]) -> None:
    rows: Counter[tuple[Occupation, int, int]] = Counter()
    odds: Counter[tuple[Occupation, int, int]] = Counter()
    for states, group in ((EVEN, rows), (ODD, odds)):
        for state in states:
            occ = occupation(state, 3)
            group[occ, charge(state, weights), 3 - 2 * occ[0]] += 1
    require(set(map(complement, EVEN)) == set(ODD), "even/odd complement partition")
    require(len(rows) == len(odds) == len(BENCHMARK), "unlisted charge row")
    print(
        "even (k_c,k_w)  mult  6Y   D | odd complement  mult  6Y   D | imported left-Weyl label / rep"
    )
    for occ, (label, rep, size, q, d) in BENCHMARK.items():
        kc, kw = occ
        dual = (3 - kc, 2 - kw)
        require(rows[occ, q, d] == size == comb(3, kc) * comb(2, kw), ("even row", occ))
        require(odds[dual, -q, -d] == size, ("odd complement row", dual))
        print(
            f"{occ!s:>14} {size:5} {q:3} {d:3} | {dual!s:>14} {size:5} {-q:3} {-d:3} | {label} / {rep}"
        )
    require(
        all(
            charge(complement(state), weights) == -charge(state, weights)
            for state in EVEN
        ),
        "odd charge is not the even complement's negative",
    )
    # The supplied determinant-one action pairs exterior degrees k and n-k
    # as duals via the top wedge; this is not a measured particle dictionary.
    print("Odd rows have conjugate reps under the supplied determinant-one action.")


def signed_permutation_character(signed: bool) -> int:
    """Trace on the even basis of the block double transposition (01)(34)."""
    permutation = (1, 0, 2, 4, 3)
    total = 0
    for state in EVEN:
        moved = tuple(permutation[i] for i in state)
        if tuple(sorted(moved)) == state:
            inversions = sum(a > b for a, b in combinations(moved, 2))
            total += (-1) ** inversions if signed else 1
    return total


def block_anomalies(
    start: int, width: int, charges: Mapping[Subset, int]
) -> tuple[int, int | None]:
    """Finite trace coefficients for the supplied SU(width) action.

    Normalize the quadratic index by the defining trace 2 on diag(1,-1,...),
    and the cubic index by -6 on diag(1,1,-2,...) for width >= 3.  SU(2) has no
    perturbative cubic coefficient; its global doublet parity is separate.
    """
    quadratic = (0,) * start + (1, -1) + (0,) * (len(SLOTS) - start - 2)
    mixed = sum(charge(s, quadratic) ** 2 * charges[s] for s in EVEN)
    require(mixed % 2 == 0, "nonintegral normalized mixed coefficient")
    if width == 2:
        return mixed // 2, None
    cubic = (0,) * start + (1, 1, -2) + (0,) * (len(SLOTS) - start - 3)
    pure = sum(charge(s, cubic) ** 3 for s in EVEN)
    require(pure % 6 == 0, "nonintegral normalized cubic coefficient")
    return mixed // 2, pure // -6


def anomaly_controls(weights: tuple[int, ...], alt: tuple[int, ...]) -> None:
    q = {s: charge(s, weights) for s in EVEN}
    d = {s: 3 - 2 * occupation(s, 3)[0] for s in EVEN}
    alt_q = {s: charge(s, alt) for s in EVEN}
    mixed_color, cubic_color = block_anomalies(0, 3, q)
    mixed_weak, cubic_weak = block_anomalies(3, 2, q)
    require(
        (mixed_color, cubic_color, mixed_weak, cubic_weak) == (0, 0, 0, None),
        "3+2 anomalies",
    )
    doublets = sum(comb(3, kc) for kc, kw in BENCHMARK if kw == 1)
    require(doublets == 4 and doublets % 2 == 0, "weak-doublet parity")
    require(block_anomalies(0, 4, alt_q) == (0, 0), "4+1 mixed or cubic SU4 anomaly")
    require(
        (sum(alt_q.values()), sum(x**3 for x in alt_q.values())) == (0, 0),
        "4+1 U1 anomalies",
    )

    # These are all coefficients of the homogeneous cubic trace of a Q + b D,
    # before multiplying the mixed coefficients by the binomial factors 3.
    cubic_plane = tuple(
        sum(q[s] ** (3 - n) * d[s] ** n for s in EVEN) for n in range(4)
    )
    linear_plane = (sum(q.values()), sum(d.values()))
    require(
        linear_plane == (0, 0) and cubic_plane == (0, 0, 0, 0), "Q,D abelian anomalies"
    )
    require(block_anomalies(0, 3, d) == (0, 0), "SU3^2 D anomaly")
    require(block_anomalies(3, 2, d) == (0, None), "SU2^2 D anomaly")
    require(q[()] == 0 and d[()] == 3, "strict additivity versus affine vacuum shift")
    print("With supplied chiral gauge reps: SU3^3, SU3^2 Q, SU2^2 Q = 0.")
    print("Separate global SU2 (Witten) test: 4 weak doublets, so the parity is even.")
    print(
        f"Q,D linear traces {linear_plane}; cubic coefficients {cubic_plane}; SU3^2 D, SU2^2 D = 0."
    )
    print(
        "D=3-2k_c, labeled 3(B-L) by the imported dictionary, gives D=3 to the empty subset."
    )
    print(
        "Anomaly cancellation does not select Q; strict additivity makes the exterior vacuum neutral."
    )
    print(
        "4+1 is also anomaly-free for its supplied SU4 x U1 local action, but has the wrong spectrum."
    )


def reconstruct_pairs(data: Mapping[Edge, Fraction]) -> tuple[Fraction, ...]:
    """Fit no four-subset data: reconstruct exactly from all ten pair readings."""
    if set(data) != set(PAIRS):
        raise ValueError("expected exactly the ten canonical pair keys")
    # Each slot occurs in four edges; the star sum at i equals 3*x_i + S.
    total = sum(data.values(), start=Fraction()) / 4
    weights = tuple(
        (sum(data[edge] for edge in PAIRS if i in edge) - total) / 3 for i in SLOTS
    )
    bad_edges = tuple((i, j) for i, j in PAIRS if weights[i] + weights[j] != data[i, j])
    if bad_edges:
        raise ValueError(f"inconsistent additive pair data at edges {bad_edges}")
    return weights


def pair_data(weights: Sequence[int | Fraction]) -> dict[Edge, Fraction]:
    return {(i, j): Fraction(weights[i] + weights[j]) for i, j in PAIRS}


def predicts_four_subsets(data: Mapping[Edge, Fraction]) -> dict[Subset, Fraction]:
    weights = reconstruct_pairs(data)
    total = sum(weights, start=Fraction())
    return {quad: total - weights[complement(quad)[0]] for quad in QUADS}


def pair_controls(weights: tuple[int, ...]) -> None:
    generic = (
        Fraction(5, 7),
        Fraction(-2),
        Fraction(3, 5),
        Fraction(11),
        Fraction(-7, 3),
    )
    require(
        reconstruct_pairs(pair_data(generic)) == generic,
        "generic nonneutral rational input",
    )
    # A fixed synthetic input in canonical edge order, separate from the
    # four-subset target and from the benchmark used to verify recovery.
    observed_pairs = dict(
        zip(PAIRS, map(Fraction, (-4, -4, 1, 1, -4, 1, 1, 1, 1, 6)), strict=True)
    )
    recovered = reconstruct_pairs(observed_pairs)
    require(
        recovered == weights and sum(recovered) == 0, "traceless pair reconstruction"
    )
    require(Counter(recovered) == {-2: 3, 3: 2}, "reconstructed block multiplicities")

    for edge in PAIRS:
        mutated = dict(observed_pairs)
        mutated[edge] += 1
        try:
            reconstruct_pairs(mutated)
        except ValueError:
            continue
        raise AssertionError(("single-edge mutation accepted", edge))

    # Indexed separately from reconstruction; pair data alone never reads it.
    supplied_holdout = dict(
        zip(QUADS, (Fraction(-3),) * 2 + (Fraction(2),) * 3, strict=True)
    )
    predictions = predicts_four_subsets(observed_pairs)
    require(
        predictions == supplied_holdout, "synthetic four-subset holdout predictions"
    )
    destructive_swap = (3, 1, 2, 0, 4)
    moved_pairs = {
        (i, j): observed_pairs[
            min(destructive_swap[i], destructive_swap[j]),
            max(destructive_swap[i], destructive_swap[j]),
        ]
        for i, j in PAIRS
    }
    require(
        reconstruct_pairs(moved_pairs) == tuple(weights[i] for i in destructive_swap),
        "relabeled pairs",
    )
    require(
        sum(
            value != supplied_holdout[quad]
            for quad, value in predicts_four_subsets(moved_pairs).items()
        )
        == 2,
        "cross-block relabel with holdout labels fixed must spoil exactly two predictions",
    )
    predicted_labels = ", ".join(map(str, predictions.values()))
    print(
        f"All 10 pair mutations rejected; 5 blind synthetic four-subset predictions matched: {predicted_labels}."
    )
    print(
        "A cross-block relabel keeps pairs additive but breaks 2 of 5 fixed-label holdout predictions."
    )


def center_kernel_control() -> None:
    """Check center phases in sixth-turn units, conditional on the block embedding."""
    # For the supplied unitary action, wedge^2 being identity implies all
    # eigenvalue pairs multiply to 1, hence the five eigenvalues are a common
    # +/-1. Determinant 1 in odd dimension forces +1. Therefore the even
    # exterior action adds no kernel to the block embedding into SU(5).
    # For diag(e^-2it A, e^3it B) to be the identity, det(A)=det(B)=1 forces
    # e^it to be a sixth root, and both A and B to be central.
    kernel = {
        (a, b, t)
        for a, b, t in product(range(3), range(2), range(6))
        if all(
            (kc * (2 * a - 2 * t) + kw * (3 * b + 3 * t)) % 6 == 0
            for kc, kw in (occupation(s, 3) for s in EVEN)
        )
    }
    require(
        kernel == {(t % 3, t % 2, t) for t in range(6)},
        "center kernel is not diagonal Z6",
    )
    print(
        "Supplied block embedding: finite center-phase kernel Z6 generated by residues (1,1,1)."
    )


def main() -> None:
    weights, alt = primitive_weights(3), primitive_weights(4)
    expected, other = (16, 0, 120, 0, 2280, 4320), (16, 0, 80, 0, 680, -240)
    print(
        "Inputs: 3+2 block labels, supplied exterior action, even parity, additive traceless Q=6Y."
    )
    print(f"Primitive weights: {weights}; 4+1 negative spectrum control: {alt}.")
    charge_rows(weights)
    signed, unsigned = (
        signed_permutation_character(True),
        signed_permutation_character(False),
    )
    require(
        (signed, unsigned) == (0, 4), ("signed/unsigned character", signed, unsigned)
    )
    print(
        f"Trace of (01)(34) over 16 even states: exterior {signed}, unsigned {unsigned}."
    )
    trace_controls(weights, expected)
    trace_controls(alt, other)
    trace_controls((1, -3, 2, 7, -1), (16, 48, 400, 2736, 22408, 179808))
    q_spectrum = Counter(charge(s, weights) for s in EVEN)
    alt_spectrum = Counter(charge(s, alt) for s in EVEN)
    require(q_spectrum != alt_spectrum, "4+1 unexpectedly matched Q spectrum")
    print(f"Charge moments n=0..5: 3+2 {expected}; 4+1 {other}.")
    print(f"4+1 spectrum (charge,multiplicity): {tuple(sorted(alt_spectrum.items()))}.")
    anomaly_controls(weights, alt)
    pair_controls(weights)
    center_kernel_control()
    print(
        "Scope: conditional finite benchmark, not a derivation of block rotations or gauge physics."
    )
    print(
        "No new empirical data, bosons, masses, dynamics, or Standard Model confirmation."
    )


if __name__ == "__main__":
    main()
