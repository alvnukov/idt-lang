"""Three-state phase invisible to pairwise HOM, visible to native three-port words.

SUPPLIED: three single photons, one in each distinct input port, coherent
three-level internal states, a lossless one-particle spatial unitary, its
bosonic Fock lift, and squared-norm occupation counting that traces the
internal state. Native T/i addresses, preparation, timing/overlap calibration
and number resolution are resources. Unsigned packets do not derive any of
these assumptions. There is no actual source, detector data, fitting,
postselection, probability-law derivation or statistics derivation here.

Let pi=1+i and prepare (e0+e1)/pi, (e1+e2)/pi, (e2+s*e0)/pi for
s in {1,i,-1,-i}. The existing exact native compiler prepares all of them.
Every pair has squared overlap 1/4, so a fixed balanced HOM comparison has
coincidence 3/8. But the oriented Bargmann product
B=<phi0|phi1><phi1|phi2><phi2|phi0>=conj(s)/8 changes. Only pairwise
PROBABILITIES are held fixed, not the full complex Gram matrix. Individual
ray rephasings cancel around B; changing the relative phase within phi2 is
not such a rephasing. This is a loop in preparation-ray space, not a derived
spacetime gauge connection, three-body force or Sorkin third-order rule.

For occupation n and a repeated output list o, put a_sigma=prod_k U[o_k,sigma_k].
The supplied bosonic rule is
 P(n)=sum_{sigma,tau} a_sigma conj(a_tau) prod_k G[tau_k,sigma_k] / prod_j n_j!.
Grouping rho=sigma o tau^-1 gives the distinguishable term, three pair terms
proportional to |Gij|^2, and 2 Re(C_cycle B). A second, independent oracle
multiplies creation-operator polynomials in the resolved spatial/internal
modes and counts their factorial-weighted squared coefficients. Both agree
on all ten occupations, with exact positivity and normalization checks.

NATIVE HITS (words execute left to right): T01,T02 gives
P111=(5/32,1/8,3/32,1/8), in the above order of s. T01,T02,T01 also resolves
orientation: P210(i)=121/1024 versus P210(-i)=153/1024. We exhaust the 259
words of length 0..3 over {T01,T02,T12,i0,i1,i2}, counting each instruction
once and allowing all occupation outputs. Depth two is the first triad
hit; depth three the first imaginary/orientation-sensitive coefficient.
This is minimal ONLY in that enumerated word class, with preparations not
counted. No global optical-circuit minimality or apparatus resource claim.

POSITIVE PAIR-ONLY CONTROL. Independently dephase each internal state in
{e0,e1,e2}. The three diagonal mixtures still have Tr(rho_i rho_j)=1/4,
but Tr(rho0 rho1 rho2)=0. Their eight equiprobable label assignments reduce
to a 1/4 mixture of all-distinct and each of the three two-identical
partitions. This is a positive, normalized classical mixture of supplied
bosonic pair-interference models, not a complete classical-optics theory.
It matches every fixed pair HOM test and removes the cycle term; it cannot
distinguish the four s values. Any model fed ONLY the same pair magnitudes
has this information deficit. Orthogonal particle records are a different
control: they make all overlaps zero and change HOM to 1/2. Relative phase,
local dephasing, and a complete which-particle record are not conflated.

IDEAL-TRITTER COMPARISON ONLY. Counting Fourier phases exactly yields
P111=(2-sum r_ij^2+4 Re B)/9: (7/36,5/36,1/12,5/36) here. This is the
ideal formula in Menssen et al., arXiv:1609.09804, PRL 118,153603 (2017),
DOI 10.1103/PhysRevLett.118.153603. Our native words are DIFFERENT unitaries,
not reconstructions/fits of that apparatus or its measured counts. A truly
equal tritter is not an exact T/i word: every native entry is Gaussian-dyadic,
whereas its squared entry modulus would be 1/3. Approximation is a separate
question. Published source interpretation and imperfections are not tested.

Simultaneously conjugating internal states and the interferometer preserves
the predictions; an oriented readout requires a fixed apparatus convention.
An analytic phase derivative would just differentiate the same polynomial,
not add a new probability rule. Finite controls, not a Lean proof or an
experimental confirmation of IDT.

Run: python3 -B -O -m scripts.probe_packet_triad_phase
"""

from __future__ import annotations

import sys
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, prod
from pathlib import Path

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.gaussian_dyadic_words import (
    CROSS,
    ONE,
    ZERO,
    Gaussian,
    I,
    Matrix,
    Move,
    eye,
    g,
    run,
    synthesize_isometry,
    unitary,
)

State = tuple[Gaussian, ...]
States = tuple[State, ...]
Occupation = tuple[int, ...]
Permutation = tuple[int, ...]
Kernel = dict[Permutation, Gaussian]
Distribution = dict[Occupation, F]
Word = tuple[Move, ...]
UNITS = (ONE, I, g(-1), g(0, -1))
TWO: Word = (("T", 0, 1), ("T", 0, 2))
THREE: Word = TWO + (("T", 0, 1),)
MOVES: tuple[Move, ...] = (
    ("T", 0, 1),
    ("T", 0, 2),
    ("T", 1, 2),
    ("i", 0, 0),
    ("i", 1, 1),
    ("i", 2, 2),
)
CYCLE = (1, 2, 0)


def need(ok: bool, why: str) -> None:
    if not ok:
        raise ArithmeticError(why)


def states(s: Gaussian) -> States:
    return ((CROSS, CROSS, ZERO), (ZERO, CROSS, CROSS), (s * CROSS, ZERO, CROSS))


def gram(vectors: States) -> Matrix:
    return tuple(
        tuple(
            sum((a.star() * b for a, b in zip(x, y, strict=True)), ZERO)
            for y in vectors
        )
        for x in vectors
    )


def overlap_cycles(gram_matrix: Matrix) -> Kernel:
    result = {}
    for permutation in permutations(range(len(gram_matrix))):
        value = ONE
        for j, k in enumerate(permutation):
            value = value * gram_matrix[j][k]
        result[permutation] = value
    return result


def occupations(photons: int, ports: int) -> tuple[Occupation, ...]:
    return tuple(
        tuple(rows.count(j) for j in range(ports))
        for rows in combinations_with_replacement(range(ports), photons)
    )


def amplitudes(u: Matrix, occupation: Occupation) -> dict[Permutation, Gaussian]:
    rows = tuple(j for j, count in enumerate(occupation) for _ in range(count))
    answer = {}
    for permutation in permutations(range(len(rows))):
        value = ONE
        for row, col in zip(rows, permutation, strict=True):
            value = value * u[row][col]
        answer[permutation] = value
    return answer


def kernel_entry(
    amps: dict[Permutation, Gaussian], occupation: Occupation, permutation: Permutation
) -> Gaussian:
    denominator = prod(factorial(n) for n in occupation)
    return g(F(1, denominator)) * sum(
        (
            amps[tuple(permutation[j] for j in tau)] * value.star()
            for tau, value in amps.items()
        ),
        ZERO,
    )


def spatial_kernel(u: Matrix, occupation: Occupation) -> Kernel:
    amps = amplitudes(u, occupation)
    return {
        permutation: kernel_entry(amps, occupation, permutation) for permutation in amps
    }


def probability(kernel: Kernel, weights: Kernel) -> F:
    value = sum(
        (
            coefficient * weights[permutation]
            for permutation, coefficient in kernel.items()
        ),
        ZERO,
    )
    need(value.im == 0 and value.re >= 0, "real nonnegative bosonic probability")
    return value.re


def distribution(u: Matrix, vectors: States) -> Distribution:
    weights = overlap_cycles(gram(vectors))
    result = {
        occupation: probability(spatial_kernel(u, occupation), weights)
        for occupation in occupations(len(vectors), len(u))
    }
    need(sum(result.values(), F(0)) == 1, "all outcomes retained and normalized")
    return result


def fock_oracle(u: Matrix, vectors: States) -> Distribution:
    """Independent creation-polynomial oracle; no permutation/Gram formula."""
    internal = len(vectors[0])
    resolved: dict[Occupation, Gaussian] = {(0,) * (len(u) * internal): ONE}
    for incoming, vector in enumerate(vectors):
        after: defaultdict[Occupation, Gaussian] = defaultdict(lambda: ZERO)
        for occupation, coefficient in resolved.items():
            for port, mode in product(range(len(u)), range(internal)):
                value = coefficient * u[port][incoming] * vector[mode]
                if value != ZERO:
                    target = list(occupation)
                    target[port * internal + mode] += 1
                    after[tuple(target)] = after[tuple(target)] + value
        resolved = dict(after)
    result = dict.fromkeys(occupations(len(vectors), len(u)), F(0))
    for occupation, coefficient in resolved.items():
        coarse = tuple(
            sum(occupation[j * internal : (j + 1) * internal]) for j in range(len(u))
        )
        result[coarse] += coefficient.norm2() * prod(factorial(n) for n in occupation)
    need(sum(result.values(), F(0)) == 1, "resolved Fock norm")
    return result


def basis_states(labels: tuple[int, ...]) -> States:
    return tuple(
        tuple(ONE if j == label else ZERO for j in range(3)) for label in labels
    )


def average_distributions(distributions: tuple[Distribution, ...]) -> Distribution:
    return {
        occupation: sum((d[occupation] for d in distributions), F(0))
        / len(distributions)
        for occupation in distributions[0]
    }


def preparation_and_gauge_checks() -> tuple[int, ...]:
    lengths = []
    for s in UNITS:
        vectors = states(s)
        matrix = gram(vectors)
        need(all(matrix[j][j] == ONE for j in range(3)), "normalized internal states")
        need(
            all(matrix[j][k].norm2() == F(1, 4) for j, k in combinations(range(3), 2)),
            "fixed pair magnitudes",
        )
        weights = overlap_cycles(matrix)
        need(weights[CYCLE] == g(F(1, 8)) * s.star(), "oriented Bargmann phase")
        for vector in vectors:
            word = synthesize_isometry(tuple((value,) for value in vector))
            need(
                tuple(row[0] for row in run(eye(3), word)) == vector,
                "native internal preparation",
            )
            lengths.append(len(word))
        for phases in product(UNITS, repeat=3):
            reframed = tuple(
                tuple(phase * value for value in vector)
                for phase, vector in zip(phases, vectors, strict=True)
            )
            need(overlap_cycles(gram(reframed)) == weights, "ray-gauge invariance")
        common_basis = run(eye(3), (("T", 0, 1), ("i", 2, 2), ("T", 1, 2)))
        rotated = tuple(
            tuple(
                sum(
                    (entry * value for entry, value in zip(row, vector, strict=True)),
                    ZERO,
                )
                for row in common_basis
            )
            for vector in vectors
        )
        need(gram(rotated) == matrix, "common internal basis does not change the triad")
        hom = run(eye(2), (("T", 0, 1),))
        for j, k in combinations(range(3), 2):
            pair = (vectors[j], vectors[k])
            answer = distribution(hom, pair)
            need(
                answer == {(2, 0): F(5, 16), (1, 1): F(3, 8), (0, 2): F(5, 16)},
                "unchanged fixed balanced HOM",
            )
            need(answer == fock_oracle(hom, pair), "independent two-photon oracle")
    return tuple(lengths)


def native_distribution_checks() -> tuple[
    tuple[Distribution, ...], tuple[Distribution, ...]
]:
    tables = []
    for word in (TWO, THREE):
        u = run(eye(3), word)
        need(unitary(u), "native lossless spatial word")
        table = tuple(distribution(u, states(s)) for s in UNITS)
        for s, prediction in zip(UNITS, table, strict=True):
            need(
                prediction == fock_oracle(u, states(s)),
                "independent full internal-state oracle",
            )
            conjugated_u = tuple(tuple(value.star() for value in row) for row in u)
            conjugated_states = tuple(
                tuple(value.star() for value in vector) for vector in states(s)
            )
            need(
                distribution(conjugated_u, conjugated_states) == prediction,
                "simultaneous apparatus/preparation conjugation",
            )
        for labels in ((0, 0, 0), (0, 1, 2)):
            vectors = basis_states(labels)
            need(
                distribution(u, vectors) == fock_oracle(u, vectors),
                "identical/distinguishable oracle",
            )
            for occupation in occupations(3, 3):
                amps = amplitudes(u, occupation)
                denominator = prod(factorial(n) for n in occupation)
                expected = (
                    sum(amps.values(), ZERO).norm2()
                    if labels == (0, 0, 0)
                    else sum((v.norm2() for v in amps.values()), F(0))
                ) / denominator
                need(
                    distribution(u, vectors)[occupation] == expected,
                    "permanent/independent-routing limit",
                )
        tables.append(table)
    need(
        tuple(d[(1, 1, 1)] for d in tables[0])
        == (F(5, 32), F(1, 8), F(3, 32), F(1, 8)),
        "two-mixer triad witness",
    )
    need(
        tuple(d[(2, 1, 0)] for d in tables[1])
        == (F(1, 8), F(121, 1024), F(73, 512), F(153, 1024)),
        "three-mixer orientation witness",
    )
    need(
        len({tuple(d.values()) for d in tables[1]}) == 4,
        "four distinguishable distributions",
    )
    return tables[0], tables[1]


def record_and_dephasing_controls() -> None:
    assignments = tuple(product((0, 1), (1, 2), (2, 0)))
    partition_counts = Counter(
        tuple(int(labels[i] == labels[j]) for i, j in combinations(range(3), 2))
        for labels in assignments
    )
    need(
        set(partition_counts.values()) == {2} and len(partition_counts) == 4,
        "independent dephasing gives four equally weighted partitions",
    )
    mixed_cycles = {
        p: g(F(1, 8))
        * sum(
            (overlap_cycles(gram(basis_states(labels)))[p] for labels in assignments),
            ZERO,
        )
        for p in permutations(range(3))
    }
    need(mixed_cycles[CYCLE] == ZERO, "dephasing removes triad cycle")
    need(
        all(
            mixed_cycles[p] == g(F(1, 4))
            for p in permutations(range(3))
            if sum(i != j for i, j in enumerate(p)) == 2
        ),
        "dephasing preserves pair HOM",
    )
    for word in (TWO, THREE):
        u = run(eye(3), word)
        dephased = average_distributions(
            tuple(distribution(u, basis_states(labels)) for labels in assignments)
        )
        pair_only = average_distributions(
            tuple(
                distribution(u, basis_states(labels))
                for labels in ((0, 1, 2), (0, 0, 1), (0, 1, 0), (1, 0, 0))
            )
        )
        need(dephased == pair_only, "positive pair-only comparator")
        need(
            pair_only
            == average_distributions(tuple(distribution(u, states(s)) for s in UNITS)),
            "zero cycle is the phase-averaged prediction",
        )
        need(
            pair_only != distribution(u, states(ONE)),
            "pair data do not determine triple outputs",
        )
        for s in UNITS:
            tagged = tuple(
                tuple(
                    value if tag == j else ZERO for tag in range(3) for value in vector
                )
                for j, vector in enumerate(states(s))
            )
            need(
                gram(tagged) == eye(3), "unread orthogonal record destroys all overlaps"
            )
            hom = run(eye(2), (("T", 0, 1),))
            need(
                distribution(hom, tagged[:2])[(1, 1)] == F(1, 2),
                "record changes pair HOM",
            )
            need(
                distribution(u, tagged) == distribution(u, basis_states((0, 1, 2))),
                "hidden record gives distinguishable routing",
            )


def finite_word_census() -> tuple[tuple[int, int, int, int], ...]:
    rows = []
    for depth in range(4):
        triad_hits = orientation_hits = 0
        for word in product(MOVES, repeat=depth):
            u = run(eye(3), word)
            coefficients = tuple(
                kernel_entry(amplitudes(u, occupation), occupation, CYCLE)
                for occupation in occupations(3, 3)
            )
            triad_hits += any(c != ZERO for c in coefficients)
            orientation_hits += any(c.im != 0 for c in coefficients)
        rows.append((depth, len(MOVES) ** depth, triad_hits, orientation_hits))
    need(tuple(row[3] for row in rows) == (0, 0, 0, 12), "orientation census")
    need(tuple(row[2] for row in rows[:3]) == (0, 0, 6), "first triad-sensitive depth")
    need(sum(row[1] for row in rows) == 259, "bounded word class only")
    return tuple(rows)


def ideal_tritter_control() -> tuple[F, ...]:
    # Fourier numerator is omega**sum(row*input); each three-photon
    # amplitude has denominator 3*sqrt(3). Reduce integer phase counts,
    # omega+omega^2=-1; no irrational Fourier gate is supplied to a compiler.
    perms = tuple(permutations(range(3)))
    phase = {p: sum(j * p[j] for j in range(3)) % 3 for p in perms}
    for rho in perms:
        counts = Counter(
            (phase[tuple(rho[j] for j in tau)] - phase[tau]) % 3 for tau in perms
        )
        need(counts[1] == counts[2], "real Fourier P111 coefficients")
        coefficient = F(counts[0] - counts[1], 27)
        moved = sum(i != j for i, j in enumerate(rho))
        need(
            coefficient == (F(-1, 9) if moved == 2 else F(2, 9)),
            "ideal tritter cycle coefficient",
        )
    answers = tuple(
        (F(2) - F(3, 4) + 4 * (g(F(1, 8)) * s.star()).re) / 9 for s in UNITS
    )
    need(
        answers == (F(7, 36), F(5, 36), F(1, 12), F(5, 36)), "ideal-tritter comparator"
    )
    need(
        F(1, 3).denominator & (F(1, 3).denominator - 1) != 0,
        "equal-tritter intensity is not dyadic",
    )
    return answers


def main() -> None:
    lengths = preparation_and_gauge_checks()
    two, three = native_distribution_checks()
    record_and_dephasing_controls()
    census = finite_word_census()
    ideal = ideal_tritter_control()
    print(
        f"Exact native internal preparations: {lengths} instruction counts; every pair HOM coincidence=3/8; Bargmann products=conj(s)/8."
    )
    print(f"Bounded census (depth, words, any triad hit, oriented hit): {census}.")
    print(f"T01,T02 P111: {tuple(d[(1, 1, 1)] for d in two)} for s=(1,i,-1,-i).")
    print("T01,T02,T01 full occupation predictions, in that same phase order:")
    for occupation in occupations(3, 3):
        print(f"  {occupation}: {tuple(str(d[occupation]) for d in three)}")
    print(
        f"Ideal equal-tritter P111 comparator: {ideal}; not the native interferometer or measured counts."
    )
    print(
        "Both full probability oracles normalize exactly; identical/distinguishable, independent dephasing, unread-record and ray-gauge controls pass."
    )
    print(
        "Supplied bosonic lift, norm/counting, coherent internal states and addressing; no statistics derivation, local gauge dynamics or empirical claim."
    )


if __name__ == "__main__":
    main()
