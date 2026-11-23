"""Audit positive address quotients, integer contrasts, and a network ceiling.

The carrier and two factored contact layouts are fixed as in the native phase
coincidence probe. Side readers, a four-outcome relabel, settings-independent
sampling, and complete records are supplied in the network completion; none
are derived from the contact law. Integer pushforwards are not probabilities.

Run: python3 -B -E -O -m scripts.probe_raw_packet_phase_quotients
"""

import json
from collections import Counter
from dataclasses import asdict, dataclass
from fractions import Fraction as F
from itertools import combinations, product

from scripts.probe_native_phase_coincidence import (
    COLORS,
    SWAP,
    Pair,
    colored_maps,
    compose,
    contact_layout,
    edge_labels,
    equalizer_classes,
    half_filled,
    inverse,
    walk,
)
from scripts.probe_octagon_three_contexts import (
    Maps,
    Perm,
    action,
    affine,
    check_minimal_action,
    require,
    two_rings,
)
from scripts.probe_two_source_phase_network import (
    AXIS_PAIRS,
    BitPair,
    Experiment,
    Outcome,
    functional,
)

Move = tuple[Perm, Perm]
Cells = dict[Pair, frozenset[Pair]]
Vector = dict[Pair, int]
SIGNS = (-1, 1)
ALICE = tuple(product(SIGNS, repeat=3))
CHARLIE = tuple(product(SIGNS, repeat=6))
BOB: tuple[BitPair, ...] = ((0, 0), (0, 1), (1, 0), (1, 1))
SETTINGS = tuple(product(range(3), range(6)))
ACTIVE: dict[Pair, int] = {
    (x, 2 * k + sign_column): -1 if row == sign_column == 1 else 1
    for k, axes in enumerate(AXIS_PAIRS)
    for row, x in enumerate(axes)
    for sign_column in range(2)
}


@dataclass(frozen=True)
class CellCensus:
    cells: int
    cell_size: int
    raw_local_address_constant: tuple[bool, bool]


@dataclass(frozen=True)
class CellComparison:
    left: str
    right: str
    equal_roots: int


@dataclass(frozen=True)
class QuotientReport:
    raw_addresses: int
    census: dict[str, CellCensus]
    distinct_pairs: tuple[CellComparison, ...]
    generator_order: tuple[str, ...]
    generator_root_checks: int
    generator_equal_cell_roots: dict[str, dict[str, int]]
    signatures: dict[str, str]
    matchings_commuting_with_w: int
    descended_matchings: dict[str, int]


@dataclass(frozen=True)
class ContrastReport:
    basis_pairs: int
    odd_action_checks: dict[str, int]
    pushforward_checks: dict[str, int]
    selected_eigenvalue: dict[str, int]
    mirror_checks: dict[str, int]
    positive_count_controls: dict[str, int]
    signed_coefficients_on_sample: tuple[int, int]
    positive_counts_on_same_sample: tuple[int, int]


@dataclass(frozen=True)
class ContactCompletion:
    class_rails: int
    relabel_class_counts: tuple[int, ...]
    outcome_address_counts: tuple[int, ...]
    exact_forward_records: int
    setting_pairs: int
    setting_mass: tuple[str, ...]
    score: str


@dataclass(frozen=True)
class NetworkReport:
    pointwise_tables: int
    pointwise_histogram: dict[int, int]
    normalized_mixture_ceiling: int
    requires_independent_source_measures: bool
    contact_completions: dict[str, ContactCompletion]
    leaky_score: str
    leaky_setting_mass: tuple[str, ...]
    leaky_distinct_b_outcomes: int
    leaky_in_completion_class: bool
    postselected_score: str
    original_unfiltered_score: str
    postselected_acceptance: str
    postselected_distinct_acceptance_sets: int
    postselected_in_completion_class: bool
    unassigned_discard_score: None


@dataclass(frozen=True)
class Report:
    quotient: QuotientReport
    contrast: ContrastReport
    network: NetworkReport
    scope: str


def move_address(move: Move, root: Pair) -> Pair:
    return move[0][root[0]], move[1][root[1]]


def cells_for(pairs: tuple[Pair, ...], generators: tuple[Move, ...]) -> Cells:
    cells: Cells = {}
    for root in pairs:
        if root in cells:
            continue
        orbit = {root}
        pending = [root]
        while pending:
            point = pending.pop()
            for move in generators:
                image = move_address(move, point)
                if image not in orbit:
                    orbit.add(image)
                    pending.append(image)
        cell = frozenset(orbit)
        for point in cell:
            require(point not in cells, "orbits overlap")
            cells[point] = cell
    require(set(cells) == set(pairs), "orbits did not cover the raw product")
    return cells


def quotient_audit(
    maps: Maps,
    w: Perm,
    z: Perm,
    pairs: tuple[Pair, ...],
) -> tuple[QuotientReport, dict[str, Cells]]:
    ident = tuple(range(len(w)))
    s, h, d = (z, z), (w, inverse(w)), (w, w)
    left, right = (w, ident), (ident, w)
    partitions = {
        name: cells_for(pairs, gens)
        for name, gens in {
            "I": (),
            "S": (s,),
            "H": (h,),
            "D": (d,),
            "join": (h, d),
            "independent": (left, right),
        }.items()
    }
    gen_order = ("S", "H", "D", "L")
    generators = dict(zip(gen_order, (s, h, d, left), strict=True))
    local = tuple((p, ident) for p in maps.values()) + tuple(
        (ident, p) for p in maps.values()
    )
    commuting = sum(all(compose(p, w) == compose(w, p) for p in move) for move in local)
    require(commuting == len(local) == 6, "not all six local matchings commute with W")
    census, signatures, equality_roots, descended = {}, {}, {}, {}
    checks = 0
    for name, cells in partitions.items():
        unique = set(cells.values())
        (size,) = {len(cell) for cell in unique}
        constant_i = all(len({i for i, _ in cell}) == 1 for cell in unique)
        constant_j = all(len({j for _, j in cell}) == 1 for cell in unique)
        census[name] = CellCensus(len(unique), size, (constant_i, constant_j))
        equality_roots[name] = {
            key: sum(cells[root] == cells[move_address(move, root)] for root in pairs)
            for key, move in generators.items()
        }
        checks += len(pairs) * len(generators)
        require(
            set(equality_roots[name].values()) <= {0, len(pairs)},
            "uneven absorption by root",
        )
        signatures[name] = "".join(
            str(int(count == len(pairs))) for count in equality_roots[name].values()
        )
        descended[name] = sum(
            all(
                frozenset(move_address(move, p) for p in cells[root])
                == cells[move_address(move, root)]
                for root in pairs
            )
            for move in local
        )
        require(descended[name] == 6, f"not all six local matchings descend to {name}")
    distinct = tuple(
        CellComparison(a, b, sum(partitions[a][p] == partitions[b][p] for p in pairs))
        for a, b in combinations(partitions, 2)
    )
    expected = {
        "I": (256, 1, "0000"),
        "S": (128, 2, "1000"),
        "H": (64, 4, "1100"),
        "D": (64, 4, "1010"),
        "join": (32, 8, "1110"),
        "independent": (16, 16, "1111"),
    }
    require(
        {
            name: (row.cells, row.cell_size, signatures[name])
            for name, row in census.items()
        }
        == expected,
        "unexpected quotient census",
    )
    require(
        len(distinct) == 15 and all(row.equal_roots == 0 for row in distinct),
        "distinct named quotients unexpectedly agree at a root",
    )
    return QuotientReport(
        len(pairs),
        census,
        distinct,
        gen_order,
        checks,
        equality_roots,
        signatures,
        commuting,
        descended,
    ), partitions


def moved(move: Move, vector: Vector) -> Vector:
    return {move_address(move, p): value for p, value in vector.items()}


def scaled(c: int, vector: Vector) -> Vector:
    return {p: c * value for p, value in vector.items() if c * value}


def pushforward(reps: dict[Pair, Pair], vector: Vector) -> Vector:
    out: Counter[Pair] = Counter()
    for p, value in vector.items():
        out[reps[p]] += value
    return {p: value for p, value in out.items() if value}


def contrast_audit(
    maps: Maps,
    w: Perm,
    z: Perm,
    pairs: tuple[Pair, ...],
    partitions: dict[str, Cells],
) -> ContrastReport:
    w_inv = inverse(w)
    k: Move = (w, w)
    h: Move = (w, w_inv)
    ident = tuple(range(len(w)))
    require(
        compose(w, w) == z
        and compose(z, z) == ident
        and all(i != zi for i, zi in enumerate(z)),
        "W² must be the free central half-turn Z",
    )
    (mirror,) = (f for f in colored_maps(maps, SWAP) if f[0] == 0)
    require(
        compose(mirror, w) == compose(w_inv, mirror), "menu mirror did not reverse W"
    )
    reps = {
        name: {p: min(cell) for p, cell in partitions[name].items()}
        for name in ("H", "D")
    }
    mirrors = {"left": (mirror, ident), "right": (ident, mirror)}
    mir_counts: Counter[str] = Counter()
    push_counts: Counter[str] = Counter()
    positive_counts: Counter[str] = Counter()
    action_counts: Counter[str] = Counter()
    signed_sample, positive_sample = (0, 0), (0, 0)
    for i, j in pairs:
        p, q = (i, j), (z[i], j)
        v: Vector = {p: 1, q: -1, (i, z[j]): -1, (z[i], z[j]): 1}
        kv, hv = moved(k, v), moved(h, v)
        require(
            hv == scaled(-1, kv) and moved(k, kv) == v, "odd×odd monodromy mismatch"
        )
        action_counts["H=-K"] += 1
        require(
            kv
            == {
                (w[i], w[j]): 1,
                (z[w[i]], w[j]): -1,
                (w[i], z[w[j]]): -1,
                (z[w[i]], z[w[j]]): 1,
            },
            "D must be K on odd×odd",
        )
        action_counts["D=K"] += 1
        for name, sign in (("H", -1), ("D", 1)):
            root, opposite = reps[name][p], reps[name][q]
            sv = pushforward(reps[name], v)
            require(
                root != opposite and sv == {root: 2, opposite: -2},
                "wrong integer pushforward",
            )
            # The quotient map identifies its positive generator with 1.
            require(
                pushforward(reps[name], kv) == scaled(sign, sv),
                "incorrect signed K sector",
            )
            push_counts[name] += 1
            negated = scaled(-1, v)
            counts = pushforward(
                reps[name], {point: abs(value) for point, value in v.items()}
            )
            require(
                counts == {root: 2, opposite: 2}
                and pushforward(reps[name], negated) == scaled(-1, sv)
                and pushforward(reps[name], {r: abs(a) for r, a in negated.items()})
                == counts,
                "sign reversal must negate the contrast but leave positive counts unchanged",
            )
            if p == (0, 0):
                signed_sample = (sv[root], sv[opposite])
                positive_sample = (counts[root], counts[opposite])
            positive_counts[name] += 1
        for side, move in mirrors.items():
            require(
                moved(move, kv) == scaled(-1, moved(k, moved(move, v))),
                f"{side} menu mirror did not negate K on odd×odd",
            )
            for src, dst in (("H", "D"), ("D", "H")):
                require(
                    {move_address(move, r) for r in partitions[src][p]}
                    == partitions[dst][move_address(move, p)],
                    "mirror did not exchange cells",
                )
            mir_counts[side] += 1
    return ContrastReport(
        len(pairs),
        dict(action_counts),
        dict(push_counts),
        {"H": -1, "D": 1},
        dict(mir_counts),
        dict(positive_counts),
        signed_sample,
        positive_sample,
    )


def pointwise_histogram() -> Counter[int]:
    histogram: Counter[int] = Counter()
    for a, b, c in product(ALICE, BOB, CHARLIE):
        records: Experiment = {(x, z): {(a[x], *b, c[z]): F(1)} for x, z in SETTINGS}
        score = functional(records)
        require(
            score.denominator == 1, "pointwise complete record score is not integral"
        )
        histogram[score.numerator] += 1
    return histogram


def complete_mass(records: Experiment) -> tuple[str, ...]:
    require(set(records) == set(SETTINGS), "incomplete setting table")
    require(
        all(p >= 0 for row in records.values() for p in row.values()),
        "negative probability",
    )
    masses = {sum(row.values(), F(0)) for row in records.values()}
    require(masses == {F(1)}, "non-unit mass in a setting table")
    return tuple(str(mass) for mass in sorted(masses))


def bob_axis_signs(b: BitPair) -> tuple[int, int, int]:
    b1, b2 = b
    return 1 - 2 * b2, 1 - 2 * b1, -(1 - 2 * b1) * (1 - 2 * b2)


def contact_completion(
    maps: Maps,
    w: Perm,
    pairs: tuple[Pair, ...],
    cells: Cells,
    pi: str,
) -> ContactCompletion:
    n = len(w)
    dynamic, labels = equalizer_classes(w, colored_maps(maps, pi), pairs)
    require(
        dynamic == set(cells.values()),
        "physical equalizers do not give the audited cells",
    )
    residues = edge_labels(maps["C"])
    layout = contact_layout(n, pairs, labels, tuple(residues[i] for i, _ in pairs))
    cycle = tuple(min(walk(w, i)) for i in range(n))
    left_reader = dict(zip(sorted(set(cycle)), BOB, strict=True))
    coarse: dict[int, BitPair] = {}
    decoded: list[BitPair] = []
    forward = 0
    for (i, _), inp, intended in zip(
        pairs, layout.inputs, layout.contacts, strict=True
    ):
        offered = half_filled(inp, layout.contacts)
        require(
            offered == (intended,),
            "complete completion needs one actual forward contact",
        )
        forward += 1
        out = inp ^ offered[0]
        rails = (out >> (2 * n)) & ((1 << layout.class_rails) - 1)
        require(rails.bit_count() == 1, "no single positive physical class rail")
        label = rails.bit_length() - 1
        bit_pair = left_reader[cycle[i]]
        require(
            coarse.setdefault(label, bit_pair) == bit_pair,
            "coarse reader depends on residue",
        )
        decoded.append(coarse[label])
    # Uniform normalized raw-address mixture. The supplied Alice signs depend
    # only on i through its W-cycle; Charlie uses a constant local sign.
    records: Experiment = {setting: {} for setting in SETTINGS}
    for (i, _), b in zip(pairs, decoded, strict=True):
        a = bob_axis_signs(left_reader[cycle[i]])
        for (x, z), row in records.items():
            outcome = (a[x], *b, 1)
            row[outcome] = row.get(outcome, F(0)) + F(1, len(pairs))
    relabel_census = Counter(coarse.values())
    address_census = Counter(decoded)
    mass = complete_mass(records)
    score = functional(records)
    require(
        score == 6
        and layout.class_rails == len(coarse) == 64
        and set(relabel_census.values()) == {16}
        and set(address_census.values()) == {64},
        "complete physical contact mixture should saturate the deterministic ceiling",
    )
    return ContactCompletion(
        layout.class_rails,
        tuple(relabel_census[b] for b in BOB),
        tuple(address_census[b] for b in BOB),
        forward,
        len(records),
        mass,
        str(score),
    )


def network_audit(
    maps: Maps,
    w: Perm,
    pairs: tuple[Pair, ...],
    partitions: dict[str, Cells],
) -> NetworkReport:
    histogram = pointwise_histogram()
    require(
        histogram == {-6: 256, -2: 768, 2: 768, 6: 256}, "wrong deterministic census"
    )
    # Every settings-independent normalized mixture is a convex combination
    # of these pointwise scores (linearity of functional), correlated or not.
    completions = {
        mode: contact_completion(maps, w, pairs, partitions[mode], pi)
        for mode, pi in (("H", SWAP), ("D", COLORS))
    }

    leak: Experiment = {}
    original: Experiment = {}
    selected: Experiment = {}
    accepted_masses = set()
    accepted_sets = set()
    used: set[BitPair] = set()
    for x, z in SETTINGS:
        # Active coefficient from the 3×CHSH functional; set a half-sampling
        # predicate on inactive settings too so the example reports all 18.
        sign = ACTIVE.get((x, z), 1)
        winning = tuple(b for b in BOB if bob_axis_signs(b)[x] == sign)
        accepted_sets.add(winning)
        used.add(winning[0])
        leak[x, z] = {(1, *winning[0], 1): F(1)}
        original[x, z] = {(1, *b, 1): F(1, 4) for b in BOB}
        accepted: dict[Outcome, F] = {(1, *b, 1): F(1, 4) for b in winning}
        mass = sum(accepted.values())
        accepted_masses.add(mass)
        selected[x, z] = {outcome: prob / mass for outcome, prob in accepted.items()}
    leaky_mass = complete_mass(leak)
    complete_mass(original)
    complete_mass(selected)
    leaky_score, original_score, conditional_score = map(
        functional, (leak, original, selected)
    )
    require(
        leaky_score == conditional_score == 12
        and original_score == 0
        and len(used) > 1
        and accepted_masses == {F(1, 2)}
        and len(accepted_sets) > 1,
        "incorrect out-of-class controls",
    )
    (acceptance,) = accepted_masses
    # A discarded/absent event has no outcome assigned by the conditional model.
    return NetworkReport(
        sum(histogram.values()),
        dict(histogram),
        max(histogram),
        False,
        completions,
        str(leaky_score),
        leaky_mass,
        len(used),
        False,
        str(conditional_score),
        str(original_score),
        str(acceptance),
        len(accepted_sets),
        False,
        None,
    )


def run_probe() -> Report:
    maps = two_rings(affine(5, 0))
    check_minimal_action(maps)
    w, z = action(maps, "ABC"), action(maps, "ABAB")
    require(len(w) == 16, "wrong frozen carrier size")
    pairs = tuple(product(range(len(w)), range(len(w))))
    quotient, partitions = quotient_audit(maps, w, z, pairs)
    return Report(
        quotient,
        contrast_audit(maps, w, z, pairs, partitions),
        network_audit(maps, w, pairs, partitions),
        "Finite checks and a conditional deterministic completion ceiling. No normalized "
        "probability is read off the integer pushforward. Local ±1 readers, a setting-independent "
        "coarse four-result reader, a normalized setting-independent address distribution, and "
        "complete records are premises. Leaked settings or conditional acceptance are outside "
        "this class; absent or undetected offers get no assigned outcome here. The ceiling "
        "does not constrain the bare contact primitive without these premises.",
    )


def main() -> None:
    print(json.dumps(asdict(run_probe()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
