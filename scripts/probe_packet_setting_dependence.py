"""Exact setting-dependence control for the fixed H/D raw-packet carrier.

Write S for the uniform active setting pair and λ for the raw address pair.
With fixed deterministic readers (Alice uses x, Charlie uses z, Bob uses his
class rail), every strategy wins at most three cells per CHSH plaque: the four
signed scores have product -1. Thus Q = P_S P_λ has win probability q <= 3/4,
regardless of source independence. Coarse graining the KL divergence on win
versus loss gives I(S;λ) >= D_bin(p || q) >= D_bin(p || 3/4) for p >= 3/4.
The reported score is T = 12(2p - 1).

For equality at p > 3/4, strict monotonicity requires q = 3/4, hence every
P_λ-supported strategy must have three wins on each plaque. Equality in the
binary coarse graining requires a constant P/Q on wins and another on losses,
including a zero loss ratio at p = 1. Each supported address therefore has a
plaque likelihood table with three equal positive entries and one different
entry. Its determinant is nonzero. This rules out J(i,j|x,z)=L_x(i) R_z(j)
attaining equality, not side-local models exceeding T=6 at an unspecified
cost. It does not rule out J(i,j|x,z)=L(i) R_{x,z}(j), as witnessed below.

For uniform sampling on all 18 pairs, conditioning on whether the pair is
active lower-bounds the information by 2/3 of the active cost. The construction
uses the unconditional raw prior on inactive pairs, so this bound is also
tight. Supplied readers and sampling laws are controls, not derived packet
probabilities, observed leakage, or a claim of quantum reconstruction.

Run: python3 -B -E -O -m scripts.probe_packet_setting_dependence
"""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import asdict, dataclass
from fractions import Fraction as F
from itertools import product
from math import fsum, isclose, log2

from scripts.probe_native_phase_coincidence import (
    COLORS,
    SWAP,
    Pair,
    colored_maps,
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
    require,
    two_rings,
)
from scripts.probe_raw_packet_phase_quotients import (
    ACTIVE,
    BOB,
    SETTINGS,
    SIGNS,
    bob_axis_signs,
    cells_for,
    complete_mass,
    pointwise_histogram,
)
from scripts.probe_two_source_phase_network import (
    AXIS_PAIRS,
    BitPair,
    Experiment,
    Outcome,
    functional,
)

AddressLaw = dict[Pair, F]
Sampling = dict[Pair, AddressLaw]
Signs = tuple[int, int, int]
NULL = F(3, 4)
OUTCOMES: tuple[Outcome, ...] = tuple(
    (a, *b, c) for a, b, c in product(SIGNS, BOB, SIGNS)
)


@dataclass(frozen=True)
class Strategy:
    alice: Signs
    bob: BitPair
    charlie: tuple[int, ...]

    def outcome(self, setting: Pair) -> Outcome:
        x, z = setting
        return self.alice[x], *self.bob, self.charlie[z]

    def wins(self, setting: Pair) -> bool:
        a, b1, b2, c = self.outcome(setting)
        x, _ = setting
        return ACTIVE[setting] * a * bob_axis_signs((b1, b2))[x] * c == 1


@dataclass(frozen=True)
class ContactReport:
    class_rails: int
    classes_per_bob_outcome: tuple[int, ...]
    addresses_per_bob_outcome: tuple[int, ...]
    exact_forward_records: int


@dataclass(frozen=True)
class PacketReaders:
    strategies: dict[Pair, Strategy]
    instruments: dict[str, ContactReport]


@dataclass(frozen=True)
class SampleReport:
    win_probability: str
    score: str
    complete_settings: int
    setting_mass: tuple[str, ...]
    no_postselection: bool
    observable_nonsignaling: bool
    conditionally_independent_sources: bool
    uniform_raw_address_prior_active_and_all: bool
    side_local_factorization: bool
    equality_plaquette_checks: int
    equality_abs_determinant: str
    active_information_bits_approx: float
    all_settings_information_bits_approx: float


@dataclass(frozen=True)
class Report:
    raw_addresses: int
    strategy_multiplicities: dict[int, int]
    active_pairs: int
    active_win_counts_per_address: tuple[int, ...]
    active_winning_address_counts: tuple[int, ...]
    winning_and_losing_outcome_address_counts: tuple[int, int]
    inactive_outcome_address_count: int
    independent_setting_ceiling: int
    instruments: dict[str, ContactReport]
    samples: tuple[SampleReport, ...]
    scope: str


def _multiply(a: Signs, u: Signs) -> Signs:
    return a[0] * u[0], a[1] * u[1], a[2] * u[2]


def _physical_bob(
    maps: Maps, w: Perm, targets: dict[Pair, BitPair], colors: str
) -> tuple[dict[Pair, BitPair], ContactReport]:
    pairs = tuple(targets)
    physical_classes, labels = equalizer_classes(w, colored_maps(maps, colors), pairs)
    right_w = inverse(w) if colors == SWAP else w
    require(
        physical_classes == set(cells_for(pairs, ((w, right_w),)).values()),
        "physical class rail partition does not match the H/D quotient",
    )
    residues = edge_labels(maps["C"])
    n = len(w)
    layout = contact_layout(n, pairs, labels, tuple(residues[i] for i, _ in pairs))
    coarse: dict[int, BitPair] = {}
    for pair, label in zip(pairs, labels, strict=True):
        require(
            coarse.setdefault(label, targets[pair]) == targets[pair],
            "Bob's fixed reader must be constant on each whole physical class",
        )
    decoded: dict[Pair, BitPair] = {}
    for pair, occupancy, intended in zip(
        pairs, layout.inputs, layout.contacts, strict=True
    ):
        offered = half_filled(occupancy, layout.contacts)
        require(offered == (intended,), "not exactly one actual forward contact")
        output = occupancy ^ offered[0]
        rails = (output >> (2 * n)) & ((1 << layout.class_rails) - 1)
        require(rails.bit_count() == 1, "forward output lacks its unique class rail")
        decoded[pair] = coarse[rails.bit_length() - 1]
        require(decoded[pair] == targets[pair], "physical class readout mismatch")

    class_counts = Counter(coarse.values())
    address_counts = Counter(decoded.values())
    require(
        layout.class_rails == 64
        and set(class_counts.values()) == {16}
        and set(address_counts.values()) == {64}
        and len(decoded) == 256,
        "contact completion has unexpected support",
    )
    return decoded, ContactReport(
        layout.class_rails,
        tuple(class_counts[b] for b in BOB),
        tuple(address_counts[b] for b in BOB),
        len(decoded),
    )


def make_packet_readers() -> PacketReaders:
    maps = two_rings(affine(5, 0))
    w = action(maps, "ABC")
    roots = sorted({min(walk(w, i)) for i in range(len(w))})
    w_cycles = tuple(walk(w, root) for root in roots)
    require(
        len(w) == 16 and len(w_cycles) == 4 and {len(c) for c in w_cycles} == {4},
        "unexpected carrier or W-cycle census",
    )
    encode_b = {bob_axis_signs(b): b for b in BOB}
    left: dict[int, Signs] = {}
    right_axis: dict[int, Signs] = {}
    right_reader: dict[int, tuple[int, ...]] = {}
    for cycle, a in zip(w_cycles, encode_b, strict=True):
        # Alice's labels are odd parity. The paired set of right labels is even.
        u = _multiply((-1, -1, -1), a)
        for index, site in enumerate(cycle):
            left[site], right_axis[site] = a, u
            # R is the parity of position in the canonically rooted W-cycle.
            right_reader[site] = tuple(
                entry
                for k, l in AXIS_PAIRS
                for entry in ((u[l], -u[l]) if index % 2 else (u[k], u[k]))
            )
    targets = {
        (i, j): encode_b[_multiply(left[i], right_axis[j])]
        for i, j in product(range(len(w)), repeat=2)
    }
    decoded_h, instruments_h = _physical_bob(maps, w, targets, SWAP)
    decoded_d, instruments_d = _physical_bob(maps, w, targets, COLORS)
    require(decoded_h == decoded_d, "H and D coarse readouts differ")
    return PacketReaders(
        {
            (i, j): Strategy(left[i], decoded_h[i, j], right_reader[j])
            for i, j in targets
        },
        {"H": instruments_h, "D": instruments_d},
    )


def make_sampling(readers: PacketReaders, p: F) -> Sampling:
    if not NULL <= p <= 1:
        raise ValueError("p must be in [3/4, 1]")
    return {
        setting: {
            point: (
                (p / 192 if strategy.wins(setting) else (1 - p) / 64)
                if setting in ACTIVE
                else F(1, 256)
            )
            for point, strategy in readers.strategies.items()
        }
        for setting in SETTINGS
    }


def make_records(readers: PacketReaders, sampling: Sampling) -> Experiment:
    require(set(sampling) == set(SETTINGS), "a setting row is missing")
    records: Experiment = {}
    for setting, prior in sampling.items():
        require(set(prior) == set(readers.strategies), "a raw address is missing")
        require(all(q >= 0 for q in prior.values()), "negative sampling weight")
        row = dict.fromkeys(OUTCOMES, F(0))
        for point, q in prior.items():
            row[readers.strategies[point].outcome(setting)] += q
        records[setting] = row
    # Unit mass is checked without any rejection or normalization of outputs.
    complete_mass(records)
    return records


def _uniform_ab_bc(records: Experiment) -> bool:
    for row in records.values():
        ab: dict[tuple[int, int, int], F] = {}
        bc: dict[tuple[int, int, int], F] = {}
        for (a, b1, b2, c), q in row.items():
            ab[a, b1, b2] = ab.get((a, b1, b2), F(0)) + q
            bc[b1, b2, c] = bc.get((b1, b2, c), F(0)) + q
        if (
            len(ab) != 8
            or len(bc) != 8
            or set(ab.values()) | set(bc.values()) != {F(1, 8)}
        ):
            return False
    # AB is invariant under z and BC under x; this also gives the requisite
    # single-party marginals. Bob has no setting in this experiment.
    return True


def _bernoulli_kl_bits(p: F) -> float:
    return fsum(
        float(q) * log2(q / ref) for q, ref in ((p, NULL), (1 - p, 1 - NULL)) if q
    )


def _information_bits_uniform_prior(rows: list[AddressLaw]) -> float:
    return fsum(
        float(q) * log2(q * 256) for row in rows for q in row.values() if q
    ) / len(rows)


def _audit_sample(readers: PacketReaders, p: F) -> SampleReport:
    sampling = make_sampling(readers, p)
    records = make_records(readers, sampling)
    points = readers.strategies
    right: dict[Pair, dict[int, F]] = {}
    win_weight, loss_weight = p / 192, (1 - p) / 64
    for setting, row in sampling.items():
        right[setting] = {
            j: sum((row[i, j] for i in range(16)), F(0)) for j in range(16)
        }
        for (i, j), q in row.items():
            require(
                q == right[setting][j] / 16, "conditional source factorization fails"
            )
            if setting in ACTIVE:
                ratio = p / NULL if points[i, j].wins(setting) else (1 - p) / (1 - NULL)
                require(
                    q * 256 == ratio, "likelihood ratio does not attain KL equality"
                )
            else:
                require(q == F(1, 256), "inactive pair does not use the uniform prior")
    for point in points:
        for design in (ACTIVE, SETTINGS):
            require(
                sum(sampling[s][point] for s in design) / len(design) == F(1, 256),
                "raw address prior ceased to be uniform",
            )
    side_local = all(right[x, z] == right[0, z] for x, z in SETTINGS)
    require(side_local == (p == NULL), "unexpected remote setting dependence")
    right_z_independent = all(right[x, z] == right[x, 0] for x, z in SETTINGS)
    require(right_z_independent == (p == NULL), "unexpected right setting dependence")

    determinant = win_weight * (win_weight - loss_weight)
    checks = 0
    for index, (x0, x1) in enumerate(AXIS_PAIRS):
        z0, z1 = 2 * index, 2 * index + 1
        plaque = ((x0, z0), (x0, z1), (x1, z0), (x1, z1))
        for point, strategy in points.items():
            require(
                sum(strategy.wins(s) for s in plaque) == 3, "not three wins on plaque"
            )
            a, b, c, d = (sampling[s][point] for s in plaque)
            require(abs(a * d - b * c) == determinant, "wrong rank-one control")
            checks += 1

    win_mass = sum(
        q
        for setting in ACTIVE
        for point, q in sampling[setting].items()
        if points[point].wins(setting)
    ) / len(ACTIVE)
    require(win_mass == p, "wrong score-to-win translation")
    score = functional(records)
    require(score == 12 * (2 * p - 1), "network functional disagrees with wins")
    require(_uniform_ab_bc(records), "observable nonsignaling check failed")

    active_bits = _information_bits_uniform_prior([sampling[s] for s in ACTIVE])
    all_bits = _information_bits_uniform_prior(list(sampling.values()))
    require(
        isclose(active_bits, _bernoulli_kl_bits(p), rel_tol=1e-13, abs_tol=1e-15)
        and isclose(all_bits, active_bits * 2 / 3, rel_tol=1e-13, abs_tol=1e-15),
        "numeric information summary disagrees with exact likelihood certificate",
    )
    return SampleReport(
        str(p),
        str(score),
        len(records),
        complete_mass(records),
        True,
        True,
        True,
        True,
        side_local,
        checks,
        str(determinant),
        active_bits,
        all_bits,
    )


def run_probe() -> Report:
    readers = make_packet_readers()
    strategies = readers.strategies
    multiplicities = dict(Counter(Counter(strategies.values()).values()))
    wins_per_address = {
        sum(strategy.wins(s) for s in ACTIVE) for strategy in strategies.values()
    }
    winners_per_setting = {
        sum(strategy.wins(s) for strategy in strategies.values()) for s in ACTIVE
    }
    require(
        multiplicities == {8: 32}
        and wins_per_address == {9}
        and winners_per_setting == {192},
        "unexpected raw-address strategy census",
    )
    for setting in SETTINGS:
        counts = Counter(s.outcome(setting) for s in strategies.values())
        require(set(counts) == set(OUTCOMES), "missing observed outcome on raw carrier")
        for outcome, count in counts.items():
            a, b1, b2, c = outcome
            x, _ = setting
            wins = ACTIVE.get(setting, 0) * a * bob_axis_signs((b1, b2))[x] * c == 1
            expected = (24 if wins else 8) if setting in ACTIVE else 16
            require(
                count == expected, "unexpected raw-address multiplicity per outcome"
            )
    ceiling = max(pointwise_histogram())
    require(ceiling == 6, "settings-independent deterministic ceiling changed")
    return Report(
        len(strategies),
        multiplicities,
        len(ACTIVE),
        tuple(sorted(wins_per_address)),
        tuple(sorted(winners_per_setting)),
        (24, 8),
        16,
        ceiling,
        readers.instruments,
        tuple(_audit_sample(readers, p) for p in (NULL, F(7, 8), F(1))),
        "Conditional finite construction. Complete forward H/D contacts and fixed readers "
        "do not imply setting-independence. The supplied sampler depends on both settings "
        "at positive information cost, not on the observed outcomes. It is not side-local "
        "despite conditionally independent sources and nonsignaling observed marginals. "
        "No observed leakage, side-local cost optimum, or quantum reconstruction is claimed.",
    )


def main() -> None:
    print(json.dumps(asdict(run_probe()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
