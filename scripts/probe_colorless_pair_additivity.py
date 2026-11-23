"""Finite passive raw-count comparison for the fixed colorless-packet splitter.

The count reference is a fixed passive/free one-body transform U with matched
input and output modes, independent input occupations, unchanged background,
and an additive number readout P. For the pair the input one-body density is
the sum of the two single-input densities, so tr(P U rho U*) predicts the sum
of the two single-run means. Exchange can change joint coincidences without
changing this first-moment constraint. This fixture does not constrain
interacting devices or arbitrary measurements and is not a derivation of QM.
"""

from collections import Counter
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cache
from itertools import combinations

from scripts import probe_colorless_packet_arms as base

State = base.State
Preparations = tuple[frozenset[State], frozenset[State], frozenset[State]]
MaskTriple = tuple[int, int, int]
OfferWord = tuple[int, ...]

SITES = (base.DETECTOR[0], base.EDGE[0], base.DETECTOR[1], base.EDGE[1])
EDGES = (*base.A, *base.Z, *base.C)
OFFER_NAMES = ("A_L", "A_R", "Z_L", "Z_R", "C")
MIRROR = (1, 0, 3, 2, 4)
EARLY_WORD = (2, 4)
MAXIMAL_WORD = (2, 4, 1, 3, 1, 4)
PAIR_SITES = tuple(combinations(SITES, 2))
FLAT = (1, 1, 1, 1)
FERMION_COLUMNS = ((F(1, 2),) * 4, (F(1, 2), F(1, 2), F(-1, 2), F(-1, 2)))


@cache
def _split_stock() -> Preparations:
    left, right, pair = set(), set(), set()
    for seed in base.SOURCE_SEEDS:
        raw_l, raw_r = (base.initial_state(arm, seed, (0, 0))[:6] for arm in base.ARMS)
        left.add(base.replay(raw_l, base.SPLITTER)[-1])
        right.add(base.replay(raw_r, base.SPLITTER)[-1])
        pair.add(base.replay(raw_l[:3] + raw_r[3:], base.SPLITTER)[-1])
    return frozenset(left), frozenset(right), frozenset(pair)


def _move(state: State, offer: int) -> State:
    return base.replay(state, ((EDGES[offer],),))[-1]


def read_suffix(word: OfferWord) -> Preparations:
    """Apply one fixed chronological word to every seed in each preparation."""
    for offer in word:
        if type(offer) is not int or not 0 <= offer < len(EDGES):
            raise ValueError(f"unknown offer: {offer!r}")
    layers = tuple((EDGES[offer],) for offer in word)
    left, right, pair = (frozenset(base.replay(s, layers)[-1] for s in stock)
                         for stock in _split_stock())
    return left, right, pair


def _left_number(state: State) -> int:
    return sum(state[i] == base.TOKEN for i in SITES[:2])


def _site_counts(stock: Sequence[State] | frozenset[State]) -> tuple[int, ...]:
    return tuple(sum(s[i] == base.TOKEN for s in stock) for i in SITES)


@dataclass(frozen=True)
class Readout:
    site_counts: tuple[tuple[int, ...], ...]
    double_pairs: tuple[int, ...]

    @property
    def calibrated(self) -> bool:
        return self.site_counts[:2] == (FLAT, FLAT)

    @property
    def arm_means(self) -> tuple[tuple[F, F], ...]:
        return tuple((F(sum(row[:2]), 4), F(sum(row[2:]), 4)) for row in self.site_counts)

    @property
    def additivity_gap(self) -> tuple[F, F]:
        u, v, pair = self.arm_means
        return pair[0] - u[0] - v[0], pair[1] - u[1] - v[1]


def readout(stocks: Preparations) -> Readout:
    for stock, number in zip(stocks, (1, 1, 2), strict=True):
        if len(stock) != 4 or any(
            len(s) != 6 or s.count(base.TOKEN) != number or any(s[i] != 0 for i in base.ZERO)
            for s in stock
        ):
            raise AssertionError("expected every one of the four distinct, fixed-reference outcomes")
    pairs = tuple(sum(s[i] == s[j] == base.TOKEN for s in stocks[2]) for i, j in PAIR_SITES)
    return Readout(tuple(_site_counts(stock) for stock in stocks), pairs)


def fermion_menu() -> tuple[tuple[F, ...], ...]:
    """Squared single columns and squared two-column minors, in PAIR_SITES order."""
    u, v = FERMION_COLUMNS
    return (tuple(a * a for a in u), tuple(b * b for b in v),
            tuple((u[i] * v[j] - u[j] * v[i]) ** 2 for i, j in combinations(range(4), 2)))


def _close(initial: frozenset[State]) -> tuple[State, ...]:
    seen, stack = set(initial), list(initial)
    while stack:
        state = stack.pop()
        for offer in range(len(EDGES)):
            image = _move(state, offer)
            if image not in seen:
                seen.add(image)
                stack.append(image)
    return tuple(sorted(seen))


def _bit_indices(mask: int) -> Iterator[int]:
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


@dataclass(frozen=True)
class Depth:
    distinct_triples: int
    calibrated: int
    violating: int
    maximal: int


@dataclass(frozen=True)
class Certificate:
    double_orbit_by_left_count: tuple[int, int, int]
    left_mean_bound: F
    shortest_violation: int | None
    shortest_maximum: int | None
    depths: tuple[Depth, ...]


def certify() -> Certificate:
    """Full shortest-distance shells, deduplicating only identical triple masks."""
    stocks = _split_stock()
    states = _close(frozenset().union(*stocks))
    indices = {state: i for i, state in enumerate(states)}
    u_initial, v_initial, pair_initial = (sum(1 << indices[s] for s in stock) for stock in stocks)
    permutations = tuple(tuple(1 << indices[_move(s, offer)] for s in states)
                         for offer in range(len(EDGES)))
    if any(len(set(image)) != len(states) for image in permutations):
        raise AssertionError("an offer ceased to be reversible on the stock closure")

    # All four joint stocks are in the same orbit. Determinism and bijectivity
    # prevent loss, reweighting or coalescence of their four equiprobable states.
    pair_orbit = _close(frozenset({min(stocks[2])}))
    if not stocks[2].issubset(pair_orbit):
        raise AssertionError("joint post-splitter stocks left a common orbit")
    left_by_site = Counter(map(_left_number, pair_orbit))
    left_weights = sorted(map(_left_number, pair_orbit), reverse=True)
    left_mean_bound = F(sum(left_weights[:4]), 4)

    @cache
    def move_mask(mask: int, offer: int) -> int:
        return sum(permutations[offer][j] for j in _bit_indices(mask))

    @cache
    def counts(mask: int) -> tuple[int, ...]:
        return _site_counts(tuple(states[j] for j in _bit_indices(mask)))

    shell: set[MaskTriple] = {(u_initial, v_initial, pair_initial)}
    seen = set(shell)
    depths = []
    for depth in range(len(MAXIMAL_WORD) + 1):
        calibrated = violating = maximal = 0
        for u, v, pair in shell:
            if counts(u) != FLAT or counts(v) != FLAT:
                continue
            calibrated += 1
            left_count = F(sum(counts(pair)[:2]), 4)
            violating += left_count != 1
            maximal += left_count == left_mean_bound
        depths.append(Depth(len(shell), calibrated, violating, maximal))
        if depth < len(MAXIMAL_WORD):
            shell = {(move_mask(u, offer), move_mask(v, offer), move_mask(pair, offer))
                     for u, v, pair in shell for offer in range(len(EDGES))} - seen
            seen.update(shell)

    return Certificate((left_by_site[0], left_by_site[1], left_by_site[2]), left_mean_bound,
                       next((i for i, row in enumerate(depths) if row.violating), None),
                       next((i for i, row in enumerate(depths) if row.maximal), None), tuple(depths))


def report() -> str:
    certificate = certify()
    mirror = tuple(MIRROR[i] for i in EARLY_WORD)
    rows = (("splitter", ()), ("earliest witness", EARLY_WORD), ("arm mirror", mirror),
            ("reversed suffix", EARLY_WORD[::-1]), ("left maximum", MAXIMAL_WORD))
    lines = ["Frozen finite probe: four fair E-shade seeds per launch; no shutters; no postselection.",
             "Raw number at every contact: 1, 1, 2 by preparation; sites D_L,E_L,D_R,E_R.",
             "Single+single mean applies to a fixed passive/free one-body transform with matched modes,",
             "one particle in each distinct input mode, unchanged background and additive number readout.",
             "Splitter-only joint menu matches two orthogonal columns; not a Pauli test.",
             "First-moment comparison only: not interacting devices or arbitrary detectors, not a QM proof."]
    for label, word in rows:
        row = readout(read_suffix(word))
        offers = ",".join(OFFER_NAMES[i] for i in word) or "(none)"
        left, right = row.arm_means[-1]
        gap_l, gap_r = row.additivity_gap
        lines.append(f"{label}: {offers}; counts/4 left-input, right-input, pair={row.site_counts}; "
                     f"pair arm means=({left},{right}); gap=({gap_l},{gap_r}); calibrated={row.calibrated}")
        if not word:
            lines.append(f"  Pair occupancies in lexicographic site-pair order, counts/4={row.double_pairs}.")
    lines.extend((f"Double orbit by left raw count (0,1,2): {certificate.double_orbit_by_left_count}; "
                  f"left mean bound={certificate.left_mean_bound}.",
                  f"Shortest calibrated violation={certificate.shortest_violation}; "
                  f"shortest calibrated maximum={certificate.shortest_maximum}.",
                  "New triple masks by depth (all, calibrated, violating, maximal): "
                  + ", ".join(str((row.distinct_triples, row.calibrated, row.violating, row.maximal))
                              for row in certificate.depths)))
    return "\n".join(lines)


if __name__ == "__main__":
    print(report())
