"""Transfer two frozen packet instruments to scheduled one-relation offers.

Each cell supplies a relabeling of the same 15 micro-offers. The diagonal is
the occupancy and off-diagonal bonds are scratch. Overlapping cells are scanned
serially, not offered in parallel. The scan, rails and preparations are inputs.

Run: python3 -B -E -O -m scripts.probe_pair_compiled_packet_instruments
"""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import asdict, dataclass
from itertools import combinations, pairwise, product

from scripts.probe_native_phase_coincidence import (
    COLORS,
    SWAP,
    ContactLayout,
    colored_maps,
    contact_layout,
    edge_labels,
    equalizer_classes,
    half_filled,
    inverse,
    product_orbits,
)
from scripts.probe_octagon_three_contexts import (
    PAIRS,
    Maps,
    action,
    affine,
    require,
    two_rings,
)
from scripts.probe_single_relation_quartet import (
    NO_DEGREE_CODE,
    NO_DEGREE_WORD,
    PARITY_WORD,
    Pair,
    Relation,
    State,
    Word,
)


@dataclass(frozen=True)
class LocalAudit:
    clean_patterns: int
    parity_activity_by_occupancy: dict[int, int]
    parity_all_equal_internal_offers: tuple[int, int]
    code7_same_word_all_equal_internal_offers: tuple[int, int]
    code7_same_word_all_equal_bonds: tuple[int, int]
    code7_clean_word_all_equal_internal_offers: tuple[int, int]
    code7_clean_word_all_equal_bonds: tuple[int, int]
    embedded_clean_patterns: int
    dirty_cross_bond_blocks_clean_lift: bool


@dataclass(frozen=True)
class OctagonAudit:
    addresses: int
    rails: int
    cells_per_color: int
    direct_sweeps: int
    direct_offers: int
    common_central_z: bool
    central_w: bool
    w: tuple[int, ...]
    w_squared: tuple[int, ...]
    z: tuple[int, ...]
    signed_w_images: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class OrderAudit:
    lifted_sweeps: int
    lifted_cell_visits: int
    lifted_offers: int
    effective_cells: int
    effective_offers: int
    partial_visits: dict[int, int]
    direct_sweeps: int
    direct_offers: int


@dataclass(frozen=True)
class ModeAudit:
    input_rails: int
    class_rails: int
    residue_rails: int
    cells: int
    inputs: int
    outputs: int
    unique_forward: int
    unique_reverse: int
    orders: dict[str, OrderAudit]


@dataclass(frozen=True)
class Report:
    local: LocalAudit
    octagon: OctagonAudit
    modes: dict[str, ModeAudit]
    scope: str


@dataclass(frozen=True)
class LocalTrace:
    states: tuple[State, ...]
    effective_offers: int
    occupancy: int


def local_traces() -> tuple[LocalTrace, ...]:
    relation = Relation(4)
    steps = tuple(relation.compile_word((pair,)) for pair in PARITY_WORD)
    traces = []
    for sites in range(16):
        states = [State(sites, 0)]
        for step in steps:
            states.append(step(states[-1]))
        effective = sum(a != b for a, b in pairwise(states))
        occupancy = sites.bit_count()
        require(states[-1] == State(sites ^ 15 if occupancy == 2 else sites, 0),
                "local trajectory does not realize the clean quartet map")
        traces.append(LocalTrace(tuple(states), effective, occupancy))
    return tuple(traces)


def _image(index: int, bits: tuple[int, ...]) -> int:
    return sum(bit for k, bit in enumerate(bits) if index & (1 << k))


def _sites(mask: int, size: int) -> tuple[int, ...]:
    return tuple(i for i in range(size) if mask & (1 << i))


@dataclass(frozen=True)
class Cell:
    mask: int
    word: Word
    site_images: tuple[int, ...]
    bond_images: dict[int, int]


@dataclass(frozen=True)
class SweepResult:
    end: State
    effective_cells: tuple[int, ...]
    effective_offers: int
    partial_one: int
    partial_three: int
    direct_offers: int


class Scan:
    """An exact clean-boundary lift, with an independent global offer replay.

    On entry to each cell there are no bonds anywhere. Its offers can create
    only internal bonds, so outside incidences in the degree-parity guard are
    zero, and exterior diagonals are untouched. The 16 local trajectories
    exhaust its possible diagonals and each ends bond-free. This allows the
    clean-boundary argument to apply again even for overlapping cells.
    """

    def __init__(self, size: int, masks: tuple[int, ...], traces: tuple[LocalTrace, ...]):
        self.traces = traces
        layouts = tuple(_sites(mask, size) for mask in masks)
        require(all(len(rails) == 4 and _image(15, tuple(1 << i for i in rails)) == mask
                    for mask, rails in zip(masks, layouts, strict=True)), "invalid cell mask")
        words = tuple(tuple((rails[i], rails[j]) for i, j in PARITY_WORD) for rails in layouts)
        pairs = {pair for word in words for pair in word}
        relation = Relation(size, pairs)
        self.steps: dict[Pair, Callable[[State], State]] = {
            pair: relation.compile_word((pair,)) for pair in pairs
        }
        used_bonds = {state.bonds for row in traces for state in row.states}
        cells = []
        for mask, rails, word in zip(masks, layouts, words, strict=True):
            rail_bits = tuple(1 << i for i in rails)
            bond_bits = tuple(relation.state(0, ((i, j),)).bonds
                              for i, j in combinations(rails, 2))
            cells.append(Cell(mask, word, tuple(_image(i, rail_bits) for i in range(16)),
                              {b: _image(b, bond_bits) for b in used_bonds}))
        self.cells = tuple(cells)

    def _compare_trace(self, actual: State, cell: Cell, trace: LocalTrace) -> State:
        outside = actual.sites & ~cell.mask
        for pair, local in zip(cell.word, trace.states[1:], strict=True):
            actual = self.steps[pair](actual)
            expected = State(outside | cell.site_images[local.sites], cell.bond_images[local.bonds])
            require(actual == expected, "global and lifted micro-offers disagree")
        return actual

    def run(self, source: int, order: tuple[int, ...], *, direct: bool = False) -> SweepResult:
        sites = source
        actual = State(source, 0)
        effective_cells = []
        effective_offers = partial_one = partial_three = direct_offers = 0
        for index in order:
            cell = self.cells[index]
            pattern = cell.site_images.index(sites & cell.mask)
            trace = self.traces[pattern]
            terminal = trace.states[-1].sites
            if terminal != pattern:
                effective_cells.append(index)
                sites ^= cell.site_images[pattern ^ terminal]
            effective_offers += trace.effective_offers
            partial_one += trace.occupancy == 1
            partial_three += trace.occupancy == 3
            if direct:
                actual = self._compare_trace(actual, cell, trace)
                require(actual == State(sites, 0), "direct global cell did not clean")
                direct_offers += len(cell.word)
        return SweepResult(State(sites, 0), tuple(effective_cells), effective_offers,
                           partial_one, partial_three, direct_offers)


def audit_local(traces: tuple[LocalTrace, ...]) -> LocalAudit:
    relation = Relation(4)
    count_sets = [{row.effective_offers for row in traces if row.occupancy == n} for n in range(5)]
    require(count_sets == [{0}, {4}, {8}, {4}, {0}], "unexpected offer activity by occupancy")
    zero, full = State(0, 0), State(15, 0)
    short_zero, short_n0 = relation.replay(zero, PARITY_WORD, NO_DEGREE_CODE)
    short_full, short_n1 = relation.replay(full, PARITY_WORD, NO_DEGREE_CODE)
    long_zero, long_n0 = relation.replay(zero, NO_DEGREE_WORD, NO_DEGREE_CODE)
    long_full, long_n1 = relation.replay(full, NO_DEGREE_WORD, NO_DEGREE_CODE)
    require((short_n0, short_n1) == (15, 15) and short_zero.bonds == short_full.bonds != 0,
            "code 7 did not distinguish all-equal scratch activity under the same schedule")
    require((long_n0, long_n1) == (144, 144) and (long_zero, long_full) == (zero, full),
            "code 7 longer-word control did not clean its all-equal input")

    # All local patterns (including weights 1 and 3) inside a larger relation,
    # with untouched occupied spectators on both sides and between cell rails.
    mask = 0b1011010
    outer = 0b0100101
    scan = Scan(7, (mask,), traces)
    sites = scan.cells[0].site_images
    for pattern, trace in enumerate(traces):
        result = scan.run(outer | sites[pattern], (0,), direct=True)
        require(result.end == State(outer | sites[trace.states[-1].sites], 0),
                "embedded pattern did not preserve the spectators and clean its bonds")

    # A single pre-existing crossing bond can defeat the clean lift because
    # global parity sees it; writing only the internal sweep does not remove it.
    global_relation = Relation(5)
    dirty_input = global_relation.state(3, ((0, 4),))
    dirty_end = global_relation.compile_word(PARITY_WORD)(dirty_input)
    dirty_control = (dirty_end.bonds & dirty_input.bonds == dirty_input.bonds
                     and bool(dirty_end.bonds ^ dirty_input.bonds))
    require(dirty_control, "crossing-bond control did not distinguish the clean boundary")
    return LocalAudit(len(traces), {n: next(iter(count)) for n, count in enumerate(count_sets)},
                      (traces[0].effective_offers, traces[15].effective_offers),
                      (short_n0, short_n1), (short_zero.bonds, short_full.bonds),
                      (long_n0, long_n1), (long_zero.bonds, long_full.bonds),
                      len(sites), dirty_control)


def audit_octagon(maps: Maps, traces: tuple[LocalTrace, ...]) -> OctagonAudit:
    n = len(maps["A"])
    require(n == 16, "wrong frozen octagon size")
    rails = 2 * n
    packets = tuple(3 << (2*i) for i in range(n))
    raw: dict[str, dict[int, int]] = {}
    direct_sweeps = direct_offers = 0
    for color, matching in maps.items():
        masks = tuple(packets[i] | packets[j] for i, j in enumerate(matching) if i < j)
        require(len(masks) == 8, "wrong frozen color cell count")
        scan = Scan(rails, masks, traces)
        order = tuple(range(len(masks)))
        table = {}
        for source, target_address in zip(packets, matching, strict=True):
            (expected_mask,) = half_filled(source, masks)
            expected = source ^ expected_mask
            result = scan.run(source, order, direct=True)
            require(result.end == State(expected, 0) and expected == packets[target_address]
                    and result.effective_cells == (masks.index(expected_mask),),
                    "color sweep did not move the packet to its paired address exactly once")
            table[source] = result.end.sites
            direct_sweeps += 1
            direct_offers += result.direct_offers
        raw[color] = table

    def follow(word: str) -> tuple[int, ...]:
        current = packets
        for color in word:
            current = tuple(raw[color][p] for p in current)
        return current

    z, w, w2 = (follow(word) for word in ("ABAB", "ABC", "ABCABC"))
    require(w2 == z and w == tuple(packets[i] for i in action(maps, "ABC")),
            "compiled W differs from the upper fixture or W squared differs from Z")
    common_z = all(follow(pair * 2) == z for pair in PAIRS)
    central_z = all(follow(color + "ABAB") == follow("ABAB" + color) for color in COLORS)
    central_w = all(follow(color + "ABC") == follow("ABC" + color) for color in COLORS)
    require(common_z and central_z and central_w and follow("ABABABAB") == packets
            and all(p != q for p, q in zip(packets, z, strict=True)),
            "common central square or its free involution failed")

    raw_z = dict(zip(packets, z, strict=True))
    raw_w = dict(zip(packets, w, strict=True))
    supports = tuple((p, q) for p, q in raw_z.items() if p < q)
    images = []
    for p, q in supports:
        p1, q1 = raw_w[p], raw_w[q]
        oriented = (min(p1, q1), max(p1, q1))
        images.append((supports.index(oriented), 1 if p1 < q1 else -1))
    require(len(images) == 8 and all(images[mid] == (k, -sign)
                                    for k, (mid, sign) in enumerate(images)),
            "real signed contrast square is not negative identity")
    return OctagonAudit(n, rails, 8, direct_sweeps, direct_offers, common_z and central_z,
                        central_w, w, w2, z, tuple(images))


def audit_mode(n: int, layout: ContactLayout, traces: tuple[LocalTrace, ...]) -> ModeAudit:
    masks = layout.contacts
    size = 2*n + layout.class_rails + layout.residue_rails
    require((len(masks), layout.class_rails, layout.residue_rails) == (256, 64, 8),
            "wrong class-plus-C-residue fixture")
    scan = Scan(size, masks, traces)
    outputs = tuple(source ^ mask for source, mask in zip(layout.inputs, masks, strict=True))
    require(len(set(outputs)) == len(set(layout.inputs)) == 256, "duplicated endpoint footprints")
    unique_forward = unique_reverse = 0
    for source, output, mask in zip(layout.inputs, outputs, masks, strict=True):
        unique_forward += half_filled(source, masks) == (mask,)
        unique_reverse += half_filled(output, masks) == (mask,)
    require(unique_forward == unique_reverse == len(masks),
            "upper raw masks do not supply a unique forward and inverse cell for every pair")

    supplied = tuple(range(len(masks)))
    corners = {0, n - 1, n * (n - 1), n * n - 1}
    orders = {}
    for name, order in (("supplied", supplied), ("reversed", supplied[::-1])):
        effective_cells = effective_offers = partial_one = partial_three = 0
        direct_sweeps = direct_offers = 0
        for index, (source, expected) in enumerate(zip(layout.inputs, outputs, strict=True)):
            direct = index in corners
            first = scan.run(source, order, direct=direct)
            require(first.end == State(expected, 0) and first.effective_cells == (index,),
                    "full forward scan did not produce exactly its upper coincidence")
            second = scan.run(first.end.sites, order, direct=direct)
            require(second.end == State(source, 0) and second.effective_cells == (index,),
                    "next full scan did not recover the input with only its inverse cell")
            for result in (first, second):
                effective_cells += len(result.effective_cells)
                effective_offers += result.effective_offers
                partial_one += result.partial_one
                partial_three += result.partial_three
                direct_sweeps += direct
                direct_offers += result.direct_offers
        sweeps = 2 * len(layout.inputs)
        visits = sweeps * len(order)
        orders[name] = OrderAudit(sweeps, visits, visits * len(PARITY_WORD), effective_cells,
                                  effective_offers, {1: partial_one, 3: partial_three},
                                  direct_sweeps, direct_offers)
    return ModeAudit(2*n, layout.class_rails, layout.residue_rails, len(masks), len(layout.inputs),
                     len(outputs), unique_forward, unique_reverse, orders)


def run_probe() -> Report:
    traces = local_traces()
    local = audit_local(traces)
    maps = two_rings(affine(5, 0))
    octagon = audit_octagon(maps, traces)
    w = action(maps, "ABC")
    n = len(w)
    pairs = tuple(product(range(n), range(n)))
    c_labels = edge_labels(maps["C"])
    residues = tuple(c_labels[i] for i, _ in pairs)
    modes = {}
    for name, images, right in (("D", COLORS, w), ("H", SWAP, inverse(w))):
        classes, labels = equalizer_classes(w, colored_maps(maps, images), pairs)
        require(classes == product_orbits(w, right, pairs) and len(classes) == 64,
                "supplied class layout does not match the upper product orbits")
        modes[name] = audit_mode(n, contact_layout(n, pairs, labels, residues), traces)
    return Report(local, octagon, modes,
                  "Finite transfer on clean boundaries with externally supplied, serial offer "
                  "schedules and separately fixed D/H layouts. Signed contrasts are real "
                  "differences of packet basis states, not phases. Positive coincidences are "
                  "finite occupancy transfers, not autonomous measurements, certified nulls, "
                  "internal time, or derived detector probabilities.")


def main() -> None:
    print(json.dumps(asdict(run_probe()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
