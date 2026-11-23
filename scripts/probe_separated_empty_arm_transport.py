"""Finite comparison of two frozen two-arm circuits with inserted corridor cells.

The first leg (h) ends at the local plates and shutters; the second (g) ends
at the same analyzer as the zero-hop circuit. A hop introduces fresh raw
cells, not a virtual relabeling of an existing arm. Settings are local words
and neither a meter nor the matched-pair classifier controls the schedule.
This is a scheduled simulator test, not a physical or quantum derivation.
"""

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

from scripts import probe_colorless_packet_arms as four
from scripts import probe_eight_label_interferometer as eight

State = tuple[int, ...]
Pair = tuple[int, int]
Arms = tuple[tuple[int, ...], tuple[int, ...]]
Word = tuple[tuple[Pair, ...], ...]
Switches = tuple[bool, bool]
Number = Callable[[int], int]

OPEN = (True, True)
HOPS = range(3)
MICROSEEDS = tuple(product((0, 1), repeat=4))
IDLE_STOCK = (0, 1, 2, 3)


def four_number(label: int) -> int:
    return int(label == four.TOKEN)


@dataclass(frozen=True)
class Stage:
    name: str
    arms: Arms
    word: Word


@dataclass(frozen=True)
class Trial:
    stages: tuple[Stage, ...]
    trace: tuple[State, ...]
    dump_sites: Pair
    number: Number
    reverse_detector_ports: bool = False

    @property
    def initial(self) -> State:
        return self.trace[0]

    def position_at(self, name: str) -> int:
        position = 0
        for stage in self.stages:
            position += sum(map(len, stage.word))
            if stage.name == name:
                return position
        raise ValueError(f"unknown stage: {name}")

    def state_at(self, name: str) -> State:
        return self.trace[self.position_at(name)]

    def arms_at(self, name: str) -> Arms:
        stage = next(stage for stage in self.stages if stage.name == name)
        state = self.state_at(name)
        left, right = stage.arms
        return tuple(state[i] for i in left), tuple(state[i] for i in right)

    @property
    def occupied_pre_plate(self) -> int:
        # Audit-only observation, never consulted while compiling or replaying.
        arm_numbers = tuple(sum(map(self.number, arm)) for arm in self.arms_at("before_plates"))
        eight.check(sum(arm_numbers) == 1, "token not in either arm before the plates")
        return arm_numbers.index(1)

    @property
    def outcome(self) -> eight.Triple:
        # Both frozen readers examine only raw occupation at their D/target sites.
        left, right = self.stages[-1].arms
        final = self.trace[-1]
        detectors = (self.number(final[left[0]]), self.number(final[right[0]]))
        if self.reverse_detector_ports:
            detectors = detectors[::-1]
        return *detectors, sum(self.number(final[i]) for i in self.dump_sites)


def _allocate(stock: list[int], labels: Sequence[int]) -> tuple[int, ...]:
    start = len(stock)
    stock.extend(labels)
    return tuple(range(start, len(stock)))


def _four_arms(core: tuple[int, ...]) -> Arms:
    return ((core[four.DETECTOR[0]], core[four.EDGE[0]]),
            (core[four.DETECTOR[1]], core[four.EDGE[1]]))


def _move_word(word: Word, sites: tuple[int, ...]) -> Word:
    return tuple(tuple((sites[a], sites[b]) for a, b in layer) for layer in word)


def _four_leg(stock: list[int], before: tuple[int, ...], hops: int) -> tuple[tuple[int, ...], Word]:
    if not hops:
        return before, ()
    lanes = _four_arms(before)
    layers = []
    for _ in range(hops):
        fresh = (_allocate(stock, (1, 1)), _allocate(stock, (1, 1)))
        layers.append(tuple(zip(lanes[0] + lanes[1], fresh[0] + fresh[1], strict=True)))
        lanes = fresh
    left_zero, right_zero = _allocate(stock, (0, 0))
    layers.append(((left_zero, lanes[0][1]), (right_zero, lanes[1][1])))
    # Keep the frozen D/E/Z layouts. Dump and mask remain at the shutter site;
    # their numbers are carried in the index map, not forwarded as lanes.
    return (*lanes[0], left_zero, *lanes[1], right_zero, *before[6:]), tuple(layers)


def run_four(source: int, source_seed: Pair, mask_seed: Pair, plates: Switches,
             opened: Switches, h: int, g: int) -> Trial:
    eight.check(h in HOPS and g in HOPS, "unsupported study geometry")
    stock = list(four.initial_state(source, source_seed, mask_seed))
    split = tuple(range(len(stock)))
    switch, first_leg = _four_leg(stock, split, h)
    detector, second_leg = _four_leg(stock, switch, g)
    stages = (
        Stage("split", _four_arms(split), four.SPLITTER),
        Stage("before_plates", _four_arms(switch), first_leg),
        Stage("plates", _four_arms(switch), _move_word(four.plate_word(plates), switch)),
        Stage("shutters", _four_arms(switch), _move_word(four.shutter_word(opened), switch)),
        Stage("before_analyzer", _four_arms(detector), second_leg),
        Stage("analyzer", _four_arms(detector), _move_word(four.ANALYZER, detector)),
    )
    trace = four.replay(tuple(stock), tuple(layer for stage in stages for layer in stage.word))
    return Trial(stages, trace, four.DUMP, four_number)


def _eight_leg(stock: list[int], before: Arms, hops: int, idle_stock: tuple[int, ...]) -> tuple[Arms, Word]:
    layers = []
    for hop in range(hops):
        left, right = _allocate(stock, idle_stock[2 * hop:2 * hop + 2])
        edge = ((before[0][0], left), (before[1][0], right))
        layers.extend((edge, edge))  # T² is the exact raw SWAP, including all vacancy colors.
        before = ((left,), (right,))
    return before, tuple(layers)


def _eight_replay(initial: State, stages: tuple[Stage, ...]) -> tuple[State, ...]:
    cells = list(initial)
    trace = [initial]
    for stage in stages:
        for layer in stage.word:
            sites = tuple(i for pair in layer for i in pair)
            eight.check(len(sites) == len(set(sites)), f"overlapping layer at {stage.name}")
            for i, j in layer:
                cells[i], cells[j] = eight.coupler((cells[i], cells[j]))
                eight.check(eight.total_number(cells) == 1, f"occupation changed at {stage.name}")
                trace.append(tuple(cells))
    return tuple(trace)


def run_eight(source: int, particle_phase: int, vacuum_phase: int, dump_phases: Pair,
              plates: Switches, opened: Switches, h: int, g: int,
              *, idle_stock: tuple[int, ...] = IDLE_STOCK) -> Trial:
    eight.check(h in HOPS and g in HOPS, "unsupported study geometry")
    eight.check(tuple(sorted(idle_stock)) == IDLE_STOCK, "idle stock is not a vacancy permutation")
    stock = list(eight.source_pair(source, particle_phase, vacuum_phase))
    split = ((0,), (1,))
    switch, first_leg = _eight_leg(stock, split, h, idle_stock)
    refs_left = _allocate(stock, (eight.REFERENCE, eight.REFERENCE))
    refs_right = _allocate(stock, (eight.REFERENCE, eight.REFERENCE))
    dumps = _allocate(stock, dump_phases)
    detector, second_leg = _eight_leg(stock, switch, g, idle_stock)
    triples = tuple((refs[0], switch[i][0], refs[1])
                    for i, refs in enumerate((refs_left, refs_right)))
    plate_word = tuple(tuple((triples[i][a], triples[i][b]) for i in four.ARMS if plates[i])
                       for a, b in eight.PLATE_WORD) if any(plates) else ()
    shutter = tuple((switch[i][0], dumps[i]) for i in four.ARMS if not opened[i])
    stages = (
        Stage("split", split, (((0, 1),),)),
        Stage("before_plates", switch, first_leg),
        Stage("plates", switch, plate_word),
        Stage("shutters", switch, (shutter, shutter) if shutter else ()),
        Stage("before_analyzer", detector, second_leg),
        Stage("analyzer", detector, (((detector[0][0], detector[1][0]),),)),
    )
    return Trial(stages, _eight_replay(tuple(stock), stages), dumps, eight.number, True)


def verify_vacancy_invariant() -> int:
    """Check the local premise of the fixed-word vacancy-sector induction.

    On 0/1/2 inputs, the zero mask is fixed and each nonzero 1/2 register
    flips iff its partner is zero. For two runs with matching zero masks, a
    common prescribed vacancy-only word therefore applies the same bit flips
    at each site in both runs. Their pointwise difference support is fixed by
    induction. This does not cover a different word, adaptive scheduling or
    a contact of the varying region with a visiting token.
    """
    for a, b in product(range(3), repeat=2):
        expected = (3 - a if a and b == 0 else a, 3 - b if b and a == 0 else b)
        eight.check(four.four_label_contact((a, b)) == expected, "vacancy-only rule changed")
    return 9


@dataclass(frozen=True)
class ReturnBus:
    trace: tuple[State, ...]
    visit_sites: tuple[Pair, ...]
    visit_offsets: tuple[int, ...]

    @property
    def visited(self) -> tuple[bool, ...]:
        return tuple(four.TOKEN in tuple(self.trace[t][i] for i in sites)
                     for sites, t in zip(self.visit_sites, self.visit_offsets, strict=True))

    @property
    def destination(self) -> int:
        return self.trace[-1][:2].index(four.TOKEN)


def run_return_bus(source: int, settings: Switches, distances: Pair) -> ReturnBus:
    """Active-visit countercontrol, not a signal sent down an empty arm."""
    eight.check(source in four.ARMS and all(d in (1, 2) for d in distances), "bad bus stock")
    head = (0, 1)
    stock = [four.TOKEN if source == i else 1 for i in head]
    word: Word = ()
    visit_sites = []
    visit_offsets = []
    for enabled, distance in zip(settings, distances, strict=True):
        previous = head
        outward: Word = ()
        for _ in range(distance):
            fresh = _allocate(stock, (1, 1))
            outward += (tuple(zip(previous, fresh, strict=True)),)
            previous = fresh
        q, = _allocate(stock, (int(enabled),))
        d0, d1 = previous
        word += outward
        visit_sites.append(previous)
        visit_offsets.append(sum(map(len, word)))
        word += (((q, d0),), ((q, d1),), ((q, d0),)) + outward[::-1]
    return ReturnBus(four.replay(tuple(stock), word), tuple(visit_sites), tuple(visit_offsets))


@dataclass(frozen=True)
class GeometryEvidence:
    h: int
    g: int
    four_triggers: int
    eight_triggers: int
    matched_flips: int
    four_click_changes: int
    eight_click_changes: int


def _expect_rows(four_row: list[Trial], eight_row: list[Trial],
                 source: int, plates: Switches, opened: Switches, h: int, g: int) -> None:
    parity = four.routed(source ^ plates[0] ^ plates[1], F(1))
    if all(opened):
        four_expected = (F(1, 2), F(1, 2), F(0)) if h or g else parity
        eight_expected = parity
    else:
        four_expected = eight_expected = ((F(1, 4), F(1, 4), F(1, 2)) if any(opened)
                                          else (F(0), F(0), F(1)))
    for row, expected in ((four_row, four_expected), (eight_row, eight_expected)):
        eight.check(len(row) == len(MICROSEEDS), "row does not include all fair stocks")
        for t in row:
            eight.check(sum(t.outcome) == 1 and t.outcome[2] == int(not opened[t.occupied_pre_plate]),
                        "incorrect raw detector/dump accounting")
            shutter_pos = t.position_at("shutters")
            shuttered = t.trace[shutter_pos]
            eight.check(all(state[i] == shuttered[i]
                            for state in t.trace[shutter_pos:] for i in t.dump_sites),
                        "dump is not sealed after the shutter")
        eight.check(four.frequencies(tuple(t.outcome for t in row)) == expected,
                    f"unexpected L/R/loss rates: {source, plates, opened, h, g}")


def _flipped_vacant_plate(trial: Trial, plates: Switches) -> Switches:
    vacant = 1 - trial.occupied_pre_plate
    return plates[0] ^ (vacant == 0), plates[1] ^ (vacant == 1)


def _check_pair(a: Trial, b: Trial, *, check_retired_edge: bool) -> int:
    eight.check(a.initial == b.initial, "matched intervention changed raw stock")
    eight.check(a.state_at("before_plates") == b.state_at("before_plates"),
                "matched intervention changed pre-plate history")
    eight.check(a.stages[:2] + a.stages[3:] == b.stages[:2] + b.stages[3:],
                "matched intervention changed contacts outside the local writer")
    if check_retired_edge:
        vacant = 1 - a.occupied_pre_plate
        plate_stage = a.stages[2]
        local_edge = plate_stage.arms[vacant][1]
        suffix_a = a.trace[a.position_at("plates"):]
        suffix_b = b.trace[b.position_at("plates"):]
        for ra, rb in zip(suffix_a, suffix_b, strict=True):
            different = tuple(i for i, (x, y) in enumerate(zip(ra, rb, strict=True)) if x != y)
            eight.check(different == (local_edge,) and {ra[local_edge], rb[local_edge]} == {1, 2},
                        "vacant record did not remain on the retired writer edge")
        eight.check(a.arms_at("before_analyzer") == b.arms_at("before_analyzer"),
                    "downstream analyzer received a vacant setting difference")
    return int(a.outcome != b.outcome)


def _verify_geometry(h: int, g: int) -> GeometryEvidence:
    open_four = {}
    open_eight = {}
    four_count = eight_count = 0
    for source, plates, opened in product(four.ARMS, four.SWITCHES, four.SWITCHES):
        four_row, eight_row = [], []
        for seed in MICROSEEDS:
            p, v, left, right = seed
            a = run_four(source, (1 + p, 1 + v), (2 * left, 2 * right), plates, opened, h, g)
            b = run_eight(source, p, v, (left, right), plates, opened, h, g)
            frozen = eight.trial(source, p, v, (left, right), plates, opened)
            eight.check(b.outcome == four.swap_ports(frozen), "eight-label seed changed its outcome")
            four_row.append(a)
            eight_row.append(b)
            if opened == OPEN:
                open_four[source, plates, seed] = a
                open_eight[source, plates, seed] = b
        _expect_rows(four_row, eight_row, source, plates, opened, h, g)
        four_count += len(four_row)
        eight_count += len(eight_row)
    eight.check(four_count == eight_count == 512, "wrong launch count per model")

    # Both directions of each matched pair are counted: 2 inputs x 4 plate
    # masks x 16 seeds. Read each model's own pre-plate path only now, offline;
    # this is an outcome comparison between two already completed circuits.
    changes = []
    for cases, check_retired in ((open_four, g > 0), (open_eight, False)):
        eight.check(len(cases) == 128, "wrong oriented matched-pair case count")
        changes.append(sum(_check_pair(a, cases[source, _flipped_vacant_plate(a, plates), seed],
                                       check_retired_edge=check_retired)
                           for (source, plates, seed), a in cases.items()))
    four_changes, eight_changes = changes
    eight.check(four_changes == (128 if not g else 0), "four-label matched behavior changed")
    eight.check(eight_changes == 128, "eight-label matched behavior changed")
    return GeometryEvidence(h, g, four_count, eight_count, len(open_four), four_changes, eight_changes)


def verify() -> tuple[GeometryEvidence, ...]:
    verify_vacancy_invariant()
    eight.verify_raw_coupler()  # All raw pairs, hence any vacant idle stock on each edge.
    for source, settings, distances in product(four.ARMS, four.SWITCHES, product((1, 2), repeat=2)):
        bus = run_return_bus(source, settings, distances)
        eight.check(bus.visited == (True, True) and bus.destination == source ^ settings[0] ^ settings[1],
                    "active-visit countercontrol failed")
    return tuple(_verify_geometry(h, g) for h, g in product(HOPS, repeat=2))


def main() -> None:
    print("h upstream, g downstream: matched empty-plate flips changing the click (four / eight)")
    for r in verify():
        print(f"h={r.h}, g={r.g}: {r.four_click_changes}/{r.matched_flips} / "
              f"{r.eight_click_changes}/{r.matched_flips}; "
              f"{r.four_triggers} and {r.eight_triggers} L/R/loss trials")
    print("Single-open rows: (1/4, 1/4, 1/2); closed rows: all lost.")
    print("Open/open: eight-label XOR throughout; four-label XOR only at (0,0), otherwise halves.")
    print("In matched four-label pairs with g>0 the difference remains in retired local stock.")
    print("The fixed-word vacancy-only obstruction excludes neither adaptive schedules nor the active return-bus control.")


if __name__ == "__main__":
    main()
