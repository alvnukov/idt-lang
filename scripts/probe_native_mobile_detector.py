"""Native reversible shade records for the frozen mobile B switch.

Prepared (D,R,H,Z)=(x,1,1,0), for x in {1,2,3}, admit one fixed word:
D:R, R:H, R:Z, R:H, H:Z, R:H. Its output is (1,flag,x,0), with
ordinary shade flag 2 exactly for the token. Every update is the upstream
B contact. No token test selects a detector update. The occupation meter
is used only as a comparison after replay on the same physical launches.

Fresh record/holding stock, fixed-zero reference, contact order, and
isolation of the final holding and record relative to later traffic are
supplied. The bare contact graph neither jams nor provides a permanent
record with all contacts still available. This is a finite scheduled
readout, not irreversible absorption, a wall-time law, or a Born result.

Run: python3 -B -m scripts.probe_native_mobile_detector --json
"""

import argparse
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations, product
import json

from scripts import probe_mobile_blank_interferometer as mobile
from scripts.probe_eight_label_interferometer import check

DATA, RECORD, HOLDING, ZERO = range(4)
EDGES = ((DATA, RECORD), (RECORD, HOLDING), (RECORD, ZERO), (HOLDING, ZERO))
WORD = tuple((EDGES[i],) for i in (0, 1, 2, 1, 3, 1))
INITIAL = tuple((x, 1, 1, 0) for x in (1, 2, 3))
TARGET = ((1, 1, 1, 0), (1, 1, 2, 0), (1, 2, 3, 0))


def _step(state: mobile.State, edge: mobile.Pair) -> mobile.State:
    a, b = edge
    cells = list(state)
    cells[a], cells[b] = mobile.contact((cells[a], cells[b]))
    return tuple(cells)


def replay(initial: mobile.State, word: mobile.Word) -> mobile.Trace:
    return mobile._replay(initial, word)


def reverse(trace: mobile.Trace) -> mobile.Trace:
    return replay(trace.output, tuple(layer[::-1] for layer in trace.word[::-1]))


def detector_trace(data: int) -> mobile.Trace:
    """Replay the same word on any of the three supported incident labels."""
    if data not in (1, 2, 3):
        raise ValueError("detector needs a nonzero data label 1, 2, or 3")
    return replay((data, 1, 1, 0), WORD)


@dataclass(frozen=True)
class Search:
    word: mobile.Word
    layer_sizes: tuple[int, ...]


def shortest_word(edges: tuple[mobile.Pair, ...]) -> Search | None:
    """Breadth-first search on joint columns: one word must fit all three stocks."""
    frontier = {INITIAL: ()}
    seen = {INITIAL}
    sizes = []
    while frontier:
        sizes.append(len(frontier))
        if TARGET in frontier:
            return Search(frontier[TARGET], tuple(sizes))
        following = {}
        for columns, word in frontier.items():
            for edge in edges:
                successor = tuple(_step(column, edge) for column in columns)
                if successor not in seen:
                    seen.add(successor)
                    following[successor] = word + ((edge,),)
        frontier = following
    return None


@dataclass(frozen=True)
class Read:
    data: int
    record: int
    holding: int
    reference: int

    @property
    def word(self) -> mobile.Word:
        sites = (self.data, self.record, self.holding, self.reference)
        return tuple(tuple((sites[a], sites[b]) for a, b in layer) for layer in WORD)


def _add_read(stock: list[int], data: int) -> Read:
    record = len(stock)
    stock.extend((1, 1, 0))
    return Read(data, record, record + 1, record + 2)


@dataclass(frozen=True)
class Readout:
    trace: mobile.Trace
    reads: tuple[Read, ...]
    prefix_contacts: int

    def _flags(self, reads: tuple[Read, ...]) -> tuple[int, ...]:
        flags = tuple(self.trace.output[read.record] for read in reads)
        check(all(flag in (1, 2) for flag in flags), "readout left the ordinary-shade alphabet")
        return tuple(flag - 1 for flag in flags)

    @property
    def port_flags(self) -> tuple[int, ...]:
        return self._flags(self.reads[:2])

    @property
    def dump_flags(self) -> tuple[int, ...]:
        return self._flags(self.reads[2:])

    @property
    def outcome(self) -> mobile.Outcome:
        check(len(self.reads) == 6, "L/R/loss outcome requires both ports and all four dump cells")
        left, right = self.port_flags
        return left, right, sum(self.dump_flags)


def attach_detectors(trial: mobile.Trial, *, include_dumps: bool = True) -> Readout:
    """Append identical detector words on both physical ports and, optionally, dumps."""
    embedded = trial.embed()
    stock = list(embedded.trace.initial)
    # Sites depend only on physical interface locations, never on final labels.
    inputs = embedded.detectors + (sum(embedded.dumps, ()) if include_dumps else ())
    reads = tuple(_add_read(stock, data) for data in inputs)
    trace = replay(tuple(stock), embedded.trace.word + tuple(layer for r in reads for layer in r.word))
    return Readout(trace, reads, len(embedded.trace.states) - 1)


@dataclass(frozen=True)
class SerialReadout:
    trace: mobile.Trace
    reads: tuple[Read, ...]


def serial_detector(data: int, count: int) -> SerialReadout:
    """Directly identify each holding cell with the next detector's data site."""
    if data not in (1, 2, 3) or count < 0:
        raise ValueError("serial detector needs data label 1, 2, or 3 and nonnegative count")
    stock = [data]
    reads = []
    current = 0
    for _ in range(count):
        read = _add_read(stock, current)
        reads.append(read)
        current = read.holding
    trace = replay(tuple(stock), tuple(layer for read in reads for layer in read.word))
    return SerialReadout(trace, tuple(reads))


def _signed_contact(action: mobile.State, edge: mobile.Pair) -> mobile.State:
    """On ordinary shades each coordinate is a signed original coordinate."""
    a, b = edge
    coordinates = list(action)
    if action[a] and action[b]:
        coordinates[a], coordinates[b] = action[b], action[a]
    elif action[a] or action[b]:
        coordinates[a], coordinates[b] = -action[a], -action[b]
    return tuple(coordinates)


def _apply_signed(action: mobile.State, stock: mobile.State) -> mobile.State:
    return tuple(stock[i - 1] if i > 0 else 3 - stock[-i - 1] if i < 0 else 0 for i in action)


def _distance(left: mobile.State, right: mobile.State) -> int:
    return sum(a != b for a, b in zip(left, right, strict=True))


@dataclass(frozen=True)
class BlankControl:
    signed_permutations: int
    stock_pairs: int
    checked_images: int
    distance_changes: int


def blank_only_control(edges: tuple[mobile.Pair, ...]) -> BlankControl:
    """Check fixed zeros and exact signed-permutation closure with no token present.

    The same local swap/flip description applies to any number of fixed-zero
    and ordinary-shade sites. Composing these maps preserves the Hamming
    distance between stocks run with the same word. The census here checks
    all reachable signed maps on this detector's three ordinary sites.
    """
    stock = tuple((*shades, 0) for shades in product((1, 2), repeat=3))
    identity = (1, 2, 3, 0)
    for state, edge in product(stock, edges):
        check(_step(state, edge) == _apply_signed(_signed_contact(identity, edge), state),
              "a blank-only generator isn't the claimed signed permutation")
    actions = {identity}
    queue = deque([identity])
    while queue:
        action = queue.popleft()
        for edge in edges:
            next_action = _signed_contact(action, edge)
            if next_action not in actions:
                actions.add(next_action)
                queue.append(next_action)
    stock_pairs = tuple((a, b) for a, b in combinations(stock, 2) if _distance(a, b) == 1)
    changes = sum(_distance(_apply_signed(action, a), _apply_signed(action, b)) != 1
                  for action, (a, b) in product(actions, stock_pairs))
    return BlankControl(len(actions), len(stock_pairs), len(actions) * len(stock_pairs), changes)


@dataclass(frozen=True)
class DirtyStock:
    initial: mobile.State
    output: mobile.State


def dirty_stock_control() -> tuple[DirtyStock, ...]:
    """Uninterpreted raw outputs with a dirty ordinary-shade record or holding cell."""
    dirty = ((*stock, 0) for stock in product((1, 2, 3), (1, 2), (1, 2)) if stock[1:] != (1, 1))
    return tuple(DirtyStock(initial, replay(initial, WORD).output) for initial in dirty)


@dataclass(frozen=True)
class JamControl:
    states: int
    raw_jams: int
    nonjam_endpoints: int
    record_flips_when_offered: int
    isolated_record_checks: int
    equal_shade_memory_checks: int
    changing_edges_reversed: int


def jam_control() -> JamControl:
    """Each changing contact leaves its own inverse offered on the fixed graph."""
    states = tuple((*labels, 0) for labels in product((1, 2, 3), repeat=3) if labels.count(3) <= 1)
    changes = jams = 0
    for state in states:
        following = tuple(_step(state, edge) for edge in EDGES)
        jams += all(other == state for other in following)
        for other, edge in zip(following, EDGES, strict=True):
            if other != state:
                check(_step(other, edge) == state, "changing edge lost its inverse on the fixed graph")
                changes += 1
    moving = flips = isolated = 0
    for data in (1, 2, 3):
        state = detector_trace(data).output
        moving += any(_step(state, edge) != state for edge in EDGES)
        flips += _step(state, (RECORD, ZERO))[RECORD] == 3 - state[RECORD]
        # Only unrelated sites interact after sealing. No elapsed-time model.
        spectator = replay(state + (1, 2), (((4, 5),),) * 4)
        isolated += all(s[:4] == state for s in spectator.states)
    equal_memory = sum(all(s == (shade, shade) for s in
                           replay((shade, shade), (((0, 1),),) * 4).states) for shade in (1, 2))
    return JamControl(len(states), jams, moving, flips, isolated, equal_memory, changes)


@dataclass(frozen=True)
class Evidence:
    endpoint_launches: int
    setting_rows: int
    native_outcome_counts: mobile.Outcome
    port_meter_mismatches: int
    dump_meter_mismatches: int
    all_trace_inverses: int
    shortest_contact_lengths: tuple[int, int]
    shortest_layers: tuple[tuple[int, ...], tuple[int, ...]]
    serial_cases: int
    blank_only: BlankControl
    jam: JamControl
    dirty_stock_cases: int
    dirty_false_flags: int
    dirty_missed_flags: int


def verify() -> Evidence:
    searches = tuple(shortest_word(edges) for edges in (EDGES, EDGES + ((DATA, ZERO),)))
    check(all(result is not None and len(result.word) == 6 for result in searches),
          "the exact fixed-stock minimum contact length changed")
    for initial, expected in zip(INITIAL, TARGET, strict=True):
        trace = detector_trace(initial[DATA])
        check(trace.output == expected and reverse(trace).states == trace.states[::-1],
              "local detector truth table or inverse changed")

    counts: Counter[int] = Counter()
    outcomes = set()
    port_mismatches = dump_mismatches = inverses = launches = 0
    for setting, seeds, replacements in product(mobile.SETTINGS, mobile.SEEDS, mobile.SEEDS):
        trial = mobile.run_trial(*setting, seeds, replacements)
        output = attach_detectors(trial)
        boundary = output.trace.states[output.prefix_contacts]
        for read in output.reads:
            final = output.trace.output
            check((final[read.data], final[read.holding], final[read.reference])
                  == (1, boundary[read.data], 0), "a detector disturbed the transmitted raw label")
        external = trial.outcome
        port_mismatches += output.port_flags != external[:2]
        dump_mismatches += output.dump_flags != tuple(int(x == mobile.TOKEN)
                                                     for arm in trial.arms for x in arm.dump)
        check(output.outcome == external and sum(output.outcome) == 1,
              "native-record L/R/loss changed an unconditional endpoint")
        inverses += reverse(output.trace).states == output.trace.states[::-1]
        counts.update(i for i, flag in enumerate(output.outcome) if flag)
        outcomes.add(setting)
        launches += 1
    totals = (counts[0], counts[1], counts[2])
    check((launches, len(outcomes), totals, inverses, port_mismatches, dump_mismatches)
          == (512, 32, (128, 128, 256), 512, 0, 0), "endpoint comparison or inverse count changed")

    serial_cases = 0
    for (x, *_), expected in zip(INITIAL, TARGET, strict=True):
        for count in (0, 1, 2, 4, 8):
            witness = serial_detector(x, count)
            final = witness.trace.output
            check(all(final[read.record] == expected[RECORD] for read in witness.reads),
                  "serial detector flags changed")
            check(final[witness.reads[-1].holding if count else 0] == x
                  and final.count(mobile.TOKEN) == int(x == mobile.TOKEN)
                  and reverse(witness.trace).states == witness.trace.states[::-1],
                  "serial detector lost its carrier or inverse")
            serial_cases += 1

    blank = blank_only_control(EDGES)
    check(blank == blank_only_control(EDGES + ((DATA, ZERO),)) == BlankControl(48, 12, 576, 0),
          "fixed-zero blank-only distance invariant changed")
    jam = jam_control()
    check((jam.states, jam.raw_jams, jam.nonjam_endpoints, jam.record_flips_when_offered,
           jam.isolated_record_checks, jam.equal_shade_memory_checks) == (20, 0, 3, 3, 3, 2),
          "closed contact or isolated memory behavior changed")
    dirty = dirty_stock_control()
    false = sum(case.initial[DATA] != mobile.TOKEN and case.output[RECORD] == 2 for case in dirty)
    missed = sum(case.initial[DATA] == mobile.TOKEN and case.output[RECORD] != 2 for case in dirty)
    check((len(dirty), false, missed) == (9, 4, 2), "dirty-stock counterexamples changed")
    a, b = searches
    return Evidence(launches, len(outcomes), totals, port_mismatches, dump_mismatches, inverses,
                    (len(a.word), len(b.word)), (a.layer_sizes, b.layer_sizes), serial_cases, blank, jam,
                    len(dirty), false, missed)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="show the checked finite evidence as JSON")
    args = parser.parse_args()
    evidence = verify()
    if args.json:
        print(json.dumps({**asdict(evidence),
                          "scope": "finite reversible prepared shade readout; no absorption or Born claim",
                          "layout": ["data", "record", "holding", "zero"], "word": WORD}, indent=2))
    else:
        print(f"Matched all {evidence.endpoint_launches} prepared endpoints (L/R/loss "
              f"{evidence.native_outcome_counts}); minimum 6 native B contacts; reversible readout only.")


if __name__ == "__main__":
    main()
