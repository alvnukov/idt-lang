"""Finite two-arm readout using the unchanged four-label pair contact.

The sole occupied raw label is 3. Each arm encodes a bit in two cells
(D, E), with a local fixed-zero reference Z. Stock, chronological contact
schedule, independent fair shutter masks and the occupancy meter are supplied.
This is a finite classical circuit, not a derivation of phase, the Born rule,
or an experimental result.
"""

from collections import Counter
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

from scripts.probe_eight_label_interferometer import check, trial as eight_label_trial
from scripts.probe_packet_free_pair_record import four_label_contact

Pair = tuple[int, int]
Switches = tuple[bool, bool]
State = tuple[int, ...]
Layer = tuple[Pair, ...]
Word = tuple[Layer, ...]
Rates = tuple[F, F, F]
Outcome = tuple[int, int, int]
Setting = tuple[int, Switches, Switches]

ARMS = (0, 1)
SWITCHES = tuple(product((False, True), repeat=2))
SOURCE_SEEDS = tuple(product((1, 2), repeat=2))
MASK_SEEDS = tuple(product((0, 2), repeat=2))
TOKEN = 3
O = ((TOKEN, 2), (1, TOKEN))
V = ((1, 1), (1, 2))

# Raw layout: (D_L,E_L,Z_L,D_R,E_R,Z_R,dump_L,mask_L,dump_R,mask_R).
DETECTOR, EDGE, ZERO = (0, 3), (1, 4), (2, 5)
DUMP, MASK = (6, 8), (7, 9)
A = tuple(zip(DETECTOR, EDGE, strict=True))
Z = tuple(zip(ZERO, EDGE, strict=True))
C = ((EDGE[0], EDGE[1]),)
M = (C, A, Z, A, C)  # C P_both C; a palindrome of involutive layers.
SPLITTER = (A,) + M  # Chronological order: exact inverse of the analyzer.
ANALYZER = M + (A,)


def plate_word(plates: Switches) -> Word:
    local_a = tuple(A[i] for i in ARMS if plates[i])
    local_z = tuple(Z[i] for i in ARMS if plates[i])
    return (local_a, local_z, local_a) if local_a else ()


def shutter_word(opened: Switches) -> Word:
    closed = tuple(i for i in ARMS if not opened[i])
    if not closed:
        return ()
    return (
        tuple(A[i] for i in closed),
        tuple((DETECTOR[i], DUMP[i]) for i in closed),
        tuple((EDGE[i], MASK[i]) for i in closed),
    )


def schedule(plates: Switches, opened: Switches) -> Word:
    return SPLITTER + plate_word(plates) + shutter_word(opened) + ANALYZER


def max_degree(word: Word) -> int:
    edges = {tuple(sorted(pair)) for layer in word for pair in layer}
    return max(Counter(i for edge in edges for i in edge).values(), default=0)


def replay(before: State, word: Word,
           contact: Callable[[Pair], Pair] = four_label_contact) -> tuple[State, ...]:
    """Apply only the given word; audit raw number after every actual contact."""
    cells = list(before)
    raw_number = before.count(TOKEN)
    trace = [before]
    for layer in word:
        sites = tuple(site for pair in layer for site in pair)
        check(len(sites) == len(set(sites)), f"contact layer overlaps: {layer}")
        for i, j in layer:
            cells[i], cells[j] = contact((cells[i], cells[j]))
            state = tuple(cells)
            check(state.count(TOKEN) == raw_number, f"contact {(i, j)} changed raw number")
            trace.append(state)
    return tuple(trace)


def initial_state(source: int, source_seed: Pair, mask_seed: Pair) -> State:
    check(source in ARMS and source_seed in SOURCE_SEEDS and mask_seed in MASK_SEEDS,
          "stock outside the frozen launch support")
    return (TOKEN if source == 0 else 1, source_seed[0], 0,
            TOKEN if source == 1 else 1, source_seed[1], 0,
            1, mask_seed[0], 1, mask_seed[1])


def arm_pair(state: State, arm: int) -> Pair:
    return state[DETECTOR[arm]], state[EDGE[arm]]


def decode(state: State) -> tuple[int, int, int]:
    """Audit a one-token code state; this read is never a circuit input."""
    left, right = (arm_pair(state, i) for i in ARMS)
    if left in O and right in V:
        return 0, O.index(left), V.index(right)
    if right in O and left in V:
        return 1, V.index(left), O.index(right)
    raise AssertionError(f"not a one-token code state: {(left, right)}")


def meter(raw: State) -> Outcome:
    return (int(raw[DETECTOR[0]] == TOKEN), int(raw[DETECTOR[1]] == TOKEN),
            sum(raw[i] == TOKEN for i in DUMP))


@dataclass(frozen=True)
class Trial:
    source_seed: Pair
    mask_seed: Pair
    trace: tuple[State, ...]
    split: State
    plated: State
    shuttered: State

    @property
    def initial(self) -> State:
        return self.trace[0]

    @property
    def output(self) -> State:
        return self.trace[-1]

    @property
    def outcome(self) -> Outcome:
        return meter(self.output)


def run_trial(source: int, source_seed: Pair, mask_seed: Pair,
              plates: Switches, opened: Switches) -> Trial:
    # No code reads, meter reads or acceptance checks choose any contact.
    initial = initial_state(source, source_seed, mask_seed)
    plated_word, closed_word = plate_word(plates), shutter_word(opened)
    trace = replay(initial, SPLITTER + plated_word + closed_word + ANALYZER)
    split_at = sum(map(len, SPLITTER))
    plated_at = split_at + sum(map(len, plated_word))
    shuttered_at = plated_at + sum(map(len, closed_word))
    return Trial(source_seed, mask_seed, trace, trace[split_at], trace[plated_at], trace[shuttered_at])


def enumerate_rows() -> dict[Setting, tuple[Trial, ...]]:
    return {
        (source, plates, opened): tuple(
            run_trial(source, seeds, masks, plates, opened)
            for seeds, masks in product(SOURCE_SEEDS, MASK_SEEDS)
        )
        for source, plates, opened in product(ARMS, SWITCHES, SWITCHES)
    }


def frequencies(outcomes: Sequence[Outcome]) -> Rates:
    check(bool(outcomes), "empty frequency row")
    return tuple(F(sum(row[i] for row in outcomes), len(outcomes)) for i in range(3))


def rates(trials: Sequence[Trial]) -> Rates:
    return frequencies(tuple(trial.outcome for trial in trials))


def fixed_mask_rates(source: int, closed: int, closed_plate: bool,
                     other_plate: bool, mask: int) -> Rates:
    """Intervene on the mask stock before launch; keep every source seed."""
    opened = tuple(i != closed for i in ARMS)
    plates = tuple(closed_plate if i == closed else other_plate for i in ARMS)
    masks = tuple(mask if i == closed else 0 for i in ARMS)
    return rates(tuple(run_trial(source, seed, masks, plates, opened) for seed in SOURCE_SEEDS))


def eight_label_rates(source: int, plates: Switches, opened: Switches,
                      *, fixed_closed: int | None = None) -> Rates:
    """Actual older full-tag-swap comparator, with its own source stock."""
    dump_support = tuple((fixed_closed,) if fixed_closed is not None and not opened[i]
                         else ARMS for i in ARMS)
    return frequencies(tuple(
        eight_label_trial(source, particle, vacuum, (left, right), plates, opened)
        for particle, vacuum, left, right in product(ARMS, ARMS, *dump_support)
    ))


def mirror(state: State) -> State:
    return state[3:6] + state[:3] + state[8:10] + state[6:8]


def relabel(state: State) -> State:
    """Rename blank labels 1↔2, including all stock and the local rule."""
    return tuple((0, 2, 1, 3)[label] for label in state)


def relabel_replay(trial: Trial, plates: Switches, opened: Switches) -> tuple[State, ...]:
    def conjugated(pair: Pair) -> Pair:
        return relabel(four_label_contact(relabel(pair)))

    return replay(relabel(trial.initial), schedule(plates, opened), conjugated)


def verify_raw_contact() -> int:
    pairs = set(product(range(4), repeat=2))
    check({four_label_contact(pair) for pair in pairs} == pairs, "raw rule is not a bijection")
    for pair in pairs:
        image = four_label_contact(pair)
        check(image.count(TOKEN) == pair.count(TOKEN), f"raw rule changes number at {pair}")
        check(four_label_contact(image) == pair, f"raw rule is not an involution at {pair}")
        check(four_label_contact(pair[::-1]) == image[::-1], f"raw rule breaks mirror at {pair}")
        check(pair[0] != pair[1] or image == pair, f"raw rule changes diagonal at {pair}")
    check(four_label_contact(four_label_contact((0, 1))) != (1, 0), "rule squared to swap")
    return len(pairs)


def verify_code() -> int:
    decoded = set()
    analyzed = set()
    for source in ARMS:
        path_counts: Counter[int] = Counter()
        for seeds in SOURCE_SEEDS:
            run = run_trial(source, seeds, (0, 2), (False, False), (True, True))
            path, left, right = bits = decode(run.split)
            check(path ^ left ^ right == source, "splitter changed encoded parity")
            path_counts[path] += 1
            decoded.add(bits)
            check(run.output == run.initial, "full raw echo failed")
            analyzed.add((source, *(run.output[i] for i in EDGE)))
            check(replay(replay(run.split, M)[-1], M)[-1] == run.split, "M is not involutive on code")
        check(path_counts == {0: 2, 1: 2}, "splitter paths are not balanced")
    check(decoded == set(product(ARMS, repeat=3)), "splitter does not span all eight code states")
    check(analyzed == set(product(ARMS, (1, 2), (1, 2))), "analyzer misses raw output stock")
    return len(decoded)


def routed(port: int, weight: F) -> Rates:
    return (F(0), weight, 1 - weight) if port else (weight, F(0), 1 - weight)


def swap_ports(row: Outcome | Rates) -> Outcome | Rates:
    return row[1], row[0], row[2]


def verify() -> tuple[int, int, int]:
    raw_count = verify_raw_contact()
    verify_code()
    check(max_degree(schedule((True, True), (True, True))) == 3, "wrong core degree")
    check(max_degree(schedule((True, True), (False, False))) == 4, "wrong full degree")
    rows = enumerate_rows()
    total = 0
    for (source, plates, opened), trials in rows.items():
        check(tuple((t.source_seed, t.mask_seed) for t in trials) == tuple(product(SOURCE_SEEDS, MASK_SEEDS)),
              "row did not retain the full launch grid")
        total += len(trials)
        dest = source ^ plates[0] ^ plates[1]
        expected = (routed(dest, F(1)) if all(opened) else (F(1, 4), F(1, 4), F(1, 2))
                    if any(opened) else (F(0), F(0), F(1)))
        check(rates(trials) == expected, f"wrong L/R/loss rates at {(source, plates, opened)}")
        check(rates(trials) == swap_ports(eight_label_rates(source, plates, opened)),
              "older averaged rows differ beyond the fixed detector relabeling")
        for t in trials:
            path, left, right = decode(t.split)
            check(decode(t.plated) == (path, left ^ plates[0], right ^ plates[1]), "wrong plate action")
            check(all(state[i] == 0 for state in t.trace for i in ZERO), "zero reference changed")
            phases = (left ^ plates[0], right ^ plates[1])
            for arm in ARMS:
                absorbed = int(arm == path and not opened[arm])
                # The shutter first normalizes O0/O1 to (3,2)/(3,1).
                # Dumping the token therefore complements the code bit only
                # for an occupied arm; the mask then flips either vacuum bit.
                expected_arm = (arm_pair(t.plated, arm) if opened[arm]
                                else V[phases[arm] ^ absorbed ^ int(t.mask_seed[arm] == 0)])
                check(arm_pair(t.shuttered, arm) == expected_arm, "wrong shutter code")
                check(t.shuttered[DUMP[arm]] == (TOKEN if absorbed else 1), "wrong dump capture")
                check(t.output[DUMP[arm]] == t.shuttered[DUMP[arm]], "dump not sealed from analyzer")
                check(t.output[MASK[arm]] == t.mask_seed[arm], "mask stock changed")
            loss = int(not opened[path])
            check(sum(t.outcome) == 1 and t.outcome[2] == loss, "token escaped readout and loss")
            reflected = run_trial(1 - source, t.source_seed[::-1], t.mask_seed[::-1],
                                  plates[::-1], opened[::-1])
            check(reflected.output == mirror(t.output) and reflected.outcome == swap_ports(t.outcome),
                  "mirror covariance failed")
            check(relabel_replay(t, plates, opened) == tuple(map(relabel, t.trace)),
                  "raw rename did not conjugate the circuit")

    for source, closed, other_plate in product(ARMS, ARMS, (False, True)):
        opened = tuple(i != closed for i in ARMS)
        before = tuple(other_plate if i != closed else False for i in ARMS)
        after = tuple(other_plate if i != closed else True for i in ARMS)
        for mask in (0, 2):
            base = fixed_mask_rates(source, closed, False, other_plate, mask)
            toggle = fixed_mask_rates(source, closed, True, other_plate, mask)
            dest = source ^ other_plate ^ int(mask == 0)
            check(base == routed(dest, F(1, 2)) and toggle == swap_ports(base),
                  "fixed-mask control did not expose the old closed-arm bit")
            check(toggle == fixed_mask_rates(source, closed, False, other_plate, 2 - mask),
                  "complement mask and complement old bit did not agree")
            comparator = eight_label_rates(source, before, opened, fixed_closed=mask // 2)
            check(comparator == eight_label_rates(source, after, opened, fixed_closed=mask // 2),
                  "full-tag replacement did not erase the closed-arm setting")
    check(total == 512 and len(rows) == 32, "wrong total trial or row count")
    return total, len(rows), raw_count


def main() -> None:
    trials, rows, raw_count = verify()
    print(f"Four-label packet arms: {trials} launches, {rows} L/R/loss rows, {raw_count} raw inputs checked.")
    print("Reciprocal full-state echo; single-open rates (1/4, 1/4, 1/2); both closed all loss.")
    print("Fixed mask: toggling the closed-arm plate swaps detected ports; full-tag replacement does not.")
    print("Finite scheduled circuit only: stock, masks, contacts and occupancy readout are supplied.")


if __name__ == "__main__":
    main()
