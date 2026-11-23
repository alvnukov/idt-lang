"""A finite four-label two-arm circuit with mobile blanks and clean shutters.

All updates use B, the original contact plus 12 <-> 21.  The source stock,
the two-rail topology, the words, the local reference/replacement stocks and
the final number meter are supplied.  Nothing reads, measures or decodes the
arm bits to select a contact.  This is a scheduled reversible classical
fixture, not a full raw SWAP, an experimental result, or a Born derivation.
"""

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
from functools import cache
from itertools import product
import json

from scripts import probe_colorless_packet_arms as legacy
from scripts.probe_eight_label_interferometer import check
from scripts.probe_packet_free_pair_record import four_label_contact

Pair = tuple[int, int]
Arms = tuple[Pair, Pair]
State = tuple[int, ...]
Layer = tuple[Pair, ...]
Word = tuple[Layer, ...]
Switches = tuple[bool, bool]
Geometry = tuple[int, int, int, int]  # h_L, h_R, g_L, g_R
Outcome = tuple[int, int, int]  # left detector, right detector, isolated dumps
Setting = tuple[int, Switches, Switches]

TOKEN = 3
SEEDS = tuple(product((1, 2), repeat=2))
SWITCHES = tuple(product((False, True), repeat=2))
SETTINGS = tuple(product((0, 1), SWITCHES, SWITCHES))
HOPS = (0, 1, 2, 5)
V = ((2, 1), (2, 2))
O = ((3, 1), (1, 3))

# Hub layout: D_L,E_L,Z_L,D_R,E_R,Z_R.  A, Y contact both arms;
# C is the single E_L--E_R contact.  Order is chronological.
A = ((0, 1), (3, 4))
Y = ((2, 1), (5, 4))
C = (((1, 4),),)
Q = (A, Y, A)
SPLITTER = C + Q + C + Q + C + Q + C
ANALYZER = SPLITTER

# One plate: X = B(Z,D), A_local = B(D,E).
X = ((2, 0),)
A_LOCAL = ((0, 1),)
PLATE = (X, A_LOCAL, X, A_LOCAL, X)

# D,E,dumpD,dumpE,refillD,refillE: dump first; refill the same rails second.
SHUTTER = (((0, 2), (1, 3)), ((4, 0), (5, 1)))


def contact(pair: Pair) -> Pair:
    return pair[::-1] if pair in ((1, 2), (2, 1)) else four_label_contact(pair)


@dataclass(frozen=True)
class Trace:
    word: Word
    states: tuple[State, ...]  # one state after each individual pair contact

    @property
    def initial(self) -> State:
        return self.states[0]

    @property
    def output(self) -> State:
        return self.states[-1]


def _replay(initial: State, word: Word) -> Trace:
    cells = list(initial)
    number = initial.count(TOKEN)
    states = [initial]
    for layer in word:
        sites = tuple(site for pair in layer for site in pair)
        check(len(sites) == len(set(sites)), f"overlapping contact layer: {layer}")
        for a, b in layer:
            cells[a], cells[b] = contact((cells[a], cells[b]))
            state = tuple(cells)
            check(state.count(TOKEN) == number, f"number changed at contact {(a, b)}")
            states.append(state)
    return Trace(word, tuple(states))


@cache
def relay(pair: Pair, hops: int) -> Trace:
    check(hops in HOPS and all(label in (1, 2, 3) for label in pair), "unsupported relay stock")
    word = tuple(((2 * i, 2 * i + 2), (2 * i + 1, 2 * i + 3)) for i in range(hops))
    trace = _replay(pair + (1, 1) * hops, word)
    for i in range(hops + 1):
        check(trace.states[2 * i] == (1, 1) * i + pair + (1, 1) * (hops - i),
              "raw rail pair did not advance into fresh stock and leave fresh stock behind")
    return trace


@cache
def plate(pair: Pair, enabled: bool) -> Trace:
    trace = _replay((*pair, 0), PLATE if enabled else ())
    check(all(state[2] == 0 for state in trace.states), "plate reference changed")
    return trace


@cache
def shutter(pair: Pair, opened: bool, replacement: int) -> Trace:
    check(replacement in (1, 2), "unsupported shutter stock")
    trace = _replay((*pair, 1, 1, 2, replacement), () if opened else SHUTTER)
    if not opened:
        check(trace.states[2] == (1, 1, *pair, 2, replacement), "shutter did not dump both raw labels")
        check(trace.output == (2, replacement, *pair, 1, 1), "incorrect refill or dump change")
    return trace


@cache
def _hub(arms: Arms, word: Word) -> Trace:
    left, right = arms
    trace = _replay((*left, 0, *right, 0), word)
    check(all(state[2] == state[5] == 0 for state in trace.states), "hub reference changed")
    return trace


def _rails(state: State) -> Arms:
    return (state[0], state[1]), (state[3], state[4])


def decode(state: State) -> tuple[int, int, int]:
    """Audit-only decoding; used after simulation, never in the schedule."""
    left, right = _rails(state)
    if left in O and right in V:
        return 0, O.index(left), V.index(right)
    if left in V and right in O:
        return 1, V.index(left), O.index(right)
    raise AssertionError(f"not a one-token code state: {(left, right)}")


@dataclass(frozen=True)
class ArmTrace:
    inbound: Trace
    plate: Trace
    shutter: Trace
    outbound: Trace

    @property
    def arriving(self) -> Pair:
        return self.outbound.output[-2:]

    @property
    def dump(self) -> Pair:
        return self.shutter.output[2:4]


@cache
def _arm(pair: Pair, enabled: bool, opened: bool, replacement: int, h: int, g: int) -> ArmTrace:
    inbound = relay(pair, h)
    plated = plate(inbound.output[-2:], enabled)
    shuttered = shutter(plated.output[:2], opened, replacement)
    outbound = relay(shuttered.output[:2], g)
    return ArmTrace(inbound, plated, shuttered, outbound)


@dataclass(frozen=True)
class Embedded:
    trace: Trace
    references: tuple[int, ...]
    retired: tuple[int, ...]
    dumps: Arms
    refills: Arms
    detectors: Pair

    @property
    def max_degree(self) -> int:
        edges = {tuple(sorted(pair)) for layer in self.trace.word for pair in layer}
        return max(Counter(i for edge in edges for i in edge).values(), default=0)


@dataclass(frozen=True)
class Trial:
    split: Trace
    arms: tuple[ArmTrace, ArmTrace]
    analyzer: Trace

    @property
    def outcome(self) -> Outcome:
        result = self.analyzer.output
        return (int(result[0] == TOKEN), int(result[3] == TOKEN),
                sum(arm.dump.count(TOKEN) for arm in self.arms))

    def embed(self) -> Embedded:
        """Replay the same witnesses on one array of physical cell indices.

        Only the D,E boundary of a section can alias predecessor cells.
        Everything else receives a new index, even for zero-hop separations.
        Each projection is compared after every contact, not only at endpoints.
        """
        stock = list(self.split.initial)
        pieces = [(self.split, tuple(range(len(stock))))]

        def append(trace: Trace, wires: tuple[int | None, ...]) -> tuple[int, ...]:
            mapping = []
            for label, wire in zip(trace.initial, wires, strict=True):
                if wire is None:
                    wire = len(stock)
                    stock.append(label)
                mapping.append(wire)
            indices = tuple(mapping)
            pieces.append((trace, indices))
            return indices

        references = [2, 5]
        retired = []
        dumps = []
        refills = []
        arrive = []
        for arm, source_rails in zip(self.arms, ((0, 1), (3, 4)), strict=True):
            before = append(arm.inbound, source_rails + (None,) * (len(arm.inbound.initial) - 2))
            retired.extend(before[:-2])
            rails = before[-2:]
            local = append(arm.plate, (*rails, None))
            references.append(local[2])
            local = append(arm.shutter, (*rails, None, None, None, None))
            dumps.append(local[2:4])
            refills.append(local[4:6])
            after = append(arm.outbound, rails + (None,) * (len(arm.outbound.initial) - 2))
            retired.extend(after[:-2])
            arrive.append(after[-2:])
        hub = append(self.analyzer, (*arrive[0], None, *arrive[1], None))
        references.extend((hub[2], hub[5]))
        word = tuple(tuple((sites[a], sites[b]) for a, b in layer)
                     for trace, sites in pieces for layer in trace.word)
        whole = _replay(tuple(stock), word)
        offset = 0
        for trace, sites in pieces:
            for idx, expected in enumerate(trace.states):
                actual = tuple(whole.states[offset + idx][i] for i in sites)
                check(actual == expected, "physical trace disagrees with local witness")
            offset += len(trace.states) - 1
        check(len(set(references)) == 6, "shared stage reference")
        check(all(whole.output[i] == 1 for i in retired), "retired lane not returned to 1")
        for arm, dump_sites, refill_sites in zip(self.arms, dumps, refills, strict=True):
            check(tuple(whole.output[i] for i in dump_sites) == arm.dump, "dump not isolated")
            check(tuple(whole.output[i] for i in refill_sites) == arm.shutter.output[4:6],
                  "refill stock changed after shutter")
        return Embedded(whole, tuple(references), tuple(retired), tuple(dumps), tuple(refills),
                        (hub[0], hub[3]))


def run_trial(source: int, plates: Switches, opened: Switches, seeds: Pair, replacements: Pair,
              geometry: Geometry = (0, 0, 0, 0)) -> Trial:
    check(source in (0, 1) and seeds in SEEDS and replacements in SEEDS
          and plates in SWITCHES and opened in SWITCHES, "unsupported setting or launch stock")
    h_left, h_right, g_left, g_right = geometry
    split = _hub(((TOKEN if source == 0 else 1, seeds[0]),
                  (TOKEN if source == 1 else 1, seeds[1])), SPLITTER)
    left, right = _rails(split.output)
    arms = (_arm(left, plates[0], opened[0], replacements[0], h_left, g_left),
            _arm(right, plates[1], opened[1], replacements[1], h_right, g_right))
    analyzer = _hub((arms[0].arriving, arms[1].arriving), ANALYZER)
    return Trial(split, arms, analyzer)


def _expected(source: int, plates: Switches, opened: Switches) -> Outcome:
    """Exact counts per 16 equally weighted pairs of source/replacement stock."""
    if all(opened):
        dest = source ^ plates[0] ^ plates[1]
        return 16 * int(dest == 0), 16 * int(dest == 1), 0
    if any(opened):
        return 4, 4, 8
    return 0, 0, 16


def _old_rows() -> tuple[int, tuple[Setting, ...]]:
    original_passed = 0
    modified_passed = []
    for source, plates, opened in SETTINGS:
        word = legacy.schedule(plates, opened)
        stock = tuple(legacy.initial_state(source, seeds, masks) for seeds, masks in
                      product(legacy.SOURCE_SEEDS, legacy.MASK_SEEDS))
        expected = _expected(source, plates, opened)
        original = tuple(legacy.meter(legacy.replay(raw, word)[-1]) for raw in stock)
        changed = tuple(legacy.meter(_replay(raw, word).output) for raw in stock)
        original_passed += tuple(map(sum, zip(*original))) == expected
        if tuple(map(sum, zip(*changed))) == expected:
            modified_passed.append((source, plates, opened))
    return original_passed, tuple(modified_passed)


@dataclass(frozen=True)
class Evidence:
    endpoint_launches: int
    setting_rows: int
    geometries: int
    joint_launches: int
    joint_outcome_counts: Outcome
    fixed_stock_interventions: int
    supported_raw_contacts: int
    max_embedded_degree: int
    legacy_original_rows_passed: int
    legacy_rows_passed: int
    legacy_rows_total: int
    legacy_passing_settings: tuple[Setting, ...]


def verify() -> Evidence:
    raw_pairs = tuple(product(range(4), repeat=2))
    changed = tuple(pair for pair in raw_pairs if contact(pair) != four_label_contact(pair))
    check(changed == ((1, 2), (2, 1)), "not the single specified law edit")
    for pair in raw_pairs:
        after = contact(pair)
        check(contact(after) == pair and contact(pair[::-1]) == after[::-1]
              and after.count(TOKEN) == pair.count(TOKEN), "contact invariants failed")
    check(all(contact((x, 1)) == (1, x) for x in (1, 2, 3)), "fresh-1 relay is not exact")
    check(ANALYZER == SPLITTER == SPLITTER[::-1], "the two hub words are not the same palindrome")

    # Endpoints certify the finite statistics. All 256 geometries separately
    # preserve the full analyzer input (not just its meter), all isolated
    # dump/refill pairs, and the discarded relay lanes. This composes the
    # local per-contact certificates without replicating 131072 global arrays.
    rows = {}
    seen_split = set()
    for source in (0, 1):
        paths = []
        for seeds in SEEDS:
            trial = run_trial(source, (False, False), (True, True), seeds, (1, 1))
            path, left, right = decode(trial.split.output)
            check(path ^ left ^ right == source, "split code parity disagrees with source port")
            check(trial.analyzer.output == trial.split.initial, "raw logical source did not echo")
            paths.append(path)
            seen_split.add(trial.split.output)
        check(sorted(paths) == [0, 0, 1, 1], "split path is not balanced")
    check(len(seen_split) == 8, "source did not cover the full one-token code")

    interventions = 0
    totals = [0, 0, 0]
    for source, plates, opened in SETTINGS:
        counted = [0, 0, 0]
        for seeds, replacements in product(SEEDS, repeat=2):
            trial = run_trial(source, plates, opened, seeds, replacements)
            rows[source, plates, opened, seeds, replacements] = trial
            path, lbit, rbit = decode(trial.split.output)
            for side, (arm, bit) in enumerate(zip(trial.arms, (lbit, rbit), strict=True)):
                code = O if side == path else V
                plated = code[bit ^ plates[side]]
                check(arm.plate.output == (*plated, 0), "wrong local plate bit")
                check(arm.shutter.output == ((*plated, 1, 1, 2, replacements[side]) if opened[side]
                      else (2, replacements[side], *plated, 1, 1)), "shutter boundary changed")
            outcome = trial.outcome
            check(sum(outcome) == 1 and outcome[2] == int(not opened[path]), "unaccounted token or loss")
            for side, value in enumerate(outcome):
                counted[side] += value
        check(tuple(counted) == _expected(source, plates, opened), "wrong exact detector/loss row")
        for side, value in enumerate(counted):
            totals[side] += value

    for (source, plates, opened, seeds, replacements), trial in rows.items():
        for closed in (0, 1):
            if opened[closed] or plates[closed]:
                continue
            toggled = tuple(setting or i == closed for i, setting in enumerate(plates))
            other = rows[source, toggled, opened, seeds, replacements]
            check(other.outcome == trial.outcome and other.analyzer.initial == trial.analyzer.initial,
                  "closed-plate intervention leaked outside its dump at fixed replacement stock")
            check(other.arms[closed].dump != trial.arms[closed].dump, "dump did not retain old raw state")
            check(other.arms[1 - closed].dump == trial.arms[1 - closed].dump,
                  "closed plate changed the other isolated dump")
            interventions += 1

    geometries = 0
    joint = 0
    degree = 0
    for geometry in product(HOPS, repeat=4):
        geometries += 1
        # Exercise the physical embedding at each geometry with every plate
        # and shutter edge present. Within a phase independent arms commute.
        embedded = run_trial(0, (True, True), (False, False), (2, 1), (2, 1), geometry).embed()
        degree = max(degree, embedded.max_degree)
        for row, endpoint in rows.items():
            trial = run_trial(*row, geometry)
            check(trial.analyzer == endpoint.analyzer and
                  all(arm.shutter == reference.shutter for arm, reference in zip(trial.arms, endpoint.arms)),
                  "separation changed a shutter boundary or analyzer input")
            joint += 1
    check((len(rows), geometries, joint, interventions, tuple(totals))
          == (512, 256, 131072, 256, (128, 128, 256)), "fixture coverage or outcomes changed")
    old_original, old_changed = _old_rows()
    check((old_original, len(old_changed)) == (32, 2), "legacy positive/negative control changed")
    return Evidence(len(rows), len(SETTINGS), geometries, joint, tuple(n * geometries for n in totals),
                    interventions, len(raw_pairs), degree, old_original, len(old_changed),
                    len(SETTINGS), old_changed)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print the evidence counts and fixture contract as JSON")
    args = parser.parse_args()
    evidence = verify()
    if args.json:
        print(json.dumps({
            **asdict(evidence),
            "scope": "finite scheduled reversible classical witness; no full raw SWAP or Born claim",
            "law_edit": "12 <-> 21, all other ordered pairs unchanged",
            "stock": {"source": "D_source=3; D_other=1; E_L,E_R iid fair {1,2}",
                      "references": "distinct 0 at each arm of source, plates, and analyzer",
                      "relay": "fresh 1 at each D/E hop", "dump_and_refill": "fresh dump (1,1), refill (2,fair{1,2}) per arm"},
            "schedule": {"both_hubs": "C Q C Q C Q C", "Q": "A Y A on both arms",
                         "A": "B(D,E)", "Y": "B(Z,E)", "C": "B(E_L,E_R)",
                         "plate": "X A X A X locally", "X": "B(Z,D)",
                         "shutter": "B(D,dumpD) || B(E,dumpE); then B(refillD,D) || B(refillE,E)",
                         "geometry_order": ["h_L", "h_R", "g_L", "g_R"], "hops_per_leg": HOPS},
        }, indent=2))
    else:
        print(f"Mobile blanks: {evidence.endpoint_launches} endpoint launches, {evidence.geometries} geometries, "
              f"{evidence.joint_launches} joint launches; L/R/loss counts {evidence.joint_outcome_counts}.")
        print("Both open: source XOR local plates; one open: (1/4, 1/4, 1/2); both closed: loss 1.")
        print(f"Old source/program: original law {evidence.legacy_original_rows_passed}/32, "
              f"modified law {evidence.legacy_rows_passed}/32. Finite scheduled classical witness only.")


if __name__ == "__main__":
    main()
