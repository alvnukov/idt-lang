"""Exact open-arm control: replace only the scheduled analyzer by edge clocks.

The reciprocal launch/splitter, optional late plates, fair shade seeds, three
clock laws, and occupancy readout are supplied. Only the analyzer has no pulse
word. This tests a small classical routing transient, not interference, physical
timing, a closed-arm experiment, or a derivation of QM.
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import permutations, product

from scripts import probe_colorless_packet_arms as frozen
from scripts.probe_colorless_packet_arms import State, Switches, check, four_label_contact


Distribution = tuple[F, ...]
Matrix = tuple[Distribution, ...]
Setting = tuple[int, Switches]

CONTACTS = frozen.A + frozen.Z + frozen.C
SITES = (frozen.DETECTOR[0], frozen.EDGE[0], frozen.DETECTOR[1], frozen.EDGE[1])
PARKED_MASKS = (0, 0)  # Disconnected in the both-open experiment; not re-sampled.
CERTIFICATE_TICK = 4
SWEEP_DIP_TICK = 38


def prepared_states(source: int, plates: Switches) -> tuple[State, ...]:
    """Four equally weighted launches with independent arm shades, no shutters."""
    word = frozen.SPLITTER + frozen.plate_word(plates)
    return tuple(frozen.replay(frozen.initial_state(source, seed, PARKED_MASKS), word)[-1]
                 for seed in frozen.SOURCE_SEEDS)


def contact(state: State, edge: tuple[int, int]) -> State:
    i, j = edge
    left, right = four_label_contact((state[i], state[j]))
    cells = list(state)
    cells[i], cells[j] = left, right
    return tuple(cells)


def reachable(prepared: tuple[State, ...]) -> tuple[State, ...]:
    todo = list(prepared)
    seen = set(todo)
    while todo:
        state = todo.pop()
        for edge in CONTACTS:
            after = contact(state, edge)
            if after not in seen:
                todo.append(after)
                seen.add(after)
    return tuple(sorted(seen))


def advance(distribution: Distribution, matrix: Matrix) -> Distribution:
    return tuple(sum((p * q for p, q in zip(distribution, column, strict=True)), F(0))
                 for column in zip(*matrix, strict=True))


@dataclass(frozen=True)
class Clock:
    unit: str
    operations_per_tick: int
    matrix: Matrix
    stationary: Distribution


def clock_tables(states: tuple[State, ...]) -> dict[str, Clock]:
    ix = {state: i for i, state in enumerate(states)}
    moves = tuple(tuple(ix[contact(state, edge)] for edge in CONTACTS) for state in states)
    active = tuple(tuple(j for j in row if j != i) for i, row in enumerate(moves))
    check(all(active), "active-event clock would be undefined at an absorbing state")
    schedules = tuple(permutations(range(len(CONTACTS))))
    sweep = []
    for start in range(len(states)):
        outcomes = []
        for order in schedules:
            current = start
            for edge in order:
                current = moves[current][edge]
            outcomes.append(current)
        sweep.append(tuple(outcomes))

    def matrix(offers: tuple[tuple[int, ...], ...]) -> Matrix:
        rows = []
        for row in offers:
            counts = Counter(row)
            rows.append(tuple(F(counts[j], len(row)) for j in range(len(states))))
        return tuple(rows)

    # Each contact is an involution. Its attempt kernel and every complete
    # permutation of contacts preserve uniform mass. Counting changing offers
    # in both directions gives detailed balance for the active-event kernel.
    uniform = (F(1, len(states)),) * len(states)
    degree_sum = sum(map(len, active))
    weighted = tuple(F(len(row), degree_sum) for row in active)
    return {
        "attempted_edges": Clock("attempted edge", 1, matrix(moves), uniform),
        "active_offers": Clock("active edge offer", 1, matrix(active), weighted),
        "permutation_sweeps": Clock("complete five-edge permutation sweep", len(CONTACTS),
                                    matrix(tuple(sweep)), uniform),
    }


@dataclass(frozen=True)
class Readout:
    sites: tuple[F, F, F, F]  # (D_L, E_L, D_R, E_R)

    @property
    def arms(self) -> tuple[F, F]:
        dl, el, dr, er = self.sites
        return dl + el, dr + er

    @property
    def fixed_detector(self) -> tuple[F, F, F]:
        dl, el, dr, er = self.sites
        return dl, dr, el + er

    def correct_given_detector_click(self, correct_arm: int) -> F | None:
        left, right, _ = self.fixed_detector
        return (left, right)[correct_arm] / (left + right) if left + right else None


def read(distribution: Distribution, states: tuple[State, ...]) -> Readout:
    def site_mass(site: int) -> F:
        return sum((p for p, raw in zip(distribution, states, strict=True)
                    if raw[site] == frozen.TOKEN), F(0))

    return Readout(tuple(map(site_mass, SITES)))


@dataclass(frozen=True)
class Tick:
    distribution: Distribution
    readout: Readout


@dataclass(frozen=True)
class Trajectory:
    prefix: tuple[Tick, ...]
    maximum: F
    maximizing_ticks: tuple[int, ...]
    tail_tv: F


def certify(initial: Distribution, states: tuple[State, ...], clock: Clock,
            correct_arm: int) -> Trajectory:
    prefix = [Tick(initial, read(initial, states))]
    for _ in range(CERTIFICATE_TICK):
        after = advance(prefix[-1].distribution, clock.matrix)
        prefix.append(Tick(after, read(after, states)))
    probabilities = tuple(t.readout.arms[correct_arm] for t in prefix)
    maximum = max(probabilities)
    tail_tv = sum(abs(p - q) for p, q in zip(prefix[-1].distribution,
                                            clock.stationary, strict=True)) / 2
    # For every later whole tick, TV to an invariant law is nonincreasing
    # under a stochastic matrix, and indicator-event deviation is <= TV.
    # Thus this strict bound rules out any later larger or equal maximum;
    # it says nothing about monotonicity or the sign of later deviations.
    stationary_read = read(clock.stationary, states)
    check(stationary_read.arms[correct_arm] + tail_tv < maximum, "uncertified maximum")
    return Trajectory(tuple(prefix), maximum,
                      tuple(t for t, p in enumerate(probabilities) if p == maximum), tail_tv)


@dataclass(frozen=True)
class Row:
    correct_arm: int
    initial: Distribution
    trajectories: dict[str, Trajectory]


@dataclass(frozen=True)
class Evidence:
    states: tuple[State, ...]
    clocks: dict[str, Clock]
    rows: dict[Setting, Row]
    sweep_dip_tick: int


def verify() -> Evidence:
    frozen.verify_raw_contact()
    prepared = {(source, plates): prepared_states(source, plates)
                for source, plates in product(frozen.ARMS, frozen.SWITCHES)}
    states = reachable(prepared[0, (False, False)])
    check(len(CONTACTS) == 5 and len({frozenset(edge) for edge in CONTACTS}) == 5,
          "clock must offer exactly five undirected contacts")
    check(len(states) == 12, "not the frozen 12-state orbit")
    check(all(raw.count(frozen.TOKEN) == 1 and raw.index(frozen.TOKEN) in SITES
              and raw[2] == raw[5] == 0 and raw[6:] == (1, 0, 1, 0) for raw in states),
          "token, fixed reference, or parked stock escaped the readout model")
    check(all(len(set(samples)) == 4 and reachable(samples) == states
              for samples in prepared.values()), "not four launches into the same raw orbit per row")
    reflected_ix = tuple(states.index(frozen.mirror(raw)) for raw in states)
    clocks = clock_tables(states)
    for name, clock in clocks.items():
        check(all(sum(row) == 1 and all(p >= 0 for p in row) for row in clock.matrix),
              f"nonstochastic clock: {name}")
        check(sum(clock.stationary) == 1 and all(p > 0 for p in clock.stationary)
              and advance(clock.stationary, clock.matrix) == clock.stationary
              and read(clock.stationary, states).arms == (F(1, 2), F(1, 2)),
              f"incorrect stationary reference law: {name}")
        check(all(clock.matrix[i][j] == clock.matrix[ri][rj]
                  for i, ri in enumerate(reflected_ix) for j, rj in enumerate(reflected_ix)),
              f"clock breaks reflection: {name}")

    rows = {}
    for (source, plates), samples in prepared.items():
        correct_arm = source ^ plates[0] ^ plates[1]
        check(Counter(samples) == Counter(prepared[correct_arm, (False, False)]),
              "fair seed ensemble does not reduce to the late-plate parity target")
        mirror = prepared[1 - source, plates[::-1]]
        check(all(frozen.mirror(raw) == mirror[frozen.SOURCE_SEEDS.index(seed[::-1])]
                  for seed, raw in zip(frozen.SOURCE_SEEDS, samples, strict=True)),
              "seed-conditional preparation breaks reflection")
        initial = tuple(F(samples.count(raw), len(samples)) for raw in states)
        check(sum(initial) == 1 and read(initial, states).arms == (F(1, 2), F(1, 2)),
              "invalid initial ensemble")
        trajectories = {name: certify(initial, states, clock, correct_arm)
                        for name, clock in clocks.items()}
        for name, result in trajectories.items():
            expected = {
                "attempted_edges": (F(11, 20), (1, 2), F(23, 500)),
                "active_offers": (F(7, 12), (1,), F(19, 288)),
                "permutation_sweeps": (F(1297, 2304), (2,), F(2153557, 46080000)),
            }[name]
            check((result.maximum, result.maximizing_ticks, result.tail_tv) == expected,
                  f"unexpected transient certificate for {(source, plates, name)}")
        rows[source, plates] = Row(correct_arm, initial, trajectories)

    left = rows[0, (False, False)]
    first = left.trajectories["attempted_edges"].prefix[1].readout
    check(first.sites == (F(3, 10), F(1, 4), F(3, 10), F(3, 20))
          and first.fixed_detector == (F(3, 10), F(3, 10), F(2, 5))
          and first.correct_given_detector_click(0) == F(1, 2), "unexpected first-attempt readout")
    distribution = left.initial
    for _ in range(SWEEP_DIP_TICK):
        distribution = advance(distribution, clocks["permutation_sweeps"].matrix)
    check(read(distribution, states).arms[0] < F(1, 2), "missing late sweep dip")
    return Evidence(states, clocks, rows, SWEEP_DIP_TICK)


def main() -> None:
    result = verify()
    print(f"Both open: {len(result.states)} raw states, {len(result.rows)} input/plate settings, "
          "4 fair launch seeds per setting; exactly one token.")
    left = result.rows[0, (False, False)]
    for name, clock in result.clocks.items():
        trajectory = left.trajectories[name]
        times = ",".join(map(str, trajectory.maximizing_ticks))
        print(f"{name}: maximum {trajectory.maximum}, tick(s) {times}; unit: {clock.unit} "
              f"({clock.operations_per_tick} contact operation(s)); stationary arm mass 1/2, "
              f"TV at tick {CERTIFICATE_TICK}: {trajectory.tail_tv}.")
    print("Active offers exclude stutters and count offers, not distinct destination states.")
    print("Each sweep independently samples one of 5! complete contact orders; maxima are at tick boundaries.")
    print(f"The sweep clock dips below 1/2 at tick {result.sweep_dip_tick}.")
    print("Sites=(D_L,E_L,D_R,E_R); D-only=(click L,click R,unresolved at E).")
    for (source, plates), row in result.rows.items():
        for name, trajectory in row.trajectories.items():
            for tick in trajectory.maximizing_ticks:
                readout = trajectory.prefix[tick].readout
                sites = ",".join(map(str, readout.sites))
                detectors = ",".join(map(str, readout.fixed_detector))
                conditional = readout.correct_given_detector_click(row.correct_arm)
                print(f"input={source} plates={int(plates[0])}{int(plates[1])} target={row.correct_arm} "
                      f"{name}@{tick}: sites=({sites}) D-only=({detectors}) "
                      f"P(correct D | D click)={conditional}")
    print("Small transient for furnished stock, clocks and readouts; no interference or autonomous timing claim.")


if __name__ == "__main__":
    main()
