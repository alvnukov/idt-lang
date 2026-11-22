"""Local matching resolvers: schedule-independent completion, not a physical clock.

Four colors are the supplied incident legs, not signed amplitudes. Free marks
and stored unordered pairs are distinct states. Unlike pair ab will eventually
emit the two complementary colors; equal pairs and unmatched marks remain
unchanged. Allocation/repair happens BEFORE that emission, so output marks do
not re-enter the current allocation layer. The companion
probe_complement_collision_mixer.py handles the later cyclic wiring/mixer.

TERNARY-OBJECT CANDIDATE. Use unlike bonds only:
  F_a+F_b -> B_ab                       (a!=b)
  2 F_a+B_bc -> B_ab+B_ac               (a not in {b,c}, b!=c).
Every rewrite removes two free marks. At a terminal state all free marks have
one color a. If at least two remain, every bond contains a, since otherwise
repair applies. For EVEN input stock S this gives exactly
  residual = max(0, 2*max_i n_i-S).
In particular, max_i n_i<=S/2 guarantees exhaustion under EVERY maximal
reduction, without a chosen sorted pairing. The repair is a three-object,
four-constituent encounter; that locality resource is explicit.

PREFERRED BINARY-COMPOUND RESOLVER. Add temporary equal-color reservations
B_aa, not new colors or trimers:
  F_a+F_b -> B_ab                       (including a=b)
  B_aa+B_bc -> B_ab+B_ac               (a not in {b,c}; b=c allowed)
  F_b+B_aa -> B_ab+F_a                 (b!=a; also handles odd stocks).
The first TWO rules alone are the tested `binary` even-stock core. The third
rule is enabled only in the separately checked `binary_odd` extension.
All reactions have at most TWO input and TWO output objects. A bond is still
a two-mark compound: this is not a two-elementary-particle derivation. The
integer potential #free + #equal-pairs strictly decreases. Pairing lowers it
by one or two, pair-pair repair by one or two, free-pair repair by one.
Hence every actual reduction sequence terminates; from S initially free marks
there are at most S rewrites. No transition probability or preferred schedule
is used. At a terminal state there is at most one free mark. If an equal pair
aa remains, all other pairs contain a. Even stock leaves no free mark; in the
odd-stock extension any remaining free mark must also be a. The relevant
resolver therefore leaves exactly the majority obstruction, retaining equal
pairs as residual rather than erasing or complementing them. On odd balanced
stock one unmatched color may vary, so histogram confluence is explicitly EVEN.

HISTOGRAM, NOT MICROSTATE, CONFLUENCE. Let r_i be residual free/equal-pair
constituents and B the number of unlike terminal pairs. Emission gives
  output_i = B - n_i + 2*r_i.
For balanced even stock r=0 and B=S/2, independently of every hidden pairing.
Different terminal pair sets and different labeled partner assignments remain.
Exhaustive checks below enumerate all state-level reduction paths on small
stocks; individual token identities are quotiented out, with separate labeled
countercontrols. The general termination/completion arguments are analytical,
not inferred from this finite census and not Lean proofs.

SCOPED LOWER-COMPLEXITY WALL. If the only states are F_a and UNORDERED unlike
B_ab, interactions conserve constituent colors, have at most two reactant
objects, and are fully S4-equivariant, the trap 2F_a+B_bc cannot be resolved
by pairing the two free a's. A nontrivial free-pair exchange must include
F_a+B_bc -> F_c+B_ab (or its b/c counterpart). Transposing a,c forces the
inverse rule, hence a two-cycle. Unbinding to three free marks also cycles
back via the admitted binding rule. Bond-pair interactions cannot help this
one-bond trap. Thus this restricted vocabulary cannot both repair every trap
and strongly terminate for arbitrary schedules. This is NOT a no-go for all
pairwise protocols with auxiliary states, ordering, fairness or records. Equal
reservations are precisely the small extra state used by the binary solution.

LIMITS. Maximal rewrite sequences exclude indefinitely refusing an enabled
reaction or inserting no-ops. The finite rewrite bound is not a wall-clock
encounter bound. Disconnected compartments can trap globally balanced inputs.
The irreversible state merging shown below needs history/environment records
for any reversible implementation. Terminal histogram agreement does not
detect termination, synchronize another collision layer, justify erasing hidden
pairing, or generate independent samples. Eagerly feeding complemented outputs
back into the same layer already cycles AB -> CD -> AB. No graph status,
physical realization, detector, Born rule, or QM claim is upgraded here.
"""

from __future__ import annotations

import argparse
import json
import unittest
from dataclasses import dataclass
from functools import cache
from itertools import combinations_with_replacement, permutations, product
from typing import Literal

Counts = tuple[int, ...]
Mode = Literal["naive", "ternary", "binary", "binary_odd"]
PAIRS = tuple(combinations_with_replacement(range(4), 2))
INDEX = {pair: index for index, pair in enumerate(PAIRS)}
ZERO_PAIRS = (0,) * len(PAIRS)


def need(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def pair_index(a: int, b: int) -> int:
    return INDEX[min(a, b), max(a, b)]


@dataclass(frozen=True)
class State:
    free: Counts
    bonds: Counts = ZERO_PAIRS

    def __post_init__(self) -> None:
        if (
            len(self.free) != 4
            or len(self.bonds) != len(PAIRS)
            or min(self.free + self.bonds) < 0
        ):
            raise ValueError(
                "nonnegative four-color free and ten-pair populations required"
            )

    def inventory(self) -> Counts:
        result = list(self.free)
        for amount, (a, b) in zip(self.bonds, PAIRS, strict=True):
            result[a] += amount
            result[b] += amount
        return tuple(result)

    def equal_pairs(self) -> int:
        return sum(self.bonds[pair_index(a, a)] for a in range(4))

    def residual(self) -> Counts:
        return tuple(self.free[a] + 2 * self.bonds[pair_index(a, a)] for a in range(4))

    def emission(self) -> Counts:
        result = list(self.residual())
        for amount, (a, b) in zip(self.bonds, PAIRS, strict=True):
            if a != b:
                for color in range(4):
                    if color not in (a, b):
                        result[color] += amount
        return tuple(result)


def update(
    state: State,
    free_changes: tuple[tuple[int, int], ...] = (),
    pair_changes: tuple[tuple[int, int], ...] = (),
) -> State:
    free, bonds = list(state.free), list(state.bonds)
    for color, amount in free_changes:
        free[color] += amount
    for index, amount in pair_changes:
        bonds[index] += amount
    result = State(tuple(free), tuple(bonds))
    need(
        result.inventory() == state.inventory(), "constituent color inventory preserved"
    )
    return result


def potential(state: State, mode: Mode) -> int:
    return sum(state.free) + (
        state.equal_pairs() if mode in ("binary", "binary_odd") else 0
    )


@cache
def successors(state: State, mode: Mode) -> frozenset[State]:
    if mode not in ("binary", "binary_odd"):
        need(state.equal_pairs() == 0, "unlike-only vocabulary")
    output: set[State] = set()
    for index, (a, b) in enumerate(PAIRS):
        if a == b:
            if mode in ("binary", "binary_odd") and state.free[a] >= 2:
                output.add(update(state, ((a, -2),), ((index, 1),)))
        elif state.free[a] and state.free[b]:
            output.add(update(state, ((a, -1), (b, -1)), ((index, 1),)))
    if mode == "ternary":
        for a in range(4):
            if state.free[a] >= 2:
                for index, (b, c) in enumerate(PAIRS):
                    if b != c and a not in (b, c) and state.bonds[index]:
                        output.add(
                            update(
                                state,
                                ((a, -2),),
                                (
                                    (index, -1),
                                    (pair_index(a, b), 1),
                                    (pair_index(a, c), 1),
                                ),
                            )
                        )
    if mode in ("binary", "binary_odd"):
        for a in range(4):
            equal = pair_index(a, a)
            if not state.bonds[equal]:
                continue
            for index, (b, c) in enumerate(PAIRS):
                if a not in (b, c) and state.bonds[index]:
                    output.add(
                        update(
                            state,
                            pair_changes=(
                                (equal, -1),
                                (index, -1),
                                (pair_index(a, b), 1),
                                (pair_index(a, c), 1),
                            ),
                        )
                    )
            for b in range(4):
                if mode == "binary_odd" and b != a and state.free[b]:
                    output.add(
                        update(
                            state,
                            ((b, -1), (a, 1)),
                            ((equal, -1), (pair_index(a, b), 1)),
                        )
                    )
    need(
        all(
            potential(next_state, mode) < potential(state, mode)
            for next_state in output
        ),
        "strict local termination potential",
    )
    return frozenset(output)


@dataclass(frozen=True)
class Resolution:
    terminals: frozenset[State]
    state_paths: int
    maximum_steps: int


@cache
def resolve(state: State, mode: Mode) -> Resolution:
    next_states = successors(state, mode)
    if not next_states:
        return Resolution(frozenset((state,)), 1, 0)
    tails = tuple(resolve(next_state, mode) for next_state in next_states)
    return Resolution(
        frozenset(terminal for tail in tails for terminal in tail.terminals),
        sum(tail.state_paths for tail in tails),
        1 + max(tail.maximum_steps for tail in tails),
    )


def stock_histograms(limit: int, parity: int) -> tuple[Counts, ...]:
    return tuple(
        n
        for n in product(range(limit + 1), repeat=4)
        if sum(n) <= limit and sum(n) % 2 == parity
    )


def census(limit: int = 8) -> dict[str, object]:
    if not 0 <= limit <= 10:
        raise ValueError("bounded census supports total stock at most ten")
    statistics = {}
    for mode in ("ternary", "binary"):
        paths, terminal_count, maximum_steps, inputs = 0, 0, 0, 0
        for n in stock_histograms(limit, 0):
            size, majority = sum(n), max(n)
            excess = max(0, 2 * majority - size)
            residual = tuple(
                excess if excess and value == majority else 0 for value in n
            )
            unlike_pairs = (size - excess) // 2
            expected = tuple(unlike_pairs - n[i] + 2 * residual[i] for i in range(4))
            result = resolve(State(n), mode)
            for terminal in result.terminals:
                need(
                    terminal.residual() == residual,
                    "exact even-stock majority obstruction",
                )
                need(
                    terminal.emission() == expected,
                    "schedule-independent terminal histogram",
                )
                need(
                    sum(terminal.emission()) == size,
                    "residuals are preserved, not discarded",
                )
                need(
                    not excess
                    or all(
                        not amount or majority == n[a] or majority == n[b]
                        for amount, (a, b) in zip(terminal.bonds, PAIRS, strict=True)
                    ),
                    "terminal bonds contain residual majority",
                )
            need(
                result.maximum_steps <= size,
                "binary finite rewrite bound (not encounter time)",
            )
            if mode == "ternary":
                need(
                    result.maximum_steps == unlike_pairs,
                    "each ternary reduction removes two free marks",
                )
            paths += result.state_paths
            terminal_count += len(result.terminals)
            maximum_steps = max(maximum_steps, result.maximum_steps)
            inputs += 1
        statistics[mode] = {
            "even_input_histograms": inputs,
            "terminal_state_instances": terminal_count,
            "all_distinct_state_schedule_paths": paths,
            "largest_rewrite_count": maximum_steps,
        }
    return {"maximum_total_stock": limit, "modes": statistics}


def make_state(free: Counts, pairs: tuple[tuple[int, int], ...]) -> State:
    bonds = [0] * len(PAIRS)
    for a, b in pairs:
        bonds[pair_index(a, b)] += 1
    return State(free, tuple(bonds))


def permute(state: State, labels: tuple[int, ...]) -> State:
    free, bonds = [0] * 4, [0] * len(PAIRS)
    for a in range(4):
        free[labels[a]] = state.free[a]
    for amount, (a, b) in zip(state.bonds, PAIRS, strict=True):
        bonds[pair_index(labels[a], labels[b])] += amount
    return State(tuple(free), tuple(bonds))


def equivariance_controls() -> int:
    checked = 0
    for mode in ("ternary", "binary", "binary_odd"):
        seen: set[State] = set()
        stack = [State(n) for n in stock_histograms(4, 0)]
        while stack:
            state = stack.pop()
            if state in seen:
                continue
            seen.add(state)
            stack.extend(successors(state, mode))
        for state in seen:
            for labels in permutations(range(4)):
                need(
                    {permute(item, labels) for item in successors(state, mode)}
                    == set(successors(permute(state, labels), mode)),
                    "S4-equivariant local relation, no privileged color priority",
                )
                checked += 1
    return checked


def trap_and_microstate_controls() -> dict[str, object]:
    initial = State((2, 1, 1, 0))
    trap = make_state((2, 0, 0, 0), ((1, 2),))
    need(
        trap in resolve(initial, "naive").terminals and trap.residual() == (2, 0, 0, 0),
        "naive unlike-only greedy trap",
    )
    complete = make_state((0, 0, 0, 0), ((0, 1), (0, 2)))
    need(
        resolve(initial, "ternary").terminals
        == resolve(initial, "binary").terminals
        == frozenset((complete,)),
        "both repairs clear balanced trap",
    )
    need(
        trap.emission() == (3, 0, 0, 1) and complete.emission() == (0, 1, 1, 2),
        "premature emission differs from complete layer",
    )
    equal = State((2, 0, 0, 0))
    need(
        all(
            state.emission() == equal.free
            for mode in ("ternary", "binary")
            for state in resolve(equal, mode).terminals
        ),
        "unrepairable equal pair remains intact",
    )
    distinct = resolve(State((1, 1, 1, 1)), "binary").terminals
    need(
        len(distinct) == 3
        and {state.emission() for state in distinct} == {(1, 1, 1, 1)},
        "three microscopic pair sets but one output histogram",
    )
    colors = (0, 0, 1, 2)
    first, second = ((0, 2), (1, 3)), ((0, 3), (1, 2))
    need(
        first != second
        and sorted(tuple(sorted((colors[i], colors[j]))) for i, j in first)
        == sorted(tuple(sorted((colors[i], colors[j]))) for i, j in second),
        "labeled partner records also survive histogram agreement",
    )
    odd = resolve(State((1, 1, 1, 0)), "binary").terminals
    need(
        len({state.emission() for state in odd}) == 3,
        "odd balanced residual does not have one output histogram",
    )
    for n in stock_histograms(7, 1):
        size, majority = sum(n), max(n)
        expected_count = max(1, 2 * majority - size)
        for mode in ("ternary", "binary_odd"):
            for terminal in resolve(State(n), mode).terminals:
                need(
                    sum(terminal.residual()) == expected_count,
                    "odd stock maximum matching, separate from histogram confluence",
                )
    odd_trap = State((2, 1, 0, 0))
    need(
        max(sum(state.residual()) for state in resolve(odd_trap, "binary").terminals)
        == 3
        and {
            sum(state.residual()) for state in resolve(odd_trap, "binary_odd").terminals
        }
        == {1},
        "third rule is genuinely needed for the stated odd-stock extension",
    )
    return {
        "naive_trap_input": initial.free,
        "naive_trap_emission": trap.emission(),
        "repaired_emission": complete.emission(),
        "distinct_terminal_pair_sets_for_1111": len(distinct),
        "odd_1110_output_histograms": 3,
        "equal_pair_residual_preserved": True,
        "odd_stock_requires_optional_third_rule": True,
    }


def lower_complexity_and_physical_controls() -> dict[str, object]:
    local_before = make_state((1, 0, 0, 0), ((1, 2),))
    local_after = make_state((0, 0, 1, 0), ((0, 1),))
    transposition = (2, 1, 0, 3)
    need(
        permute(local_before, transposition) == local_after
        and permute(local_after, transposition) == local_before,
        "equivariance forces inverse unlike-only exchange",
    )
    # Adding the same extra free a realizes the balanced trap cycle.
    cycle_first = make_state((2, 0, 0, 0), ((1, 2),))
    cycle_second = make_state((1, 0, 1, 0), ((0, 1),))
    need(
        cycle_first.inventory() == cycle_second.inventory(),
        "exchange cycle conserves balanced stock",
    )
    need(
        update(
            cycle_first,
            ((0, -1), (2, 1)),
            ((pair_index(1, 2), -1), (pair_index(0, 1), 1)),
        )
        == cycle_second
        and update(
            cycle_second,
            ((2, -1), (0, 1)),
            ((pair_index(0, 1), -1), (pair_index(1, 2), 1)),
        )
        == cycle_first,
        "two admitted unlike-only exchanges are an actual state cycle",
    )
    need(
        local_before in successors(make_state((1, 1, 1, 0), ()), "naive"),
        "unbinding has a binding inverse",
    )
    # Different previous states merge with no retained inverse record.
    source_a = make_state((0, 0, 0, 0), ((0, 0), (1, 2)))
    source_b = make_state((1, 1, 0, 0), ((0, 2),))
    target = make_state((0, 0, 0, 0), ((0, 1), (0, 2)))
    need(
        source_a != source_b
        and target in successors(source_a, "binary")
        and target in successors(source_b, "binary"),
        "binary allocation is not injective without history",
    )
    need(
        target in successors(cycle_first, "ternary")
        and target in successors(source_b, "ternary"),
        "ternary allocation is also not injective",
    )
    left = next(iter(resolve(State((2, 0, 0, 0)), "binary").terminals))
    right = next(iter(resolve(State((0, 2, 0, 0)), "binary").terminals))
    combined = State(
        tuple(a + b for a, b in zip(left.free, right.free, strict=True)),
        tuple(a + b for a, b in zip(left.bonds, right.bonds, strict=True)),
    )
    need(
        not successors(left, "binary")
        and not successors(right, "binary")
        and bool(successors(combined, "binary")),
        "disconnected compartments block an otherwise available repair",
    )
    need(
        combined.emission() == (2, 2, 0, 0),
        "local terminals do not implement the global complete histogram",
    )
    need(
        {state.emission() for state in resolve(State((2, 2, 0, 0)), "binary").terminals}
        == {(0, 0, 2, 2)},
        "global encounter stock would resolve the same inventory",
    )
    eager_ab = make_state((0, 0, 0, 0), ((0, 1),)).emission()
    eager_cd = make_state((0, 0, 0, 0), ((2, 3),)).emission()
    need(
        eager_ab == (0, 0, 1, 1) and eager_cd == (1, 1, 0, 0),
        "feeding outputs into the same layer cycles",
    )
    return {
        "unlike_only_binary_exchange": "equivariance forces a two-cycle",
        "different_predecessors_merge": True,
        "disconnected_component_emission": combined.emission(),
        "global_completed_emission": (0, 0, 2, 2),
        "same_layer_eager_cycle": [eager_cd, eager_ab, eager_cd],
        "scope": "compound encounter availability, completion barrier and inverse records remain supplied",
    }


def audit(limit: int = 8) -> dict[str, object]:
    result = {
        "ok": True,
        "exhaustive_even_census": census(limit),
        "S4_transition_checks": equivariance_controls(),
        "traps_and_hidden_pairings": trap_and_microstate_controls(),
        "lower_complexity_and_physical_controls": lower_complexity_and_physical_controls(),
        "boundary": "terminal histogram confluence under local compound rewrites, not a scheduler clock, reversible implementation, physical matching law or status upgrade",
    }
    return result


class PairResolverTests(unittest.TestCase):
    def test_every_small_maximal_schedule(self) -> None:
        self.assertEqual(census(8)["maximum_total_stock"], 8)

    def test_color_equivariance(self) -> None:
        self.assertGreater(equivariance_controls(), 0)

    def test_trap_and_microstates(self) -> None:
        self.assertEqual(
            trap_and_microstate_controls()["distinct_terminal_pair_sets_for_1111"], 3
        )

    def test_lower_complexity_and_boundary_controls(self) -> None:
        self.assertTrue(
            lower_complexity_and_physical_controls()["different_predecessors_merge"]
        )

    def test_invalid_population(self) -> None:
        with self.assertRaises(ValueError):
            State((-1, 0, 0, 0))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-stock", type=int, default=8)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = audit(args.max_stock)
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(
            "PASS: all small maximal ternary and binary-compound schedules reach exact majority residuals."
        )
        print(
            "PASS: equal reservations remove the naive trap; microscopic pairings need not agree."
        )
        print(
            "PASS: unlike-only binary cycle, spatial separation, irreversibility and layer-barrier controls."
        )
        print(result["boundary"])


if __name__ == "__main__":
    main()
