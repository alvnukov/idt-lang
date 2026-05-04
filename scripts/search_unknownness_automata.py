from __future__ import annotations

import argparse
import random
from collections.abc import Sequence
from typing import Literal

State = int
Triple = tuple[State, State, State]
Rule = tuple[State, ...]
ControlMode = Literal["u0", "inert-x", "erase-conflict"]

EMPTY = 0
PLUS = 1
MINUS = 2
RESIDUE = 3
STATE_NAMES = ("_", "+", "-", "X")
STATE_COUNT = 4
CONTROL_MODES: tuple[ControlMode, ...] = ("u0", "inert-x", "erase-conflict")


def flip_state(state: State) -> State:
    if state == PLUS:
        return MINUS
    if state == MINUS:
        return PLUS
    return state


def flip_triple(triple: Triple) -> Triple:
    left, center, right = triple
    return (flip_state(left), flip_state(center), flip_state(right))


def index_of(triple: Triple) -> int:
    left, center, right = triple
    return left * STATE_COUNT * STATE_COUNT + center * STATE_COUNT + right


def triple_of(index: int) -> Triple:
    left = index // (STATE_COUNT * STATE_COUNT)
    rest = index % (STATE_COUNT * STATE_COUNT)
    center = rest // STATE_COUNT
    right = rest % STATE_COUNT
    return (left, center, right)


def render_cells(cells: Sequence[State]) -> str:
    return "".join(STATE_NAMES[state] for state in cells)


def render_rule(rule: Rule) -> str:
    rows: list[str] = []
    for index, output in enumerate(rule):
        triple = triple_of(index)
        rows.append(f"{render_cells(triple)}->{STATE_NAMES[output]}")
    return " ".join(rows)


def rotate(cells: tuple[State, ...], offset: int) -> tuple[State, ...]:
    return cells[offset:] + cells[:offset]


def canonical_rotation(cells: tuple[State, ...]) -> tuple[State, ...]:
    return min(rotate(cells, offset) for offset in range(len(cells)))


def set_equivariant(table: list[State | None], triple: Triple, output: State) -> None:
    index = index_of(triple)
    flipped_index = index_of(flip_triple(triple))
    existing = table[index]
    if existing is not None and existing != output:
        raise ValueError(f"conflicting output for {triple}: {existing} vs {output}")
    flipped_output = flip_state(output)
    flipped_existing = table[flipped_index]
    if flipped_existing is not None and flipped_existing != flipped_output:
        raise ValueError(f"conflicting output for flipped {triple}: {flipped_existing} vs {flipped_output}")
    table[index] = output
    table[flipped_index] = flipped_output


def has_conflict(triple: Triple) -> bool:
    return PLUS in triple and MINUS in triple


def parse_control(value: str) -> ControlMode:
    if value == "u0":
        return "u0"
    if value == "inert-x":
        return "inert-x"
    if value == "erase-conflict":
        return "erase-conflict"
    raise ValueError(f"unknown control mode: {value}")


def inert_triple(triple: Triple) -> Triple:
    left, center, right = triple
    return (
        EMPTY if left == RESIDUE else left,
        EMPTY if center == RESIDUE else center,
        EMPTY if right == RESIDUE else right,
    )


def allowed_outputs(triple: Triple, control: ControlMode) -> tuple[State, ...]:
    if has_conflict(triple):
        if control == "erase-conflict":
            return (EMPTY,)
        return (RESIDUE,)
    has_plus = PLUS in triple
    has_minus = MINUS in triple
    if has_plus and not has_minus:
        return (EMPTY, PLUS, RESIDUE)
    if has_minus and not has_plus:
        return (EMPTY, MINUS, RESIDUE)
    return (EMPTY, RESIDUE)


def seeded_table(control: ControlMode) -> list[State | None]:
    table: list[State | None] = [None] * (STATE_COUNT**3)

    set_equivariant(table, (EMPTY, EMPTY, EMPTY), EMPTY)
    if control != "inert-x":
        set_equivariant(table, (RESIDUE, RESIDUE, RESIDUE), RESIDUE)

    set_equivariant(table, (PLUS, PLUS, PLUS), PLUS)
    set_equivariant(table, (EMPTY, PLUS, EMPTY), EMPTY)
    set_equivariant(table, (PLUS, EMPTY, PLUS), PLUS)

    if control != "inert-x":
        set_equivariant(table, (EMPTY, RESIDUE, EMPTY), EMPTY)
        set_equivariant(table, (RESIDUE, EMPTY, RESIDUE), RESIDUE)

    for left in range(STATE_COUNT):
        for center in range(STATE_COUNT):
            for right in range(STATE_COUNT):
                triple = (left, center, right)
                if has_conflict(triple):
                    set_equivariant(table, triple, EMPTY if control == "erase-conflict" else RESIDUE)

    return table


def random_rule(rng: random.Random, control: ControlMode) -> Rule:
    table = seeded_table(control)

    for index, value in enumerate(table):
        if value is not None:
            continue
        triple = triple_of(index)
        if control == "inert-x" and RESIDUE in triple:
            continue
        flipped = flip_triple(triple)
        flipped_index = index_of(flipped)
        if flipped_index < index:
            continue
        if flipped == triple:
            output = rng.choice((EMPTY, RESIDUE))
        else:
            output = rng.choice(allowed_outputs(triple, control))
        set_equivariant(table, triple, output)

    for index, value in enumerate(table):
        if value is not None:
            continue
        triple = triple_of(index)
        if control == "inert-x" and RESIDUE in triple:
            normalized = inert_triple(triple)
            normalized_value = table[index_of(normalized)]
            if normalized_value is None:
                raise ValueError(f"inert normalized triple {normalized} was not initialized")
            set_equivariant(table, triple, normalized_value)
            continue
        flipped = flip_triple(triple)
        flipped_index = index_of(flipped)
        if flipped_index < index:
            continue
        if flipped == triple:
            output = rng.choice((EMPTY, RESIDUE))
        else:
            output = rng.choice(allowed_outputs(triple, control))
        set_equivariant(table, triple, output)

    return tuple(state if state is not None else EMPTY for state in table)


def step(rule: Rule, cells: tuple[State, ...]) -> tuple[State, ...]:
    size = len(cells)
    next_cells: list[State] = []
    for index, center in enumerate(cells):
        left = cells[(index - 1) % size]
        right = cells[(index + 1) % size]
        next_cells.append(rule[index_of((left, center, right))])
    return tuple(next_cells)


def residue_affects_rule(rule: Rule) -> bool:
    for index, output in enumerate(rule):
        triple = triple_of(index)
        if RESIDUE not in triple:
            continue
        empty_triple = inert_triple(triple)
        if output != rule[index_of(empty_triple)]:
            return True
    return False


def inertized_rule(rule: Rule) -> Rule:
    table = list(rule)
    for index in range(len(table)):
        triple = triple_of(index)
        if RESIDUE in triple:
            table[index] = rule[index_of(inert_triple(triple))]
    return tuple(table)


def conflict_erased_rule(rule: Rule) -> Rule:
    table = list(rule)
    for index in range(len(table)):
        triple = triple_of(index)
        if has_conflict(triple):
            table[index] = EMPTY
    return tuple(table)


def audit_x_causality(rule: Rule, seeds: Sequence[tuple[State, ...]], steps: int) -> dict[str, int]:
    counts = {
        "x_created_from_conflict": 0,
        "x_created_from_nonconflict": 0,
        "x_participations": 0,
        "x_changed_output": 0,
        "x_to_record": 0,
        "x_blocks_record": 0,
        "x_redirects_record": 0,
    }
    for seed in seeds:
        cells = seed
        size = len(cells)
        for _time in range(steps):
            for index, center in enumerate(cells):
                triple = (cells[(index - 1) % size], center, cells[(index + 1) % size])
                output = rule[index_of(triple)]
                inert_output = rule[index_of(inert_triple(triple))]
                if output == RESIDUE and RESIDUE not in triple:
                    if has_conflict(triple):
                        counts["x_created_from_conflict"] += 1
                    else:
                        counts["x_created_from_nonconflict"] += 1
                if RESIDUE in triple:
                    counts["x_participations"] += 1
                    if output != inert_output:
                        counts["x_changed_output"] += 1
                    if output in {PLUS, MINUS}:
                        counts["x_to_record"] += 1
                    if inert_output in {PLUS, MINUS} and output not in {PLUS, MINUS}:
                        counts["x_blocks_record"] += 1
                    if output in {PLUS, MINUS} and output != inert_output:
                        counts["x_redirects_record"] += 1
            cells = step(rule, cells)
    return counts


def simulate(rule: Rule, seed: tuple[State, ...], steps: int, burn_in: int) -> tuple[str, bool]:
    cells = seed
    seen_raw: dict[tuple[State, ...], int] = {}
    seen_canonical: dict[tuple[State, ...], tuple[int, tuple[State, ...]]] = {}
    residue_seen = RESIDUE in cells

    for time in range(steps + 1):
        if RESIDUE in cells:
            residue_seen = True
        if time >= burn_in:
            if all(state == EMPTY for state in cells):
                return ("dead", residue_seen)
            previous = seen_raw.get(cells)
            if previous is not None:
                period = time - previous
                return ("frozen" if period == 1 else "periodic", residue_seen)
            seen_raw[cells] = time

            canonical = canonical_rotation(cells)
            previous_canonical = seen_canonical.get(canonical)
            if previous_canonical is not None:
                _, previous_cells = previous_canonical
                if previous_cells != cells:
                    return ("moving", residue_seen)
            seen_canonical[canonical] = (time, cells)

        cells = step(rule, cells)

    return ("chaotic", residue_seen)


def build_seeds(size: int, rng: random.Random, random_seed_count: int) -> list[tuple[State, ...]]:
    seeds: list[tuple[State, ...]] = []
    seeds.append(tuple([EMPTY] * size))
    seeds.append(tuple([PLUS] * size))

    single = [EMPTY] * size
    single[size // 2] = PLUS
    seeds.append(tuple(single))

    gap = [EMPTY] * size
    gap[size // 2 - 1] = PLUS
    gap[size // 2 + 1] = PLUS
    seeds.append(tuple(gap))

    conflict = [EMPTY] * size
    conflict[size // 2 - 1] = PLUS
    conflict[size // 2 + 1] = MINUS
    seeds.append(tuple(conflict))

    residue = [EMPTY] * size
    residue[size // 2] = RESIDUE
    seeds.append(tuple(residue))

    for _ in range(random_seed_count):
        cells = []
        for _index in range(size):
            roll = rng.random()
            if roll < 0.70:
                cells.append(EMPTY)
            elif roll < 0.82:
                cells.append(PLUS)
            elif roll < 0.94:
                cells.append(MINUS)
            else:
                cells.append(RESIDUE)
        seeds.append(tuple(cells))
    return seeds


def active_count(counts: dict[str, int]) -> int:
    return counts["periodic"] + counts["moving"]


def score_rule(
    rule: Rule,
    seeds: Sequence[tuple[State, ...]],
    steps: int,
    burn_in: int,
    residue_critical: bool,
) -> tuple[int, dict[str, int]]:
    counts = {"dead": 0, "frozen": 0, "periodic": 0, "moving": 0, "chaotic": 0, "residue_seen": 0}
    for seed in seeds:
        label, residue_seen = simulate(rule, seed, steps, burn_in)
        counts[label] += 1
        if residue_seen:
            counts["residue_seen"] += 1

    active = active_count(counts)
    boring = counts["dead"] + counts["frozen"]
    score = 0
    score += 4 if residue_affects_rule(rule) else -8
    score += 5 if counts["dead"] > 0 else -3
    score += 5 if counts["frozen"] > 0 else -3
    score += 8 if active > 0 else -8
    score += 5 if counts["moving"] > 0 else 0
    score += 3 if counts["chaotic"] > 0 else 0
    score -= 5 if active == len(seeds) else 0
    score -= 5 if boring == len(seeds) else 0
    score += counts["residue_seen"]
    if residue_critical:
        _, inert_counts = score_rule(inertized_rule(rule), seeds, steps, burn_in, residue_critical=False)
        active_delta = active - active_count(inert_counts)
        score += max(active_delta, 0) * 4
        if active > 0 and active_delta <= 0:
            score -= 10
    return score, counts


def search(
    samples: int,
    size: int,
    steps: int,
    burn_in: int,
    seed: int,
    keep: int,
    control: ControlMode,
    residue_critical: bool,
) -> list[tuple[int, Rule, dict[str, int]]]:
    rng = random.Random(seed)
    seeds = build_seeds(size, rng, random_seed_count=10)
    best: list[tuple[int, Rule, dict[str, int]]] = []

    for _ in range(samples):
        rule = random_rule(rng, control)
        score, counts = score_rule(rule, seeds, steps, burn_in, residue_critical=residue_critical)
        if len(best) < keep or score > best[-1][0]:
            best.append((score, rule, counts))
            best.sort(key=lambda item: item[0], reverse=True)
            del best[keep:]
    return best


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Search small U0 unknownness automata.")
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--size", type=int, default=48)
    parser.add_argument("--steps", type=int, default=160)
    parser.add_argument("--burn-in", type=int, default=20)
    parser.add_argument("--seed", type=int, default=174)
    parser.add_argument("--keep", type=int, default=5)
    parser.add_argument("--control", choices=CONTROL_MODES, default="u0")
    parser.add_argument("--compare-controls", action="store_true")
    parser.add_argument("--paired-controls", action="store_true")
    parser.add_argument("--residue-critical", action="store_true")
    parser.add_argument("--audit-x", action="store_true")
    parser.add_argument("--show-rule", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    controls = CONTROL_MODES if args.compare_controls else (parse_control(str(args.control)),)
    for control in controls:
        best = search(
            samples=args.samples,
            size=args.size,
            steps=args.steps,
            burn_in=args.burn_in,
            seed=args.seed,
            keep=args.keep,
            control=control,
            residue_critical=bool(args.residue_critical and control == "u0"),
        )
        audit_seeds = build_seeds(args.size, random.Random(args.seed), random_seed_count=10)
        for rank, (score, rule, counts) in enumerate(best, start=1):
            print(
                f"control={control} rank={rank} score={score} counts={counts} "
                f"residue_affects={residue_affects_rule(rule)}"
            )
            if args.paired_controls and control == "u0":
                paired_rules = (
                    ("paired-inert-x", inertized_rule(rule)),
                    ("paired-erase-conflict", conflict_erased_rule(rule)),
                )
                for label, paired_rule in paired_rules:
                    paired_score, paired_counts = score_rule(
                        paired_rule,
                        audit_seeds,
                        args.steps,
                        args.burn_in,
                        residue_critical=False,
                    )
                    print(
                        f"control={label} source_rank={rank} score={paired_score} "
                        f"counts={paired_counts} residue_affects={residue_affects_rule(paired_rule)}"
                    )
            if args.audit_x:
                print(f"x_audit={audit_x_causality(rule, audit_seeds, args.steps)}")
            if args.show_rule:
                print(render_rule(rule))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
