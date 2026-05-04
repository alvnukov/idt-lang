from __future__ import annotations

import argparse
import itertools
import json
import random
from collections.abc import Sequence
from dataclasses import asdict, dataclass
from typing import Literal

State = int
Cells = tuple[State, ...]
Verdict = Literal["VALID_HIT", "IMPORTED_HIT", "NEAR_MISS", "KILL"]
TestVerdict = Literal["PASS", "FAIL"]
ContextKind = Literal["identity", "swap", "oriented_swap"]
ReadoutKind = Literal["residue", "barrier_residue", "oriented_residue"]
PairReadoutKind = Literal["local", "pr_parity"]

EMPTY = 0
PLUS = 1
MINUS = 2
X_PLUS = 3
X_MINUS = 4
STATES: tuple[State, ...] = (EMPTY, PLUS, MINUS, X_PLUS, X_MINUS)
STATE_NAMES = ("_", "+", "-", "Xp", "Xm")


@dataclass(frozen=True)
class TwoLayerSchema:
    name: str
    context: ContextKind
    readout: ReadoutKind
    pair_readout: PairReadoutKind
    imports: tuple[str, ...]
    description: str


@dataclass(frozen=True)
class TestResult:
    name: str
    verdict: TestVerdict
    reason: str
    details: dict[str, int | float | str | bool]


@dataclass(frozen=True)
class SchemaResult:
    schema: str
    verdict: Verdict
    passed: int
    failed: int
    imports: tuple[str, ...]
    tests: list[TestResult]
    description: str


SCHEMAS: tuple[TwoLayerSchema, ...] = (
    TwoLayerSchema(
        name="identity_residue_baseline",
        context="identity",
        readout="residue",
        pair_readout="local",
        imports=(),
        description="negative control: irreversible residue readout with no noncommuting context layer",
    ),
    TwoLayerSchema(
        name="local_swap_residue",
        context="swap",
        readout="residue",
        pair_readout="local",
        imports=(),
        description="reversible local context swaps followed by residue/readout stabilization",
    ),
    TwoLayerSchema(
        name="oriented_swap_residue",
        context="oriented_swap",
        readout="oriented_residue",
        pair_readout="local",
        imports=(),
        description="reversible local swaps with orientation-carrying residue",
    ),
    TwoLayerSchema(
        name="barrier_sensitive_residue",
        context="swap",
        readout="barrier_residue",
        pair_readout="local",
        imports=(),
        description="local context swaps with records acting as compatibility bottlenecks",
    ),
    TwoLayerSchema(
        name="imported_pr_parity_residue",
        context="swap",
        readout="residue",
        pair_readout="pr_parity",
        imports=("bell_parity_readout",),
        description="control: Bell-strength is inserted as a PR-like parity readout",
    ),
    TwoLayerSchema(
        name="imported_pr_parity_metric",
        context="swap",
        readout="barrier_residue",
        pair_readout="pr_parity",
        imports=("bell_parity_readout",),
        description="control: PR-like parity readout plus local metric bottleneck",
    ),
)


def flip_residue(state: State) -> State:
    if state == X_PLUS:
        return X_MINUS
    if state == X_MINUS:
        return X_PLUS
    return state


def render(cells: Sequence[State]) -> str:
    return " ".join(STATE_NAMES[state] for state in cells)


def context_step(schema: TwoLayerSchema, cells: Cells, setting: int) -> Cells:
    if schema.context == "identity":
        return cells
    output = list(cells)
    size = len(cells)
    start = setting % 2
    for index in range(start, size - 1, 2):
        output[index], output[index + 1] = output[index + 1], output[index]
    if schema.context == "oriented_swap":
        output = [flip_residue(state) if state in (X_PLUS, X_MINUS) else state for state in output]
    return tuple(output)


def context_region(schema: TwoLayerSchema, cells: Cells, center: int, radius: int, setting: int) -> Cells:
    if schema.context == "identity":
        return cells
    output = list(cells)
    size = len(cells)
    indices = list(range(center - radius, center + radius + 1))
    for raw_index in indices:
        index = raw_index % size
        next_index = (raw_index + 1) % size
        if raw_index % 2 != setting % 2:
            continue
        if next_index not in {value % size for value in indices}:
            continue
        output[index], output[next_index] = output[next_index], output[index]
    if schema.context == "oriented_swap":
        for raw_index in indices:
            index = raw_index % size
            output[index] = flip_residue(output[index])
    return tuple(output)


def has_conflict(triple: Sequence[State]) -> bool:
    return PLUS in triple and MINUS in triple


def majority_record(triple: Sequence[State]) -> State:
    plus_count = triple.count(PLUS)
    minus_count = triple.count(MINUS)
    if plus_count > minus_count:
        return PLUS
    if minus_count > plus_count:
        return MINUS
    return EMPTY


def residue_count(triple: Sequence[State]) -> int:
    return triple.count(X_PLUS) + triple.count(X_MINUS)


def readout_cell(schema: TwoLayerSchema, triple: Sequence[State]) -> State:
    center = triple[1]
    if has_conflict(triple):
        return X_PLUS
    if schema.readout == "barrier_residue" and center in (PLUS, MINUS):
        return center
    if schema.readout == "barrier_residue" and residue_count(triple) > 0 and (PLUS in triple or MINUS in triple):
        return EMPTY if center in (EMPTY, X_PLUS, X_MINUS) else center
    if schema.readout == "oriented_residue":
        if X_PLUS in triple and X_MINUS in triple:
            return EMPTY
        if X_PLUS in triple:
            return X_PLUS
        if X_MINUS in triple:
            return X_MINUS
    else:
        if residue_count(triple) > 0:
            return X_PLUS
    if center in (PLUS, MINUS):
        return center
    record = majority_record(triple)
    if record != EMPTY and triple[0] == triple[2]:
        return record
    return EMPTY


def readout_step(schema: TwoLayerSchema, cells: Cells) -> Cells:
    size = len(cells)
    output: list[State] = []
    for index in range(size):
        triple = (cells[(index - 1) % size], cells[index], cells[(index + 1) % size])
        output.append(readout_cell(schema, triple))
    return tuple(output)


def full_step(schema: TwoLayerSchema, cells: Cells, setting: int) -> Cells:
    return readout_step(schema, context_step(schema, cells, setting))


def context_readout_split_test(schema: TwoLayerSchema) -> TestResult:
    size = 5
    witness_found = False
    for setting in (0, 1):
        seen: dict[Cells, Cells] = {}
        for values in itertools.product(STATES, repeat=size):
            cells = tuple(values)
            output = context_step(schema, cells, setting)
            previous = seen.get(output)
            if previous is not None and previous != cells:
                return TestResult(
                    name="reversible_readout_split",
                    verdict="FAIL",
                    reason="context step is not injective",
                    details={"setting": setting, "ring_size": size},
                )
            seen[output] = cells
    for values in itertools.product(STATES, repeat=size):
        cells = tuple(values)
        if context_step(schema, context_step(schema, cells, 0), 1) != context_step(schema, context_step(schema, cells, 1), 0):
            witness_found = True
            break
    if not witness_found:
        return TestResult(
            name="reversible_readout_split",
            verdict="FAIL",
            reason="context settings commute; no context-order witness exists",
            details={"ring_size": size},
        )
    readout_seen: dict[Cells, Cells] = {}
    for values in itertools.product(STATES, repeat=size):
        cells = tuple(values)
        output = readout_step(schema, cells)
        previous = readout_seen.get(output)
        if previous is not None and previous != cells:
            return TestResult(
                name="reversible_readout_split",
                verdict="PASS",
                reason="context is reversible/noncommuting and readout is irreversible",
                details={"ring_size": size, "checked_states": len(readout_seen)},
            )
        readout_seen[output] = cells
    return TestResult(
        name="reversible_readout_split",
        verdict="FAIL",
        reason="readout did not collapse any checked states",
        details={"ring_size": size},
    )


def random_background(size: int, rng: random.Random) -> list[State]:
    cells: list[State] = []
    for _index in range(size):
        roll = rng.random()
        if roll < 0.78:
            cells.append(EMPTY)
        elif roll < 0.86:
            cells.append(PLUS)
        elif roll < 0.94:
            cells.append(MINUS)
        elif roll < 0.97:
            cells.append(X_PLUS)
        else:
            cells.append(X_MINUS)
    return cells


def local_window(center: int, radius: int) -> tuple[int, ...]:
    return tuple(range(center - radius, center + radius + 1))


def local_counts(cells: Cells, center: int, radius: int) -> tuple[int, int, int]:
    plus = minus = residue = 0
    size = len(cells)
    for raw_index in local_window(center, radius):
        state = cells[raw_index % size]
        if state == PLUS:
            plus += 1
        elif state == MINUS:
            minus += 1
        elif state in (X_PLUS, X_MINUS):
            residue += 1
    return plus, minus, residue


def outcome_from_cells(cells: Cells, center: int, radius: int) -> int:
    plus, minus, residue = local_counts(cells, center, radius)
    if plus > minus:
        return 1
    if minus > plus:
        return -1
    return 1 if residue % 2 == 0 else -1


def hidden_bit(cells: Cells) -> int:
    total = sum(1 for state in cells if state in (PLUS, X_PLUS))
    return 1 if total % 2 == 0 else -1


def pair_outcomes(schema: TwoLayerSchema, cells: Cells, left_setting: int, right_setting: int) -> tuple[int, int]:
    if schema.pair_readout == "pr_parity":
        left = hidden_bit(cells)
        right = left
        if left_setting == 1 and right_setting == 1:
            right = -right
        return left, right
    size = len(cells)
    left_center = size // 4
    right_center = (3 * size) // 4
    evolved = context_region(schema, cells, left_center, radius=6, setting=left_setting)
    evolved = context_region(schema, evolved, right_center, radius=6, setting=right_setting)
    for time in range(6):
        evolved = full_step(schema, evolved, time % 2)
    return outcome_from_cells(evolved, left_center, 5), outcome_from_cells(evolved, right_center, 5)


def no_signalling_test(schema: TwoLayerSchema, seed: int) -> TestResult:
    rng = random.Random(seed)
    trials = 128
    mismatches = 0
    for _trial in range(trials):
        base = tuple(random_background(96, rng))
        for left_setting in (0, 1):
            left_a, _ = pair_outcomes(schema, base, left_setting, 0)
            left_b, _ = pair_outcomes(schema, base, left_setting, 1)
            if left_a != left_b:
                mismatches += 1
    if mismatches == 0:
        return TestResult(
            name="explicit_no_signalling",
            verdict="PASS",
            reason="remote setting did not change local outcome on paired hidden samples",
            details={"trials": trials, "mismatches": mismatches},
        )
    return TestResult(
        name="explicit_no_signalling",
        verdict="FAIL",
        reason="remote setting changed local outcome on paired hidden samples",
        details={"trials": trials, "mismatches": mismatches},
    )


def bell_strength_test(schema: TwoLayerSchema, seed: int) -> TestResult:
    rng = random.Random(seed)
    trials = 256
    sums: dict[tuple[int, int], int] = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for _trial in range(trials):
        base = tuple(random_background(96, rng))
        for settings in sums:
            left, right = pair_outcomes(schema, base, settings[0], settings[1])
            sums[settings] += left * right
    e00 = sums[(0, 0)] / trials
    e01 = sums[(0, 1)] / trials
    e10 = sums[(1, 0)] / trials
    e11 = sums[(1, 1)] / trials
    chsh = e00 + e01 + e10 - e11
    if abs(chsh) > 2.05:
        return TestResult(
            name="bell_strength",
            verdict="PASS",
            reason="CHSH-like screen exceeds the local deterministic bound",
            details={"chsh": round(chsh, 6), "e00": e00, "e01": e01, "e10": e10, "e11": e11},
        )
    return TestResult(
        name="bell_strength",
        verdict="FAIL",
        reason="CHSH-like screen remains local/shared-cause compatible",
        details={"chsh": round(chsh, 6), "e00": e00, "e01": e01, "e10": e10, "e11": e11},
    )


def block_state(block: Sequence[State]) -> State:
    if X_PLUS in block or X_MINUS in block:
        return X_PLUS
    has_plus = PLUS in block
    has_minus = MINUS in block
    if has_plus and has_minus:
        return X_PLUS
    if has_plus:
        return PLUS
    if has_minus:
        return MINUS
    return EMPTY


def coarse_grain(cells: Cells, block_size: int) -> Cells:
    return tuple(block_state(cells[index : index + block_size]) for index in range(0, len(cells), block_size))


def coarse_graining_test(schema: TwoLayerSchema, seed: int) -> TestResult:
    rng = random.Random(seed)
    records = residues = empty = 0
    observations = 0
    for _sample in range(16):
        cells = tuple(random_background(48, rng))
        for time in range(12):
            coarse = coarse_grain(cells, 4)
            records += sum(1 for state in coarse if state in (PLUS, MINUS))
            residues += sum(1 for state in coarse if state in (X_PLUS, X_MINUS))
            empty += sum(1 for state in coarse if state == EMPTY)
            observations += len(coarse)
            cells = full_step(schema, cells, time % 2)
    non_empty = records + residues
    if records > 0 and residues > 0 and non_empty > 0:
        ratio = residues / non_empty
        if 0.05 <= ratio <= 0.95:
            return TestResult(
                name="coarse_graining",
                verdict="PASS",
                reason="coarse blocks preserve both records and residue",
                details={"records": records, "residues": residues, "empty": empty, "observations": observations, "residue_ratio": round(ratio, 6)},
            )
    return TestResult(
        name="coarse_graining",
        verdict="FAIL",
        reason="coarse blocks collapse record/residue distinction",
        details={"records": records, "residues": residues, "empty": empty, "observations": observations},
    )


def domain_seed(size: int, center: int) -> Cells:
    cells = [EMPTY] * size
    cells[center - 2] = PLUS
    cells[center + 2] = MINUS
    return tuple(cells)


def merged_seed(size: int, centers: Sequence[int]) -> Cells:
    cells = [EMPTY] * size
    for center in centers:
        cells[center - 2] = PLUS
        cells[center + 2] = MINUS
    return tuple(cells)


def window(cells: Cells, center: int, radius: int) -> Cells:
    size = len(cells)
    return tuple(cells[index % size] for index in local_window(center, radius))


def compositionality_test(schema: TwoLayerSchema) -> TestResult:
    size = 96
    left_center = 24
    right_center = 72
    left = domain_seed(size, left_center)
    right = domain_seed(size, right_center)
    both = merged_seed(size, (left_center, right_center))
    mismatches = 0
    max_steps = 12
    for time in range(max_steps + 1):
        if window(left, left_center, 8) != window(both, left_center, 8):
            mismatches += 1
        if window(right, right_center, 8) != window(both, right_center, 8):
            mismatches += 1
        left = full_step(schema, left, time % 2)
        right = full_step(schema, right, time % 2)
        both = full_step(schema, both, time % 2)
    if mismatches == 0:
        return TestResult(
            name="compositionality",
            verdict="PASS",
            reason="separated domains compose before light-cone overlap",
            details={"max_steps": max_steps, "mismatches": mismatches},
        )
    return TestResult(
        name="compositionality",
        verdict="FAIL",
        reason="separated domains cross-talk before light-cone overlap",
        details={"max_steps": max_steps, "mismatches": mismatches},
    )


def first_residue_arrival(schema: TwoLayerSchema, source: int, target: int, barrier: bool) -> int:
    size = 80
    cells = [EMPTY] * size
    cells[source] = PLUS
    cells[source + 2] = MINUS
    if barrier:
        midpoint = (source + target) // 2
        for index in range(midpoint - 2, midpoint + 3):
            cells[index % size] = PLUS
    current = tuple(cells)
    for time in range(size + 1):
        if current[target % size] in (X_PLUS, X_MINUS):
            return time
        current = full_step(schema, current, time % 2)
    return -1


def metric_extraction_test(schema: TwoLayerSchema) -> TestResult:
    forward = first_residue_arrival(schema, 10, 42, barrier=False)
    backward = first_residue_arrival(schema, 42, 10, barrier=False)
    blocked = first_residue_arrival(schema, 10, 42, barrier=True)
    symmetric = forward > 0 and abs(forward - backward) <= 1
    bottleneck = blocked == -1 or (forward > 0 and blocked > forward + 2)
    if symmetric and bottleneck:
        return TestResult(
            name="metric_extraction",
            verdict="PASS",
            reason="residue travel time is symmetric and compatibility bottleneck-sensitive",
            details={"forward": forward, "backward": backward, "blocked": blocked},
        )
    return TestResult(
        name="metric_extraction",
        verdict="FAIL",
        reason="metric screen recovers only lattice propagation or no stable distance-like quantity",
        details={"forward": forward, "backward": backward, "blocked": blocked},
    )


def evaluate_schema(schema: TwoLayerSchema, seed: int) -> SchemaResult:
    tests = [
        context_readout_split_test(schema),
        no_signalling_test(schema, seed),
        coarse_graining_test(schema, seed),
        compositionality_test(schema),
        bell_strength_test(schema, seed),
        metric_extraction_test(schema),
    ]
    passed = sum(1 for test in tests if test.verdict == "PASS")
    failed = len(tests) - passed
    if passed == len(tests) and not schema.imports:
        verdict: Verdict = "VALID_HIT"
    elif passed == len(tests):
        verdict = "IMPORTED_HIT"
    elif passed >= 4:
        verdict = "NEAR_MISS"
    else:
        verdict = "KILL"
    return SchemaResult(
        schema=schema.name,
        verdict=verdict,
        passed=passed,
        failed=failed,
        imports=schema.imports,
        tests=tests,
        description=schema.description,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate two-layer context/readout schema hypothesis in one pass.")
    parser.add_argument("--seed", type=int, default=174)
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    results = [evaluate_schema(schema, int(args.seed)) for schema in SCHEMAS]
    results.sort(key=lambda result: (result.verdict == "VALID_HIT", result.verdict == "IMPORTED_HIT", result.passed), reverse=True)
    for result in results:
        imported = ",".join(result.imports) if result.imports else "-"
        print(f"verdict={result.verdict} schema={result.schema} passed={result.passed}/6 imports={imported}")
        for test in result.tests:
            print(f"  {test.verdict} {test.name}: {test.reason} details={test.details}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
