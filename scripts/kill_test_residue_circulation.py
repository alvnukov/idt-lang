from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
from collections.abc import Iterable, Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.evaluate_unknownness_schemas import make_rule, residue_circulation  # noqa: E402
from scripts.search_unknownness_automata import (  # noqa: E402
    EMPTY,
    MINUS,
    PLUS,
    RESIDUE,
    Rule,
    State,
    build_seeds,
    index_of,
    step,
)

KillVerdict = Literal["SURVIVED", "KILLED"]
DetailsValue = str | int | float | bool
Cells = tuple[State, ...]


@dataclass(frozen=True)
class KillTestResult:
    name: str
    verdict: KillVerdict
    reason: str
    details: dict[str, DetailsValue]


def candidate_rule() -> Rule:
    return make_rule(residue_circulation, 1)


def window_indices(size: int, center: int, radius: int) -> tuple[int, ...]:
    return tuple((center + offset) % size for offset in range(-radius, radius + 1))


def apply_window_context(rule: Rule, cells: Cells, center: int, radius: int, parity: int) -> Cells:
    size = len(cells)
    output = list(cells)
    allowed = set(window_indices(size, center, radius))
    for index in allowed:
        if index % 2 != parity:
            continue
        left = cells[(index - 1) % size]
        right = cells[(index + 1) % size]
        output[index] = rule[index_of((left, cells[index], right))]
    return tuple(output)


def run_steps(rule: Rule, cells: Cells, count: int) -> Cells:
    for _ in range(count):
        cells = step(rule, cells)
    return cells


def local_record_marginal(cells: Cells, center: int, radius: int) -> tuple[int, int, int]:
    plus = 0
    minus = 0
    residue = 0
    for index in window_indices(len(cells), center, radius):
        if cells[index] == PLUS:
            plus += 1
        elif cells[index] == MINUS:
            minus += 1
        elif cells[index] == RESIDUE:
            residue += 1
    return plus, minus, residue


def random_background(size: int, rng: random.Random) -> list[State]:
    cells: list[State] = [EMPTY] * size
    for index in range(size):
        roll = rng.random()
        if roll < 0.84:
            cells[index] = EMPTY
        elif roll < 0.90:
            cells[index] = PLUS
        elif roll < 0.96:
            cells[index] = MINUS
        else:
            cells[index] = RESIDUE
    return cells


def no_signalling_test(rule: Rule, seed: int) -> KillTestResult:
    rng = random.Random(seed)
    size = 80
    left_center = 18
    right_center = 58
    mismatches = 0
    trials = 64
    for _trial in range(trials):
        cells = random_background(size, rng)
        cells[left_center - 1] = PLUS
        cells[left_center + 1] = MINUS
        cells[right_center - 1] = PLUS
        cells[right_center + 1] = MINUS
        base = tuple(cells)

        local_first = apply_window_context(rule, base, left_center, radius=4, parity=0)
        remote_a = apply_window_context(rule, local_first, right_center, radius=4, parity=0)
        remote_b = apply_window_context(rule, local_first, right_center, radius=4, parity=1)
        readout_a = run_steps(rule, remote_a, count=8)
        readout_b = run_steps(rule, remote_b, count=8)
        if local_record_marginal(readout_a, left_center, radius=5) != local_record_marginal(readout_b, left_center, radius=5):
            mismatches += 1

    if mismatches == 0:
        return KillTestResult(
            name="explicit_no_signalling",
            verdict="SURVIVED",
            reason="remote context choice did not change local record marginals before the light-cone boundary",
            details={"trials": trials, "mismatches": mismatches, "readout_steps": 8},
        )
    return KillTestResult(
        name="explicit_no_signalling",
        verdict="KILLED",
        reason="remote context choice changed local record marginals inside the no-signalling window",
        details={"trials": trials, "mismatches": mismatches, "readout_steps": 8},
    )


def block_state(block: Sequence[State]) -> State:
    if RESIDUE in block:
        return RESIDUE
    has_plus = PLUS in block
    has_minus = MINUS in block
    if has_plus and has_minus:
        return RESIDUE
    if has_plus:
        return PLUS
    if has_minus:
        return MINUS
    return EMPTY


def coarse_grain(cells: Cells, block_size: int) -> Cells:
    return tuple(block_state(cells[index : index + block_size]) for index in range(0, len(cells), block_size))


def coarse_graining_test(rule: Rule, seed: int) -> KillTestResult:
    rng = random.Random(seed)
    seeds = build_seeds(48, rng, random_seed_count=8)
    record_blocks = 0
    residue_blocks = 0
    empty_blocks = 0
    observations = 0
    for seed_cells in seeds:
        cells = seed_cells
        for _time in range(24):
            for block_size in (2, 4):
                coarse = coarse_grain(cells, block_size)
                record_blocks += sum(1 for state in coarse if state in (PLUS, MINUS))
                residue_blocks += sum(1 for state in coarse if state == RESIDUE)
                empty_blocks += sum(1 for state in coarse if state == EMPTY)
                observations += len(coarse)
            cells = step(rule, cells)

    non_empty = record_blocks + residue_blocks
    if non_empty > 0 and record_blocks > 0 and residue_blocks > 0:
        residue_ratio = residue_blocks / non_empty
        if 0.05 <= residue_ratio <= 0.95:
            return KillTestResult(
                name="coarse_graining",
                verdict="SURVIVED",
                reason="block summaries preserve both record and residue classes without immediate collapse",
                details={
                    "record_blocks": record_blocks,
                    "residue_blocks": residue_blocks,
                    "empty_blocks": empty_blocks,
                    "observations": observations,
                    "residue_ratio": round(residue_ratio, 6),
                },
            )
    return KillTestResult(
        name="coarse_graining",
        verdict="KILLED",
        reason="coarse-graining collapses the record/residue distinction",
        details={
            "record_blocks": record_blocks,
            "residue_blocks": residue_blocks,
            "empty_blocks": empty_blocks,
            "observations": observations,
        },
    )


def domain_seed(size: int, center: int) -> Cells:
    cells = [EMPTY] * size
    cells[center - 1] = PLUS
    cells[center + 1] = MINUS
    return tuple(cells)


def merge_domains(size: int, centers: Iterable[int]) -> Cells:
    cells = [EMPTY] * size
    for center in centers:
        cells[center - 1] = PLUS
        cells[center + 1] = MINUS
    return tuple(cells)


def window(cells: Cells, center: int, radius: int) -> Cells:
    return tuple(cells[index] for index in window_indices(len(cells), center, radius))


def compositionality_test(rule: Rule) -> KillTestResult:
    size = 96
    left_center = 24
    right_center = 72
    left_only = domain_seed(size, left_center)
    right_only = domain_seed(size, right_center)
    combined = merge_domains(size, (left_center, right_center))
    max_steps = 16
    mismatches = 0
    for _time in range(max_steps + 1):
        if window(combined, left_center, 8) != window(left_only, left_center, 8):
            mismatches += 1
        if window(combined, right_center, 8) != window(right_only, right_center, 8):
            mismatches += 1
        left_only = step(rule, left_only)
        right_only = step(rule, right_only)
        combined = step(rule, combined)

    if mismatches == 0:
        return KillTestResult(
            name="compositionality",
            verdict="SURVIVED",
            reason="separated residue domains compose independently before light-cone overlap",
            details={"max_steps": max_steps, "mismatches": mismatches, "separation": right_center - left_center},
        )
    return KillTestResult(
        name="compositionality",
        verdict="KILLED",
        reason="separated residue domains influence each other before light-cone overlap",
        details={"max_steps": max_steps, "mismatches": mismatches, "separation": right_center - left_center},
    )


def reversible_readout_split_test(rule: Rule) -> KillTestResult:
    size = 6
    seen: dict[Cells, Cells] = {}
    for values in itertools.product((EMPTY, PLUS, MINUS, RESIDUE), repeat=size):
        cells = tuple(values)
        output = step(rule, cells)
        previous = seen.get(output)
        if previous is not None and previous != cells:
            return KillTestResult(
                name="reversible_readout_split",
                verdict="KILLED",
                reason="one-step context map is many-to-one, so no reversible pre-readout phase is represented",
                details={
                    "ring_size": size,
                    "collision_a": "".join(str(state) for state in previous),
                    "collision_b": "".join(str(state) for state in cells),
                    "shared_output": "".join(str(state) for state in output),
                },
            )
        seen[output] = cells
    return KillTestResult(
        name="reversible_readout_split",
        verdict="SURVIVED",
        reason="finite global map was injective on the checked ring",
        details={"ring_size": size, "states_checked": len(seen)},
    )


def local_outcome(cells: Cells, center: int, radius: int) -> int:
    plus, minus, residue = local_record_marginal(cells, center, radius)
    if plus > minus:
        return 1
    if minus > plus:
        return -1
    return 1 if residue % 2 == 0 else -1


def chsh_correlations(rule: Rule, seed: int) -> tuple[float, dict[str, float]]:
    rng = random.Random(seed)
    size = 96
    left_center = 24
    right_center = 72
    trials = 256
    sums: dict[tuple[int, int], int] = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for _trial in range(trials):
        base = random_background(size, rng)
        base[left_center - 2] = PLUS
        base[left_center + 2] = MINUS
        base[right_center - 2] = MINUS
        base[right_center + 2] = PLUS
        base_cells = tuple(base)
        for left_setting, right_setting in sums:
            cells = apply_window_context(rule, base_cells, left_center, radius=5, parity=left_setting)
            cells = apply_window_context(rule, cells, right_center, radius=5, parity=right_setting)
            cells = run_steps(rule, cells, count=6)
            sums[(left_setting, right_setting)] += local_outcome(cells, left_center, 4) * local_outcome(cells, right_center, 4)
    correlations = {f"e{left}{right}": value / trials for (left, right), value in sums.items()}
    chsh = correlations["e00"] + correlations["e01"] + correlations["e10"] - correlations["e11"]
    return chsh, correlations


def bell_strength_test(rule: Rule, seed: int) -> KillTestResult:
    chsh, correlations = chsh_correlations(rule, seed)
    if abs(chsh) > 2.05:
        return KillTestResult(
            name="bell_strength",
            verdict="SURVIVED",
            reason="CHSH-like screen exceeded the local deterministic bound on the sampled setting grid",
            details={"chsh": round(chsh, 6), **correlations},
        )
    return KillTestResult(
        name="bell_strength",
        verdict="KILLED",
        reason="correlations remain compatible with a local deterministic/shared-cause model on the CHSH-like screen",
        details={"chsh": round(chsh, 6), **correlations},
    )


def first_residue_arrival(rule: Rule, size: int, source: int, target: int, barrier: bool) -> int:
    cells = [EMPTY] * size
    cells[source] = PLUS
    cells[(source + 1) % size] = MINUS
    if barrier:
        start = (source + target) // 2 - 2
        for index in range(start, start + 5):
            cells[index % size] = PLUS
    current = tuple(cells)
    for time in range(size + 1):
        if current[target % size] == RESIDUE:
            return time
        current = step(rule, current)
    return -1


def metric_extraction_test(rule: Rule) -> KillTestResult:
    size = 80
    source = 10
    target = 42
    forward = first_residue_arrival(rule, size, source, target, barrier=False)
    backward = first_residue_arrival(rule, size, target, source, barrier=False)
    blocked = first_residue_arrival(rule, size, source, target, barrier=True)
    symmetric = forward == backward and forward > 0
    bottleneck_sensitive = blocked > 0 and abs(blocked - forward) >= 2
    if symmetric and bottleneck_sensitive:
        return KillTestResult(
            name="metric_extraction",
            verdict="SURVIVED",
            reason="residue travel time is symmetric and responds to a compatibility bottleneck",
            details={"forward": forward, "backward": backward, "blocked": blocked},
        )
    return KillTestResult(
        name="metric_extraction",
        verdict="KILLED",
        reason="only lattice propagation was recovered; compatibility bottleneck did not define a distinct distance-like quantity",
        details={"forward": forward, "backward": backward, "blocked": blocked},
    )


def run_kill_tests(seed: int) -> list[KillTestResult]:
    rule = candidate_rule()
    return [
        no_signalling_test(rule, seed),
        coarse_graining_test(rule, seed),
        compositionality_test(rule),
        reversible_readout_split_test(rule),
        bell_strength_test(rule, seed),
        metric_extraction_test(rule),
    ]


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Kill-test the residue-circulation candidate law.")
    parser.add_argument("--seed", type=int, default=174)
    parser.add_argument("--output-json", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    results = run_kill_tests(seed=int(args.seed))
    survived = sum(1 for result in results if result.verdict == "SURVIVED")
    killed = len(results) - survived
    print(f"candidate=residue_circulation_update variant=1 survived={survived} killed={killed}")
    for result in results:
        print(f"{result.verdict} {result.name}: {result.reason}")
        print(f"  details={result.details}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump([asdict(result) for result in results], handle, indent=2, sort_keys=True)
            handle.write("\n")
    return 0 if killed == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
