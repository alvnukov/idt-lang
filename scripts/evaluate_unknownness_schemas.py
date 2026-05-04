from __future__ import annotations

import argparse
import json
import random
import sys
from collections.abc import Callable, Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.search_unknownness_automata import (  # noqa: E402
    EMPTY,
    MINUS,
    PLUS,
    RESIDUE,
    Rule,
    State,
    Triple,
    active_count,
    audit_x_causality,
    build_seeds,
    conflict_erased_rule,
    flip_triple,
    has_conflict,
    index_of,
    inertized_rule,
    render_cells,
    score_rule,
    set_equivariant,
    simulate,
    triple_of,
)

Verdict = Literal["HIT", "NEAR_MISS", "KILL"]
ProjectionName = Literal["context", "bell", "metric"]
SchemaFn = Callable[[Triple, int], State]


@dataclass(frozen=True)
class ProjectionResult:
    passed: bool
    reason: str


@dataclass(frozen=True)
class SchemaEvaluation:
    family: str
    variant: int
    verdict: Verdict
    passed_projections: list[ProjectionName]
    context: ProjectionResult
    bell: ProjectionResult
    metric: ProjectionResult
    base_counts: dict[str, int]
    inert_counts: dict[str, int]
    erased_counts: dict[str, int]
    x_audit: dict[str, int]
    scale_active_counts: dict[str, int]
    compact_description: str


@dataclass(frozen=True)
class SchemaFamily:
    name: str
    variants: int
    description: str
    fn: SchemaFn


def has_record(triple: Triple) -> bool:
    return PLUS in triple or MINUS in triple


def majority_record(triple: Triple) -> State:
    plus_count = triple.count(PLUS)
    minus_count = triple.count(MINUS)
    if plus_count > minus_count:
        return PLUS
    if minus_count > plus_count:
        return MINUS
    return EMPTY


def make_rule(schema: SchemaFn, variant: int) -> Rule:
    table: list[State | None] = [None] * 64
    set_equivariant(table, (EMPTY, EMPTY, EMPTY), EMPTY)
    for index in range(64):
        triple = triple_of(index)
        flipped = flip_triple(triple)
        if index_of(flipped) < index:
            continue
        output = schema(triple, variant)
        set_equivariant(table, triple, output)
    return tuple(EMPTY if state is None else state for state in table)


def least_residue(triple: Triple, variant: int) -> State:
    left, center, right = triple
    if has_conflict(triple):
        return RESIDUE
    if center in (PLUS, MINUS) and variant % 2 == 0:
        return center
    if left == right and left in (PLUS, MINUS):
        return left
    if RESIDUE in triple:
        return RESIDUE if variant >= 2 and has_record(triple) else EMPTY
    return majority_record(triple)


def residue_circulation(triple: Triple, variant: int) -> State:
    left, center, right = triple
    if has_conflict(triple):
        return RESIDUE
    if center == RESIDUE and variant % 2 == 0:
        return RESIDUE
    if left == RESIDUE or right == RESIDUE:
        if has_record(triple) and variant >= 2:
            return majority_record(triple)
        return RESIDUE
    if left == right and left in (PLUS, MINUS):
        return RESIDUE if variant == 3 else left
    return center if center in (PLUS, MINUS) else EMPTY


def boundary_cancellation(triple: Triple, variant: int) -> State:
    left, center, right = triple
    if has_conflict(triple):
        return EMPTY if center == RESIDUE and variant % 2 == 1 else RESIDUE
    if left == RESIDUE and right == RESIDUE:
        return center if center in (PLUS, MINUS) else RESIDUE
    if left == right and left in (PLUS, MINUS):
        return left
    if RESIDUE in triple and has_record(triple):
        return EMPTY if variant >= 2 else RESIDUE
    return center if center in (PLUS, MINUS) else EMPTY


def compatibility_relaxation(triple: Triple, variant: int) -> State:
    _left, center, _right = triple
    if has_conflict(triple):
        return RESIDUE
    majority = majority_record(triple)
    if majority != EMPTY:
        return majority if variant != 1 else (center if center in (PLUS, MINUS) else EMPTY)
    if RESIDUE in triple:
        return RESIDUE if variant in (2, 3) else EMPTY
    return EMPTY


def reversible_readout_split(triple: Triple, variant: int) -> State:
    left, center, right = triple
    if has_conflict(triple):
        return RESIDUE
    if center == RESIDUE:
        return majority_record(triple) if variant >= 2 and has_record(triple) else RESIDUE
    if left == RESIDUE or right == RESIDUE:
        return center if center in (PLUS, MINUS) and variant % 2 == 1 else RESIDUE
    if center in (PLUS, MINUS):
        return center
    return PLUS if left == right == PLUS else MINUS if left == right == MINUS else EMPTY


def coarse_residue_geometry(triple: Triple, variant: int) -> State:
    residue_count = triple.count(RESIDUE)
    if has_conflict(triple):
        return RESIDUE
    if residue_count >= 2:
        return RESIDUE
    if residue_count == 1:
        return majority_record(triple) if variant >= 2 and has_record(triple) else RESIDUE
    majority = majority_record(triple)
    return majority if variant % 2 == 0 else EMPTY


def global_constraint_local_readout(triple: Triple, variant: int) -> State:
    left, center, right = triple
    if has_conflict(triple):
        return RESIDUE
    if center == RESIDUE:
        return EMPTY if variant == 0 else RESIDUE
    if left == RESIDUE and right == RESIDUE:
        return RESIDUE
    if RESIDUE in triple:
        return center if center in (PLUS, MINUS) and variant >= 2 else RESIDUE
    if left == right and left in (PLUS, MINUS):
        return left
    return EMPTY


def parity_holonomy(triple: Triple, variant: int) -> State:
    if has_conflict(triple):
        return RESIDUE
    non_empty = sum(1 for state in triple if state != EMPTY)
    if RESIDUE in triple:
        return RESIDUE if non_empty % 2 == variant % 2 else majority_record(triple)
    majority = majority_record(triple)
    if majority != EMPTY and non_empty % 2 == 1:
        return majority
    return EMPTY


def record_residue_dual_flow(triple: Triple, variant: int) -> State:
    left, center, right = triple
    if has_conflict(triple):
        return RESIDUE
    if center in (PLUS, MINUS) and (left == EMPTY or right == EMPTY):
        return RESIDUE if variant >= 2 else center
    if RESIDUE in triple and has_record(triple):
        return majority_record(triple) if variant % 2 == 1 else RESIDUE
    if left == right and left in (PLUS, MINUS):
        return left
    return center if center in (PLUS, MINUS) else EMPTY


def scale_critical(triple: Triple, variant: int) -> State:
    if has_conflict(triple):
        return RESIDUE
    residue_count = triple.count(RESIDUE)
    record_count = triple.count(PLUS) + triple.count(MINUS)
    if residue_count == 1 and record_count == 1:
        return RESIDUE
    if residue_count >= 2:
        return EMPTY if variant % 2 == 0 else RESIDUE
    if record_count == 2:
        return majority_record(triple)
    if record_count == 1:
        return RESIDUE if variant >= 2 else EMPTY
    return EMPTY


SCHEMA_FAMILIES: tuple[SchemaFamily, ...] = (
    SchemaFamily("least_residue_update", 4, "minimize local unresolved residue", least_residue),
    SchemaFamily("residue_circulation_update", 4, "conserve residue as local circulation", residue_circulation),
    SchemaFamily("boundary_cancellation_update", 4, "form records at cancellation boundaries", boundary_cancellation),
    SchemaFamily("compatibility_relaxation_update", 4, "relax distinctions toward local compatibility", compatibility_relaxation),
    SchemaFamily("reversible_exposure_readout_split", 4, "separate reversible exposure from readout stabilization", reversible_readout_split),
    SchemaFamily("coarse_grained_residue_geometry", 4, "project residue density as effective geometry", coarse_residue_geometry),
    SchemaFamily("global_constraint_local_readout_split", 4, "global constraints with local readouts", global_constraint_local_readout),
    SchemaFamily("parity_holonomy_residue", 4, "closed parity residue hidden from open local readout", parity_holonomy),
    SchemaFamily("record_residue_dual_flow", 4, "records export compensating boundary residue", record_residue_dual_flow),
    SchemaFamily("scale_critical_update", 4, "edge between frozen records and chaotic residue", scale_critical),
)


def context_projection(rule: Rule, size: int, steps: int, burn_in: int) -> ProjectionResult:
    seed = [EMPTY] * size
    seed[size // 2 - 2] = PLUS
    seed[size // 2] = RESIDUE
    seed[size // 2 + 2] = MINUS
    cells = tuple(seed)

    def partial_step(input_cells: tuple[State, ...], parity: int) -> tuple[State, ...]:
        output = list(input_cells)
        for index, center in enumerate(input_cells):
            if index % 2 != parity:
                continue
            left = input_cells[(index - 1) % size]
            right = input_cells[(index + 1) % size]
            output[index] = rule[index_of((left, center, right))]
        return tuple(output)

    ab = partial_step(partial_step(cells, 0), 1)
    ba = partial_step(partial_step(cells, 1), 0)
    if ab == ba:
        return ProjectionResult(False, "even/odd exposure order commutes on conflict-residue witness")
    ab_label, _ = simulate(rule, ab, steps, burn_in)
    ba_label, _ = simulate(rule, ba, steps, burn_in)
    if ab_label in {"dead", "frozen", "periodic", "moving"} and ba_label in {"dead", "frozen", "periodic", "moving"}:
        return ProjectionResult(True, f"order witness {render_cells(ab)} != {render_cells(ba)} with stable labels {ab_label}/{ba_label}")
    return ProjectionResult(False, f"order differs but does not stabilize cleanly: {ab_label}/{ba_label}")


def bell_projection(rule: Rule, seeds: Sequence[tuple[State, ...]], steps: int, burn_in: int) -> ProjectionResult:
    score, counts = score_rule(rule, seeds, steps, burn_in, residue_critical=True)
    _inert_score, inert_counts = score_rule(inertized_rule(rule), seeds, steps, burn_in, residue_critical=False)
    _erased_score, erased_counts = score_rule(conflict_erased_rule(rule), seeds, steps, burn_in, residue_critical=False)
    audit = audit_x_causality(rule, seeds, steps)
    active = active_count(counts)
    inert_active = active_count(inert_counts)
    erased_active = active_count(erased_counts)
    x_ratio = 1.0
    if audit["x_participations"] > 0:
        x_ratio = audit["x_to_record"] / audit["x_participations"]
    if score > 0 and active > 0 and inert_active == 0 and erased_active > 0 and x_ratio <= 0.20:
        return ProjectionResult(True, f"global residue critical: active={active}, inert_active=0, erased_active={erased_active}, x_to_record_ratio={x_ratio:.3f}")
    return ProjectionResult(False, f"failed residue/no-transfer screen: active={active}, inert_active={inert_active}, erased_active={erased_active}, x_to_record_ratio={x_ratio:.3f}")


def metric_projection(rule: Rule, sizes: Sequence[int], steps: int, burn_in: int, seed: int) -> ProjectionResult:
    active_by_size: list[int] = []
    for size in sizes:
        seeds = build_seeds(size, random.Random(seed + size), random_seed_count=10)
        _score, counts = score_rule(rule, seeds, steps, burn_in, residue_critical=True)
        active_by_size.append(active_count(counts))
    if all(1 <= active <= 10 for active in active_by_size) and len(set(active_by_size)) > 1:
        return ProjectionResult(True, f"scale-sensitive active counts={active_by_size}")
    return ProjectionResult(False, f"no robust scale-sensitive band: active counts={active_by_size}")


def evaluate_schema(family: SchemaFamily, variant: int, size: int, steps: int, burn_in: int, seed: int) -> SchemaEvaluation:
    rule = make_rule(family.fn, variant)
    seeds = build_seeds(size, random.Random(seed), random_seed_count=10)
    _score, counts = score_rule(rule, seeds, steps, burn_in, residue_critical=True)
    _inert_score, inert_counts = score_rule(inertized_rule(rule), seeds, steps, burn_in, residue_critical=False)
    _erased_score, erased_counts = score_rule(conflict_erased_rule(rule), seeds, steps, burn_in, residue_critical=False)
    audit = audit_x_causality(rule, seeds, steps)
    context = context_projection(rule, size, steps, burn_in)
    bell = bell_projection(rule, seeds, steps, burn_in)
    sizes = (max(24, size - 16), size, size + 16)
    metric = metric_projection(rule, sizes, steps, burn_in, seed)
    scale_active_counts: dict[str, int] = {}
    for scale_size in sizes:
        scale_seeds = build_seeds(scale_size, random.Random(seed + scale_size), random_seed_count=10)
        _scale_score, scale_counts = score_rule(rule, scale_seeds, steps, burn_in, residue_critical=True)
        scale_active_counts[str(scale_size)] = active_count(scale_counts)

    passed: list[ProjectionName] = []
    if context.passed:
        passed.append("context")
    if bell.passed:
        passed.append("bell")
    if metric.passed:
        passed.append("metric")
    verdict: Verdict
    if len(passed) == 3:
        verdict = "HIT"
    elif len(passed) >= 2:
        verdict = "NEAR_MISS"
    else:
        verdict = "KILL"

    return SchemaEvaluation(
        family=family.name,
        variant=variant,
        verdict=verdict,
        passed_projections=passed,
        context=context,
        bell=bell,
        metric=metric,
        base_counts=counts,
        inert_counts=inert_counts,
        erased_counts=erased_counts,
        x_audit=audit,
        scale_active_counts=scale_active_counts,
        compact_description=family.description,
    )


def evaluate_all(size: int, steps: int, burn_in: int, seed: int) -> list[SchemaEvaluation]:
    results: list[SchemaEvaluation] = []
    for family in SCHEMA_FAMILIES:
        for variant in range(family.variants):
            results.append(evaluate_schema(family, variant, size, steps, burn_in, seed))
    return sorted(results, key=lambda result: (len(result.passed_projections), result.verdict), reverse=True)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Evaluate compact unknownness schema families against projection kill tests.")
    parser.add_argument("--size", type=int, default=40)
    parser.add_argument("--steps", type=int, default=120)
    parser.add_argument("--burn-in", type=int, default=16)
    parser.add_argument("--seed", type=int, default=174)
    parser.add_argument("--output-jsonl", default="")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    results = evaluate_all(size=int(args.size), steps=int(args.steps), burn_in=int(args.burn_in), seed=int(args.seed))
    for result in results:
        print(
            f"verdict={result.verdict} family={result.family} variant={result.variant} "
            f"passed={','.join(result.passed_projections) or '-'} "
            f"base_active={active_count(result.base_counts)} inert_active={active_count(result.inert_counts)} "
            f"scale={result.scale_active_counts}"
        )
        print(f"  context: {result.context.reason}")
        print(f"  bell: {result.bell.reason}")
        print(f"  metric: {result.metric.reason}")
    if args.output_jsonl:
        with open(str(args.output_jsonl), "w", encoding="utf-8") as handle:
            for result in results:
                handle.write(json.dumps(asdict(result), sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
