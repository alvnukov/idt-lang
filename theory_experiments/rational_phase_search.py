"""Fixed exact rational probes: supplied laws, not physical or universal proofs.

The unit filter, coordinate grid, seeds and readout are conventions. Retain every
candidate, open trace and invalid port; never infer physical selection from them.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from typing import TypeAlias

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments.candidate_history import History, record_batch
from theory_experiments.primitive_screen import (
    Limits,
    canonical_json,
    load_json,
    object_fields,
)
from theory_experiments.source_candidate import SourceCandidate, SourceSnapshot

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = ROOT / "data/rational_phase_search_v1.json"
SOURCE_PATHS = (
    "theory_experiments/rational_phase_search.py", "scripts/search_rational_phases.py",
    "data/rational_phase_search_v1.json", "theory_experiments/source_candidate.py",
    "theory_experiments/primitive_screen.py", "theory_experiments/candidate_pipeline.py",
    "theory_experiments/candidate_history.py",
)
State: TypeAlias = tuple[Fraction, Fraction]
Cell: TypeAlias = str | dict[str, object]
ONE: State = (Fraction(1), Fraction(0))
MISSING_BRIDGES = ("physical_preparation", "physical_readout_map", "physical_composites",
                   "full_QM", "SM", "gravity")


def source_hashes() -> dict[str, str]:
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCE_PATHS}


LOADED_SOURCE_HASHES = source_hashes()


@dataclass(frozen=True)
class RationalModel:
    id: str
    scalar: bool
    k: int
    eta: int
    power: int = 1

    def multiply(self, x: State, y: State) -> State:
        a, b = x
        c, d = y
        return a * c + self.k * b * d, a * d + b * c

    def weight(self, x: State) -> Fraction:
        a, b = x
        return (a * a + self.eta * b * b) ** self.power

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "carrier": "Q" if self.scalar else "Q^2",
                "representation": "exact Fraction pair (a,b); b=0 for Q",
                "product_square": self.k, "imaginary_weight": self.eta,
                "weight_power": self.power,
                "addition": "(a,b)+(c,d)=(a+c,b+d)",
                "multiplication": "(a,b)*(c,d)=(a*c+k*b*d,a*d+b*c)",
                "weight_rule": "quadratic" if self.power == 1 else "quartic_control",
                "weight": "W(a,b)=(a^2+eta*b^2)^power",
                "zero": ["0", "0"], "unit": ["1", "0"],
                "readout": "p(x)=W(x+(1,0))/(W(x+(1,0))+W(x-(1,0)))"}


def candidates() -> tuple[RationalModel, ...]:
    return (RationalModel("rational_scalar_quadratic", True, 0, 0),
            RationalModel("rational_dual_quadratic", False, 0, 0),
            RationalModel("rational_gaussian_quadratic", False, -1, 1),
            RationalModel("rational_weighted_two_quadratic", False, -2, 2),
            RationalModel("rational_gaussian_quartic", False, -1, 1, 2))


def campaign_config() -> dict[str, object]:
    return {"schema": "idt-rational-phase-search-config/1",
            "candidate_ids": [m.id for m in candidates()],
            "denominator_min": 1, "denominator_max": 8, "coordinate_radius": 2,
            "coordinate_rule": "sorted unique Fraction(n,d), -2*d<=n<=2*d, 1<=d<=8",
            "unit_filter": "W(u)=1", "matrix_states": "all_selected_units",
            "matrix_actions": "all_selected_units", "matrix_depth": 1,
            "clip_products_to_grid": False, "max_multiplications": 8,
            "scalar_seeds": [[1, 0]], "plane_seeds": [[1, 0], [1, 1]],
            "readout": "W(x+1)/(W(x+1)+W(x-1))",
            "scope": "selected_rational_grid_supplied_operations_readout_and_trace_bound_only"}


def validate_config(value: object) -> dict[str, object]:
    row = object_fields(value, set(campaign_config()))
    if canonical_json(row) != canonical_json(campaign_config()):
        raise ValueError("only the fixed reviewed rational campaign configuration is accepted")
    return row


def load_config(path: Path = DEFAULT_CONFIG) -> dict[str, object]:
    return validate_config(load_json(path))


def coordinates() -> tuple[Fraction, ...]:
    return tuple(sorted({Fraction(n, d) for d in range(1, 9) for n in range(-2*d, 2*d+1)}))


def state_json(state: State) -> list[str]:
    return [str(part) for part in state]


def port_readout(plus: Fraction, minus: Fraction) -> dict[str, object]:
    denominator = plus + minus
    issues = []
    if plus < 0 or minus < 0:
        issues.append("negative_weight")
    if denominator == 0:
        issues.append("zero_denominator")
    elif denominator < 0:
        issues.append("negative_denominator")
    return {"plus_weight": str(plus), "minus_weight": str(minus),
            "denominator": str(denominator), "valid": not issues, "issues": issues,
            "p": None if issues else str(plus / denominator)}


def readout(model: RationalModel, state: State) -> dict[str, object]:
    a, b = state
    return {"state": state_json(state), "weight": str(model.weight(state)),
            **port_readout(model.weight((a+1, b)), model.weight((a-1, b)))}


def _cell(row: dict[str, object]) -> Cell:
    p = row["p"]
    if isinstance(p, str):
        return p
    return row  # Invalid ports are explicit evidence, never silently omitted.


def probe_orbit(model: RationalModel, action: State, seed: State) -> dict[str, object]:
    states = [seed]
    seen = {seed: 0}
    repetition: dict[str, object] | None = None
    for t in range(1, 9):
        following = model.multiply(states[-1], action)
        states.append(following)
        if following in seen and repetition is None:
            repetition = {"first_index": seen[following], "repeat_index": t,
                          "cycle_length": t-seen[following], "state": state_json(following)}
        seen.setdefault(following, t)
    trace = [{"t": t, **readout(model, state)} for t, state in enumerate(states)]
    return {"action": state_json(action), "seed": state_json(seed), "trace": trace,
            "orbit_status": "exact_state_closure" if repetition else "open_within_bound",
            "first_exact_state_repetition": repetition,
            "nonbinary_trace": any(row["p"] not in (None, "0", "1") for row in trace),
            "invalid_readout": any(not row["valid"] for row in trace),
            "visited_state_weights_equal_seed": all(model.weight(s) == model.weight(seed) for s in states),
            "weight_scope": "nine_observed_states_only_not_a_universal_norm_theorem",
            "candidate_verdict": "unchanged"}


def continuation_matrix(model: RationalModel, units: list[State]) -> dict[str, object]:
    current = [readout(model, x) for x in units]
    matrix = [[_cell(readout(model, model.multiply(x, u))) for u in units] for x in units]
    tokens = [[canonical_json(cell) for cell in row] for row in matrix]
    unique_rows: list[list[Cell]] = []
    row_ids: dict[tuple[str, ...], int] = {}
    row_indices = []
    for row, token in zip(matrix, tokens, strict=True):
        key = tuple(token)
        if key not in row_ids:
            row_ids[key] = len(unique_rows)
            unique_rows.append(row)
        row_indices.append(row_ids[key])
    groups: dict[str, list[int]] = {}
    for index, current_row in enumerate(current):
        groups.setdefault(canonical_json(_cell(current_row)), []).append(index)
    pair_count = sum(len(indices)*(len(indices)-1)//2 for indices in groups.values()
                     if current[indices[0]]["valid"])
    comparisons = 0
    witness: dict[str, object] | None = None
    # Global lexicographic x,y,u ordering, not order of current-readout classes.
    for left, right in combinations(range(len(units)), 2):
        if (not current[left]["valid"] or not current[right]["valid"]
                or _cell(current[left]) != _cell(current[right])):
            continue
        for action_index, action in enumerate(units):
            comparisons += 1
            differs = tokens[left][action_index] != tokens[right][action_index]
            valid_next = isinstance(matrix[left][action_index], str) and isinstance(matrix[right][action_index], str)
            if differs and valid_next and witness is None:
                witness = {"state_x": state_json(units[left]), "state_y": state_json(units[right]),
                           "action": state_json(action), "current_readout": current[left],
                           "next_x": readout(model, model.multiply(units[left], action)),
                           "next_y": readout(model, model.multiply(units[right], action))}
    partitions = [{"current_cell": _cell(current[indices[0]]), "state_indices": indices,
                   "distinct_full_continuation_rows": len({row_indices[i] for i in indices})}
                  for indices in groups.values()]
    return {"state_order": [state_json(s) for s in units],
            "action_order": [state_json(s) for s in units], "current_readouts": current,
            "encoding": "matrix[x][u]=unique_rows[row_indices[x]][u]",
            "unique_rows": unique_rows, "row_indices": row_indices,
            "current_readout_partition": partitions, "distinct_full_rows": len(unique_rows),
            "first_witness": witness,
            "result": "same_current_different_one_step_readout" if witness else "no_witness_in_selected_matrix",
            "matrix_cells": len(units)**2, "same_current_unordered_pairs": pair_count,
            "action_comparisons_planned": pair_count*len(units),
            "action_comparisons_performed": comparisons, "matrix_complete": True,
            "invalid_current_readouts": sum(not row["valid"] for row in current),
            "invalid_matrix_cells": sum(isinstance(cell, dict) for row in matrix for cell in row),
            "scope": "same_candidate_same_readout_same_action_one_step_complete_selected_matrix_only",
            "not_claimed": "universal_sufficiency_all_words_or_observational_equivalence"}


def candidate_evidence(model: RationalModel) -> dict[str, object]:
    grid = coordinates()
    points = ((a, Fraction(0)) for a in grid) if model.scalar else ((a, b) for a, b in product(grid, repeat=2))
    units: list[State] = [state for state in points if model.weight(state) == 1]
    seeds = [ONE] if model.scalar else [ONE, (Fraction(1), Fraction(1))]
    traces = [probe_orbit(model, u, seed) for seed in seeds for u in units]
    summaries = []
    for seed_index, seed in enumerate(seeds):
        rows = traces[seed_index*len(units):(seed_index+1)*len(units)]
        summaries.append({"seed": state_json(seed), "trace_count": len(rows),
                          "closed": sum(row["orbit_status"] == "exact_state_closure" for row in rows),
                          "open": sum(row["orbit_status"] == "open_within_bound" for row in rows),
                          "nonbinary": sum(bool(row["nonbinary_trace"]) for row in rows),
                          "invalid": sum(bool(row["invalid_readout"]) for row in rows),
                          "weight_change": sum(not row["visited_state_weights_equal_seed"] for row in rows)})
    # Direct equal-one third difference, not a registered native screen verdict.
    i3 = (model.weight((Fraction(3), Fraction(0))) - 3*model.weight((Fraction(2), Fraction(0)))
          + 3*model.weight(ONE) - model.weight((Fraction(0), Fraction(0))))
    return {"candidate_specification": model.specification(),
            "candidate_sha256": pipeline.digest(model.specification()),
            "coverage": {"coordinate_count": len(grid), "scanned_tuples": len(grid) if model.scalar else len(grid)**2,
                         "selected_units": len(units)},
            "selected_units": [state_json(u) for u in units], "traces": traces,
            "trace_summaries": summaries, "continuation": continuation_matrix(model, units),
            "equal_one_i3": {"inputs": [["1", "0"]]*3, "actual": str(i3),
                             "formula": "W(3)-3*W(2)+3*W(1)-W(0)",
                             "scope": "direct_formula_control_not_native_screen_status"},
            "candidate_verdict": "unchanged"}


def signature_comparisons(rows: list[dict[str, object]]) -> dict[str, object]:
    signatures: list[set[str]] = []
    ids = []
    for row in rows:
        ids.append(object_fields(row["candidate_specification"])["id"])
        traces = row["traces"]
        if not isinstance(traces, list):
            raise TypeError("expected trace list")
        values = set()
        for value in traces:
            trace = object_fields(value)
            if trace["seed"] != ["1", "0"]:
                continue
            points = trace["trace"]
            if not isinstance(points, list):
                raise TypeError("expected trace points")
            values.add(canonical_json([_cell(object_fields(p)) for p in points]))
        signatures.append(values)
    return {"seed": ["1", "0"], "signature": "all_nine_readouts_in_order",
            "distinct_counts": dict(zip((str(i) for i in ids), (len(s) for s in signatures), strict=True)),
            "pairs": [{"left": ids[i], "right": ids[j], "intersection": len(signatures[i] & signatures[j]),
                       "left_only": len(signatures[i]-signatures[j]), "right_only": len(signatures[j]-signatures[i])}
                      for i, j in combinations(range(len(rows)), 2)],
            "scope": "bounded_grid_and_supplied_readout_convention_not_physical_distinction_or_equivalence"}


def source_proposals(config: dict[str, object], hashes: dict[str, str]) -> list[object]:
    path = "theory_experiments/rational_phase_search.py"
    text = (ROOT / path).read_text(encoding="utf-8")
    snapshot = SourceSnapshot(path, 1, len(text.splitlines()), hashes[path], text)
    specs: list[object] = [SourceCandidate(m.id, "lower_law",
        (canonical_json(m.specification()), "config_sha256="+pipeline.digest(config),
         "source_context_sha256="+pipeline.digest(hashes)),
        "exploratory_finite", MISSING_BRIDGES, (snapshot,)).specification() for m in candidates()]
    if len(canonical_json(specs).encode("utf-8")) > 131072:
        raise ValueError("source proposal batch exceeds 128 KiB")
    return specs


def campaign(value: object, *, history: History | None = None) -> dict[str, object]:
    config = validate_config(value)
    before = source_hashes()
    if before != LOADED_SOURCE_HASHES or pipeline.provenance()["source_sha256"] != pipeline.LOADED_SOURCE_HASHES:
        raise ValueError("sources changed since import; restart from a stable checkout")
    specs = source_proposals(config, before)
    if source_hashes() != before:
        raise ValueError("sources changed during campaign; rerun")
    archival: dict[str, object] | None = None
    limits = Limits(1000, 1, 2, 2)
    if history is None:
        results = pipeline.run_batch(specs, limits)
    else:
        recorded = record_batch(specs, limits, history=history)
        results = recorded.results
        archival = {"root": str(history.root), "submission": recorded.submission,
                    "observation": recorded.observation, "changes": recorded.changes,
                    "submission_path": str(history.root / "submissions" / (recorded.submission+".json")),
                    "observation_path": str(history.root / "observations" / (recorded.observation+".json.gz"))}
    # Archive all inputs before expensive probes so a probe crash cannot lose them.
    rows = [candidate_evidence(model) for model in candidates()]
    for row, result in zip(rows, results, strict=True):
        row["source_proposal_screen"] = {"status": result.report["status"], "request_key": result.key,
            "provenance_sha256": pipeline.digest(object_fields(result.report["request"])["provenance"]),
            "meaning": "source_proposal_only_no_registered_rational_prediction_adapter"}
    if source_hashes() != before or pipeline.provenance()["source_sha256"] != pipeline.LOADED_SOURCE_HASHES:
        raise ValueError("sources changed during campaign; rerun")
    evidence: dict[str, object] = {
        "schema": "idt-rational-phase-search/1", "config": config,
        "config_sha256": pipeline.digest(config), "source_sha256": before,
        "screen_provenance": object_fields(results[0].report["request"])["provenance"],
        "candidates": rows, "signature_comparisons": signature_comparisons(rows),
        "summary": {"candidate_count": len(rows), "selected_units": [object_fields(r["coverage"])["selected_units"] for r in rows],
                    "matrix_cells": [object_fields(r["continuation"])["matrix_cells"] for r in rows],
                    "source_proposal_statuses": [result.report["status"] for result in results]},
        "candidate_verdict": "unchanged", "proof_status": "exploratory_finite_exact_not_formal_proof",
        "empirical_status": "not_tested", "archival": archival,
        "boundaries": ["supplied_Q_extensions_operations_and_readout_not_derived_primitives",
                       "unit_weight_filter_and_coordinate_box_are_biased_not_physical_selection",
                       "seeds_do_not_have_equal_norm_across_families",
                       "W(u)=1_does_not_prove_universal_norm_preservation",
                       "no_witness_only_complete_selected_one_step_matrix_not_all_words",
                       "same_current_different_next_also_occurs_classically_not_quantum_Bell_or_contextuality_evidence",
                       "open_within_bound_never_rejection_or_finite_certificate",
                       "previous_integer_results_unchanged",
                       "physical_preparation_composites_QM_SM_gravity_not_derived",
                       "all_five_candidates_retained_without_ranking_or_truth_scores"]}
    return {**evidence, "report_sha256": pipeline.digest(evidence)}
