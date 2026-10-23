"""Small exact native-multiplication campaign; exploratory evidence, not physics.

All 52 supplied laws are retained independently of screen status or phase hits.
W(u)=1 is a biased multiplier filter, not a norm-preservation theorem. Open
orbits mean no finite certificate within the bound, never candidate rejection.
"""

from __future__ import annotations

import hashlib
from collections import Counter
from fractions import Fraction
from pathlib import Path

from theory_experiments import candidate_pipeline as pipeline
from theory_experiments import continuation_sufficiency as continuation
from theory_experiments.amplitude_algebra import Amplitude, AmplitudeAlgebra, WeightRule
from theory_experiments.candidate_history import History, record_batch
from theory_experiments.primitive_screen import (
    Limits,
    bounded_int,
    canonical_json,
    load_json,
    object_fields,
)

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = ROOT / "data/native_phase_search_v1.json"
SOURCE_PATHS = (
    "theory_experiments/native_phase_search.py",
    "scripts/search_native_phases.py",
    "data/native_phase_search_v1.json",
    "theory_experiments/amplitude_algebra.py",
    "theory_experiments/continuation_sufficiency.py",
    "theory_experiments/primitive_screen.py",
    "theory_experiments/candidate_pipeline.py",
    "theory_experiments/candidate_history.py",
)


def source_hashes() -> dict[str, str]:
    return {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for path in SOURCE_PATHS}


LOADED_SOURCE_HASHES = source_hashes()


def campaign_config() -> dict[str, object]:
    """The reviewed campaign is intentionally fixed, not a tuning interface."""
    return {
        "schema": "idt-native-phase-search-config/1",
        "parameter_min": -2, "parameter_max": 2,
        "weight_rules": ["quadratic", "quartic"], "include_scalar_controls": True,
        "multiplier_radius": 2, "multiplier_filter": "W(u)=1", "reference": [1, 0],
        "plane_seeds": [[1, 0], [1, 1]], "scalar_seeds": [[1, 0]],
        "max_multiplications": 16, "trace_length": 5,
        "readout": "W(x+1)/(W(x+1)+W(x-1))",
        "limits": Limits(1000, 1, 2, 2).specification(),
        "scope": "selected_integer_box_multiplier_family_and_readout_convention_only",
        "search_bias": "unit_weight_filter_strongly_favors_Gaussian_roots_no_physical_selection",
    }


def validate_config(value: object) -> dict[str, object]:
    row = object_fields(value, set(campaign_config()))
    # Canonical JSON distinguishes bools/floats from ints even where Python == does not.
    if canonical_json(row) != canonical_json(campaign_config()):
        raise ValueError("unsupported campaign configuration; only the fixed reviewed bounds are accepted")
    return row


def candidates() -> tuple[AmplitudeAlgebra, ...]:
    def token(number: int) -> str:
        return f"m{-number}" if number < 0 else f"p{number}"

    models: list[AmplitudeAlgebra] = []
    rules: tuple[WeightRule, ...] = ("quadratic", "quartic")
    for k in range(-2, 3):
        for eta in range(-2, 3):
            for rule in rules:
                models.append(AmplitudeAlgebra(
                    f"phase_v1_plane_k{token(k)}_eta{token(eta)}_{rule}",
                    "integer_plane", k, eta, rule))
    for rule in rules:
        models.append(AmplitudeAlgebra(f"phase_v1_scalar_{rule}", "integer_scalar", 0, 0, rule))
    return tuple(models)


def readout(model: AmplitudeAlgebra, state: Amplitude) -> dict[str, object]:
    plus = model.weight(model.add(state, (1, 0)))
    minus = model.weight(model.add(state, (-1, 0)))
    denominator = plus + minus
    issues: list[str] = []
    if plus < 0 or minus < 0:
        issues.append("negative_weight")
    if denominator == 0:
        issues.append("zero_denominator")
    elif denominator < 0:
        issues.append("negative_denominator")
    return {"state": list(state), "weight": str(model.weight(state)),
            "plus_weight": str(plus), "minus_weight": str(minus),
            "denominator": str(denominator), "valid": not issues,
            "issues": issues, "p": None if issues else str(Fraction(plus, denominator))}


def _finite_table(model: AmplitudeAlgebra, multiplier: Amplitude,
                  states: list[Amplitude], rows: list[dict[str, object]]) -> dict[str, object]:
    indices = {state: i for i, state in enumerate(states)}
    probabilities: list[Fraction] = []
    for row in rows:
        value = row["p"]
        if not isinstance(value, str):
            raise TypeError("finite continuation table requires valid readouts")
        probabilities.append(Fraction(value))
    labels = {p: i for i, p in enumerate(dict.fromkeys(probabilities))}
    table: dict[str, object] = {
        "schema": continuation.MODEL_SCHEMA,
        "transitions": [[indices[model.multiply(state, multiplier)] for state in states]],
        "readouts": [[str(p), str(1 - p)] for p in probabilities],
        "adapter": [labels[p] for p in probabilities],
    }
    analysis = continuation.analyze(table)
    if not continuation.verify_certificate(table, analysis["certificate"]):
        raise ValueError("continuation certificate failed verification; not a candidate failure")
    return {"model": table, "analysis": analysis,
            "state_order": [list(state) for state in states],
            "adapter_meaning": "current_readout_equality_only",
            "full_state_boundary": "finite_deterministic_table_not_quantum_state_or_physical_selection"}


def probe_orbit(model: AmplitudeAlgebra, multiplier: Amplitude, seed: Amplitude,
                *, max_steps: int = 16) -> dict[str, object]:
    bounded_int(max_steps, 1, 16)
    for pair in (multiplier, seed):
        if (len(pair) != 2 or any(type(x) is not int for x in pair)
                or (model.carrier == "integer_scalar" and pair[1] != 0)):
            raise ValueError("expected exact integer states on the supplied carrier")
    states = [seed]
    seen = {seed: 0}
    repeat_index: int | None = None
    repeated_state: Amplitude | None = None
    steps = 0
    for steps in range(1, max_steps + 1):
        following = model.multiply(states[-1], multiplier)
        if following in seen:
            repeat_index, repeated_state = seen[following], following
            break
        seen[following] = len(states)
        states.append(following)
    rows = [readout(model, state) for state in states]
    trace_states = [seed]
    for _ in range(4):
        trace_states.append(model.multiply(trace_states[-1], multiplier))
    trace = [readout(model, state) for state in trace_states]
    valid = all(row["valid"] for row in rows)
    table = (_finite_table(model, multiplier, states, rows)
             if repeat_index is not None and valid else None)
    target = ["1", "1/2", "0", "1/2", "1"]
    probabilities = [row["p"] for row in trace]
    return {
        "multiplier": list(multiplier), "multiplier_weight": str(model.weight(multiplier)),
        "multiplier_has_unit_weight": model.weight(multiplier) == 1,
        "seed": list(seed), "reference": [1, 0], "multiplications_checked": steps,
        "orbit_status": "exact_state_closure" if repeat_index is not None else "open_within_bound",
        "cycle_start_index": repeat_index, "cycle_length": (
            None if repeat_index is None else len(states) - repeat_index),
        "repeated_state": None if repeated_state is None else list(repeated_state),
        "visited": rows, "trace_first_five": trace,
        "quarter_cycle_trace_hit": probabilities == target,
        "nonbinary_trace": any(isinstance(p, str) and p not in ("0", "1") for p in probabilities),
        "visited_state_weights_equal_seed": all(model.weight(s) == model.weight(seed) for s in states),
        "weight_scope": "visited_states_only_not_global_norm_preservation",
        "continuation": table,
        "continuation_status": ("verified_finite_certificate" if table is not None else
                                "invalid_orbit_readout" if repeat_index is not None else
                                "no_finite_certificate_within_bound"),
        "candidate_verdict": "unchanged",
    }


def candidate_phase_evidence(model: AmplitudeAlgebra) -> dict[str, object]:
    seeds = ((1, 0), (1, 1)) if model.carrier == "integer_plane" else ((1, 0),)
    multipliers = [u for u in model.grid(2) if model.weight(u) == 1]
    orbits = [probe_orbit(model, u, seed) for u in multipliers for seed in seeds]
    return {"selected_multipliers": [list(u) for u in multipliers], "orbits": orbits,
            "quarter_cycle_hit": any(row["quarter_cycle_trace_hit"] for row in orbits),
            "nonbinary_trace_present": any(row["nonbinary_trace"] for row in orbits),
            "equal_one_i3": {"inputs": [[1, 0], [1, 0], [1, 0]],
                             "actual": str(model.third_order((1, 0), (1, 0), (1, 0)))},
            "candidate_verdict": "unchanged"}


def campaign(value: object, *, history: History | None = None) -> dict[str, object]:
    """Compute without writes, or explicitly archive screen observations in history.

    The returned phase report must separately be saved by the caller if desired.
    Existing history records are never replaced by the archival backend.
    """
    config = validate_config(value)
    before = source_hashes()
    if (before != LOADED_SOURCE_HASHES
            or before["theory_experiments/continuation_sufficiency.py"] != continuation.LOADED_MODULE_SHA256
            or before["theory_experiments/primitive_screen.py"] != continuation.LOADED_HELPER_SHA256):
        raise ValueError("phase sources changed since import; restart the interpreter")
    models = candidates()
    specs: list[object] = [model.specification() for model in models]
    limits = Limits(1000, 1, 2, 2)
    archival: dict[str, object] | None = None
    if history is None:
        screens = pipeline.run_batch(specs, limits)
    else:
        recorded = record_batch(specs, limits, history=history)
        screens = recorded.results
        archival = {"root": str(history.root), "submission": recorded.submission,
                    "observation": recorded.observation, "changes": recorded.changes,
                    "submission_path": str(history.root / "submissions" / (recorded.submission + ".json")),
                    "observation_path": str(history.root / "observations" / (recorded.observation + ".json.gz"))}
    rows: list[dict[str, object]] = []
    for model, result in zip(models, screens, strict=True):
        # Retain full bounded checks, witnesses and scope, but link the existing
        # provenance hashes rather than duplicating archived source contents.
        screen = {key: item for key, item in result.report.items() if key != "request"}
        request = object_fields(result.report["request"])
        rows.append({"candidate_specification": model.specification(),
                     "candidate_sha256": pipeline.digest(model.specification()),
                     "screen_request_key": result.key,
                     "screen_provenance_sha256": pipeline.digest(request["provenance"]),
                     "bounded_native_laws": screen, "phase": candidate_phase_evidence(model),
                     "candidate_verdict": "unchanged"})
    if source_hashes() != before:
        raise ValueError("phase sources changed during campaign; rerun from a stable checkout")
    counts = Counter(str(object_fields(row["bounded_native_laws"])["status"]) for row in rows)
    evidence: dict[str, object] = {
        "schema": "idt-native-phase-search/1", "config": config,
        "config_sha256": pipeline.digest(config), "source_sha256": before,
        "screen_provenance": object_fields(screens[0].report["request"])["provenance"],
        "limits": limits.specification(), "candidates": rows,
        "summary": {"candidate_count": len(rows), "screen_status_counts": dict(sorted(counts.items())),
                    "quarter_cycle_candidate_count": sum(
                        bool(object_fields(row["phase"])["quarter_cycle_hit"]) for row in rows)},
        "candidate_verdict": "unchanged", "proof_status": "exploratory_finite_exact_not_lean_proof",
        "empirical_status": "not_tested", "archival": archival,
        "boundaries": ["no_hit_only_in_selected_integer_box_multiplier_family_and_readout_convention",
                       "unit_weight_filter_strongly_favors_Gaussian_roots_no_physical_selection",
                       "closed_orbits_are_supplied_finite_models_not_QM_derivations",
                       "bounded_native_laws_are_separate_from_phase_diagnostics",
                       "all_candidates_retained_no_ranking_truth_scores_or_status_upgrades"],
    }
    return {**evidence, "report_sha256": pipeline.digest(evidence)}


def load_config(path: Path = DEFAULT_CONFIG) -> dict[str, object]:
    return validate_config(load_json(path))
