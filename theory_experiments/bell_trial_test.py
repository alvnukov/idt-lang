"""Fixed-N local-response test and pinned released-candidate-record replay.

No physical locality, setting independence, calibration, or stopping policy is
inferred from a candidate label or from these records. Exact arithmetic is not
an unconditional empirical verdict.
"""

from __future__ import annotations

import csv
import hashlib
import io
import os
import re
import stat
from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from typing import cast

from theory_experiments.primitive_screen import (
    Check,
    Limits,
    bounded_int,
    candidate_id,
    canonical_json,
    load_json,
    object_fields,
)

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "data/raw_observations/hensen2015.json"
EXPERIMENT = "hensen2015_fixed_n_v1"
BRIDGE = "local_response_fixed_n_v1"
TAU = Fraction(27, 2500000)
Q = Fraction(3, 4) + 3 * (TAU + TAU * TAU)
ALPHA = Fraction(1, 20)
SHARED_NULL_TEST = "hensen2015_N245_K196_local_class_q_v1"
RAW_SHA256 = "5a6b1853554ad508d35c795415d64922ed9e5bc0469f6052ad222486ad3566ff"
RAW_SIZE = 431094
MATRIX = [[23, 3, 4, 23], [33, 11, 5, 30], [22, 10, 6, 24], [4, 20, 21, 6]]
RECIPE = {
    "id": "hensen2015_released_candidate_records_v1",
    "herald_starts_ps_by_channel": [5426350, 5425700],
    "herald_length_ps": 52450, "second_window_shift_ps": 250000,
    "herald_endpoints": "left_closed_right_open_different_detectors",
    "invalid_marker": "each_age_zero_or_strictly_greater_than_250",
    "post_excitation": "both_fields_zero",
    "readout": "plus_one_iff_10620_lt_t_le_14320_ns_else_minus_one_including_zero",
    "win": "(-1)^(a*b)*x*y=1",
    "record_scope": "released_broad_two_photon_preselected_candidates_not_full_timetags",
}
ASSUMPTIONS = (
    "actual_local_response_table_or_local_stochastic_history_dependent_mixture",
    "conditional_joint_setting_independence_and_paper_setting_predictability_model",
    "per_history_conditional_win_probability_at_most_q",
    "fixed_data_independent_N_not_optional_stopping",
    "event_ready_selection_and_readout_bridge_as_stated",
)
LIMITATIONS = (
    "QRNG_tau_is_paper_two_sigma_estimate_plus_model_not_certified_conditional_bound",
    "no_independently_timestamped_N245_commitment_verified",
    "dataset_and_analysis_policy_selection_retrospective_not_new_preregistration",
    "per_run_risk_guarantee_does_not_cover_retrospective_policy_selection",
    "base_admits_local_table_does_not_mean_base_entails_locality",
    "no_IDT_QM_acceptance_or_unconditional_primitive_rejection",
)


@dataclass(frozen=True)
class BellLocalResponse:
    id: str
    experiment: str
    bridge: str
    A0: int
    A1: int
    B0: int
    B1: int

    def __post_init__(self) -> None:
        for identifier in (self.id, self.experiment, self.bridge):
            candidate_id(identifier)
        for sign in (self.A0, self.A1, self.B0, self.B1):
            if type(sign) is not int or sign not in (-1, 1):
                raise ValueError("local response signs must be integer -1 or +1, not booleans")

    def specification(self) -> dict[str, object]:
        return {"id": self.id, "family": "bell_local_response", "experiment": self.experiment,
                "bridge": self.bridge, "A0": self.A0, "A1": self.A1, "B0": self.B0, "B1": self.B1}


def parse_bell_local_response(value: object) -> BellLocalResponse:
    row = object_fields(value, {"id", "family", "experiment", "bridge", "A0", "A1", "B0", "B1"})
    if row["family"] != "bell_local_response":
        raise ValueError("expected bell_local_response; source or nonlocal models need their own adapter")
    signs = []
    for key in ("A0", "A1", "B0", "B1"):
        val = bounded_int(row[key], -1, 1)
        if val == 0:
            raise ValueError("local response signs must be -1 or +1")
        signs.append(val)
    return BellLocalResponse(candidate_id(row["id"]), candidate_id(row["experiment"]),
                             candidate_id(row["bridge"]), *signs)


def predict_local_null(candidate: BellLocalResponse) -> dict[str, object]:
    """Construct the null before reading observations; no registry argument/access."""
    cells = [{"a": a, "b": b, "x": x, "y": y, "win": (-1) ** (a*b) * x*y == 1}
             for a, x in enumerate((candidate.A0, candidate.A1))
             for b, y in enumerate((candidate.B0, candidate.B1))]
    return {"cells": cells, "winning_cells": sum(bool(cell["win"]) for cell in cells),
            "uniform_setting_cap": "3/4", "conservative_class_cap": str(Q),
            "null_class": "local_stochastic_history_dependent_under_conditional_setting_contract",
            "artifact": "Proofs/QMClosure/BellLocalTrialNull.lean",
            "artifact_relation": "reviewed_recurrence_not_formal_verification_of_Python",
            "proof_check": "not_run_by_this_evaluator"}


def _probability(value: Fraction, *, positive: bool = False) -> None:
    if (not isinstance(value, Fraction) or not (0 <= value <= 1)
            or (positive and value == 0) or value.denominator > 10**14):
        raise ValueError("expected exact probability in [0,1] with denominator <= 10^14")


def tail_row(n: int, q: Fraction) -> tuple[Fraction, ...]:
    """B(n,k) recurrence in common-denominator integers, including k=n+1."""
    bounded_int(n, 0, 512)
    _probability(q)
    if n * len(str(q.denominator)) > 4000:
        raise ValueError("exact recurrence exceeds bounded integer-display resource budget")
    return _tail_row(n, q)


@lru_cache(maxsize=8)
def _tail_row(n: int, q: Fraction) -> tuple[Fraction, ...]:
    # ponytail: quadratic finite recurrence bounded at N=512; no asymptotic approximation.
    numerators = [1, 0]
    denominator = 1
    for size in range(n):
        denominator *= q.denominator
        numerators = [denominator] + [
            q.numerator * numerators[k] + (q.denominator-q.numerator) * numerators[k+1]
            for k in range(size+1)] + [0]
    return tuple(Fraction(value, denominator) for value in numerators)


def number(value: Fraction) -> dict[str, str]:
    with localcontext() as context:
        context.prec = 18
        decimal = str(Decimal(value.numerator) / Decimal(value.denominator))
    return {"exact": str(value), "decimal_display": decimal}


def assess_counts(n: int, k: int, q: Fraction = Q, alpha: Fraction = ALPHA) -> dict[str, object]:
    bounded_int(n, 1, 512)
    bounded_int(k, 0, n)
    _probability(alpha, positive=True)
    tails = tail_row(n, q)
    # Threshold depends only on N,q,alpha; never on the observed K.
    critical = next(index for index, tail in enumerate(tails) if tail <= alpha)
    return {"N": n, "K": k, "q": number(q), "alpha": number(alpha),
            "tail": number(tails[k]), "critical_wins": critical,
            "critical_tail": number(tails[critical]),
            "status": "conditional_statistical_exclusion" if k >= critical else "not_excluded",
            "unconditional_verdict": "not_established",
            "risk_contract": "fixed_N_conditional_per_history_win_cap_not_IID_required",
            "assumptions": list(ASSUMPTIONS), "limitations": list(LIMITATIONS)}


def reviewed_counts() -> dict[str, object]:
    row = object_fields(load_json(REGISTRY), {"schema", "provenance", "recipe", "raw", "reviewed_counts", "limitations"})
    if row["schema"] != "idt-hensen2015-registry/1" or row["recipe"] != RECIPE:
        raise ValueError("unknown registry schema or changed recipe")
    raw = object_fields(row["raw"])
    counts = object_fields(row["reviewed_counts"], {"released_rows", "herald", "also_markers", "N", "K", "matrix"})
    if (raw.get("sha256") != RAW_SHA256 or raw.get("size_bytes") != RAW_SIZE
            or counts != {"released_rows": 4746, "herald": 361, "also_markers": 248,
                          "N": 245, "K": 196, "matrix": MATRIX}):
        raise ValueError("reviewed record does not match fixed source/count contract")
    return row


def evaluate_bell_local_response(candidate: BellLocalResponse, limits: Limits
                                 ) -> tuple[tuple[Check, ...], dict[str, object]]:
    assert_loaded_sources()
    prediction = predict_local_null(candidate)
    details: dict[str, object] = {"execution_status": "unsupported", "prediction": prediction,
        "candidate_verdict": "unconditional_verdict_not_established", "assumptions": list(ASSUMPTIONS),
        "limits_role": "four_cell_structural_completion_only_not_statistical_sample_size",
        "empirical_status": "not_tested", "limitations": list(LIMITATIONS),
        "shared_null_test_id": SHARED_NULL_TEST,
        "multiple_candidate_interpretation": "one_common_local_null_test_not_16_independent_discoveries"}
    if candidate.experiment != EXPERIMENT or candidate.bridge != BRIDGE:
        details["unsupported_reason"] = "unknown_experiment_or_missing_explicit_bridge"
        return (Check("local_response_structure", "unsupported", 0, 4,
                      "explicit_four_cell_local_table", ASSUMPTIONS, None),), details
    if limits.max_cases < 4:
        details["execution_status"] = "inconclusive"
        return (Check("local_response_structure", "inconclusive", 0, 4,
                      "explicit_four_cell_local_table", ASSUMPTIONS, None),), details
    # No data access before the prediction/null class has been constructed.
    data = reviewed_counts()
    assessment = assess_counts(245, 196)
    details.update({"execution_status": "complete", "observation_origin": "reviewed_count_replay_not_raw_reexecution",
                    "observation": data, "assessment": assessment, "empirical_status": assessment["status"]})
    assert_loaded_sources()
    return (Check("local_response_structure", "no_counterexample_within_bounds", 4, 4,
                  "explicit_four_cell_local_table_not_empirical_acceptance", ASSUMPTIONS, None),), details


def readout_sign(time_ns: int) -> int:
    bounded_int(time_ns, 0, 2**63-1)
    return 1 if 10620 < time_ns <= 14320 else -1


def filter_reasons(values: tuple[int, ...]) -> list[str]:
    """16 integer columns following timestamp; no outcome-based trial discards."""
    if len(values) != 16:
        raise ValueError("expected sixteen integer columns")
    for value in values:
        bounded_int(value, 0, 2**63-1)
    for index in (3, 5, 6, 7):
        bounded_int(values[index], 0, 1)
    _, _, t1, c1, t2, c2, _, _, _, _, _, _, eA, eB, mA, mB = values
    starts = (5426350, 5425700)
    reasons = []
    if not starts[c1] <= t1 < starts[c1]+52450:
        reasons.append("first_herald_window")
    if not starts[c2]+250000 <= t2 < starts[c2]+250000+52450:
        reasons.append("second_herald_window")
    if c1 == c2:
        reasons.append("same_herald_detector")
    if any(0 < age <= 250 for age in (mA, mB)):
        reasons.append("recent_invalid_marker")
    if eA or eB:
        reasons.append("post_excitation_click")
    return reasons


def reduce_records(text: str) -> dict[str, object]:
    """Validate every released row and retain its original fields, order and reasons."""
    records: list[dict[str, object]] = []
    matrix = [[0]*4 for _ in range(4)]
    seen: set[str] = set()
    previous: datetime | None = None
    herald = markers = wins = accepted = 0
    for index, fields in enumerate(csv.reader(io.StringIO(text)), 1):
        if index > 4746 or len(fields) != 17:
            raise ValueError("released CSV requires seventeen columns and <=4746 rows")
        if not re.fullmatch(r"\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\.\d{6}", fields[0]):
            raise ValueError("invalid naive timestamp; no UTC conversion is inferred")
        timestamp = datetime.fromisoformat(fields[0])
        if fields[0] in seen or (previous is not None and timestamp <= previous):
            raise ValueError("duplicate or out-of-order released record")
        seen.add(fields[0])
        previous = timestamp
        if any(not re.fullmatch(r"\d{1,19}", item) for item in fields[1:]):
            raise ValueError("all event fields require nonnegative integer spelling")
        values = tuple(int(item) for item in fields[1:])
        reasons = filter_reasons(values)
        herald_ok = not any(reason in reasons for reason in
                            ("first_herald_window", "second_herald_window", "same_herald_detector"))
        herald += herald_ok
        markers += herald_ok and "recent_invalid_marker" not in reasons
        a, b = values[6:8]
        x, y = readout_sign(values[10]), readout_sign(values[11])
        win = (-1)**(a*b)*x*y == 1
        if not reasons:
            accepted += 1
            wins += win
            matrix[2*a+b][2*int(x == -1)+int(y == -1)] += 1
        records.append({"released_row": index, "source_fields": fields, "filter_reasons": reasons,
                        "accepted": not reasons, "a": a, "b": b, "x": x, "y": y, "win": win})
    if not records:
        raise ValueError("empty released CSV")
    return {"released_rows": len(records), "herald": herald, "also_markers": markers,
            "N": accepted, "K": wins, "matrix": matrix, "records": records,
            "accepted_row_ids": [row["released_row"] for row in records if row["accepted"]]}


PROVENANCE_PATHS = (Path(__file__), REGISTRY, ROOT / "scripts/replay_hensen2015.py",
                    ROOT / "Proofs/QMClosure/BellLocalTrialNull.lean",
                    ROOT / "theory_experiments/primitive_screen.py",
                    ROOT / "theory_experiments/__init__.py")


def source_hashes() -> dict[str, str]:
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in PROVENANCE_PATHS}


LOADED_SOURCE_HASHES = source_hashes()


def assert_loaded_sources() -> None:
    if source_hashes() != LOADED_SOURCE_HASHES:
        raise ValueError("Bell sources changed since import; restart from stable checkout")


def read_pinned_raw(path: Path) -> bytes:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as source:
        info = os.fstat(source.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size != RAW_SIZE:
            raise ValueError("raw file nonregular or wrong size; not physics rejection")
        raw = source.read(RAW_SIZE+1)
    if len(raw) != RAW_SIZE or hashlib.sha256(raw).hexdigest() != RAW_SHA256:
        raise ValueError("raw digest/size mismatch; not physics rejection")
    return raw


def replay(path: Path) -> dict[str, object]:
    assert_loaded_sources()
    sources = dict(LOADED_SOURCE_HASHES)
    # Construct the local null independently of the observations.
    candidate = BellLocalResponse("replay_local", EXPERIMENT, BRIDGE, 1, 1, 1, 1)
    prediction = predict_local_null(candidate)
    registry = reviewed_counts()
    raw = read_pinned_raw(path)
    reduced = reduce_records(raw.decode("ascii"))
    expected = object_fields(registry["reviewed_counts"])
    if {key: reduced[key] for key in expected} != expected:
        raise ValueError("raw reduction differs from reviewed counts; not physics rejection")
    assessment = assess_counts(cast(int, reduced["N"]), cast(int, reduced["K"]))
    report: dict[str, object] = {"schema": "idt-hensen2015-trial-replay/1", "execution_status": "complete",
            "shared_null_test_id": SHARED_NULL_TEST,
            "observation_origin": "pinned_released_candidate_records_reexecuted",
            "candidate_specification": candidate.specification(),
            "registry": registry, "source_sha256": sources,
            "recipe_sha256": hashlib.sha256(canonical_json(RECIPE).encode()).hexdigest(),
            "prediction": prediction, "reduction": reduced,
            "assessment": assessment,
            "candidate_verdict": "unconditional_verdict_not_established"}
    if source_hashes() != sources:
        raise ValueError("Bell sources changed during replay; no report returned")
    return report
