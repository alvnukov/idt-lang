"""Generate a packet map from a supplied opposition flag, then test its contract.

The six record labels and opposition involution are implementation coordinates.
Compatibility with the four even cube completions generates their packet edges.
An ordered two-mark controller and active recordwise coupling are supplied, not
derived by this adapter. A passive chart change has no physical data route under
the fixed-chart detector used here. No packet output table is accepted as input.

Calibration is explicit: one supplied S4 labeling, an existential S4 labeling,
or all S4 labelings. Existential success requires the SAME labeling to satisfy
both exchange and transparency. Failure concerns this extension, flag and
observation contract, never every model with three opposition pairs.

Eight packet observations form one atomic calibration test. max_cases counts
observations, not labels: a partial eight-observation block is not executed.
Existential completion by a witness need not exhaust all24 calibrations; that
coverage is reported separately. No research script is imported or executed.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations, product
from typing import Literal, TypeAlias

from theory_experiments import unsigned_pair_packet as packet
from theory_experiments.primitive_screen import (
    Check,
    Limits,
    Status,
    bounded_int,
    candidate_id,
    object_fields,
)

TupleI: TypeAlias = tuple[int, ...]
Extension: TypeAlias = Literal["transparent_spare", "flip_spare", "passive_chart"]
LabelContract: TypeAlias = Literal["fixed_calibration", "exists_s4", "all_s4"]
X = tuple(range(6))
WORDS = tuple(
    tuple(2 * i + bit for i, bit in enumerate(bits))
    for bits in product(range(2), repeat=3)
)
SHEET = tuple(word for word in WORDS if sum(x & 1 for x in word) % 2 == 0)
DUAL = tuple(tuple(x ^ 1 for x in word) for word in SHEET)
LITERAL_EDGES = tuple(tuple(i for i, word in enumerate(SHEET) if x in word) for x in X)
FLAGS = tuple((u, v) for u in X for v in X if u // 2 != v // 2)
G = tuple(
    tuple(2 * p[x // 2] + ((x & 1) ^ flips[x // 2]) for x in X)
    for p, flips in product(permutations(range(3)), product(range(2), repeat=3))
)
S4 = tuple(permutations(range(4)))


def extend(u: int, v: int, flip: bool) -> TupleI:
    bounded_int(u, 0, 5)
    bounded_int(v, 0, 5)
    if (u, v) not in FLAGS or type(flip) is not bool:
        raise ValueError(
            "two marks on different opposition pairs and boolean spare flip required"
        )
    route = {u: v, v: u ^ 1, u ^ 1: v ^ 1, v ^ 1: u}
    return tuple(route.get(x, x ^ int(flip)) for x in X)


def chart(perm: TupleI) -> tuple[bool, TupleI]:
    if perm not in G:
        raise ValueError("opposition-preserving permutation required")
    image = tuple(tuple(sorted(perm[x] for x in word)) for word in SHEET)
    dual = set(image) == set(DUAL)
    vertices = DUAL if dual else SHEET
    return dual, tuple(vertices.index(word) for word in image)


def validate_labels(labels: TupleI) -> None:
    if not isinstance(labels, tuple) or len(labels) != 4:
        raise ValueError("immutable four-leg calibration required")
    for value in labels:
        bounded_int(value, 0, 3)
    if sorted(labels) != list(range(4)):
        raise ValueError("calibration must be an S4 permutation")


def literal_packets(labels: TupleI) -> TupleI:
    validate_labels(labels)
    return tuple(
        packet.INDEX[min(labels[a], labels[c]), max(labels[a], labels[c])]
        for a, c in LITERAL_EDGES
    )


def generate_table(
    flag: tuple[int, int], extension: Extension, labels: TupleI
) -> packet.Table:
    if extension not in ("transparent_spare", "flip_spare", "passive_chart"):
        raise ValueError("unsupported data_extension")
    selected = extend(*flag, extension == "flip_spare")
    route = X if extension == "passive_chart" else selected
    encoding = literal_packets(labels)
    return tuple(encoding[route[encoding.index(i)]] for i in packet.ID)


@dataclass(frozen=True)
class OppositionFlag:
    id: str
    flag: tuple[int, int]
    data_extension: Extension
    observation_contract: packet.ObservationContract
    label_contract: LabelContract
    leg_labels: TupleI | None = None

    def __post_init__(self) -> None:
        candidate_id(self.id)
        if not isinstance(self.flag, tuple) or len(self.flag) != 2:
            raise ValueError("immutable ordered two-mark flag required")
        for mark in self.flag:
            bounded_int(mark, 0, 5)
        if self.flag not in FLAGS:
            raise ValueError("flag marks must lie on different opposition pairs")
        if self.data_extension not in (
            "transparent_spare",
            "flip_spare",
            "passive_chart",
        ):
            raise ValueError("unsupported data_extension")
        if self.observation_contract not in ("resolved_packets", "port_totals"):
            raise ValueError("unsupported observation_contract")
        if self.label_contract not in ("fixed_calibration", "exists_s4", "all_s4"):
            raise ValueError("unsupported label_contract")
        if self.label_contract == "fixed_calibration":
            if self.leg_labels is None:
                raise ValueError("fixed_calibration requires leg_labels")
            validate_labels(self.leg_labels)
        elif self.leg_labels is not None:
            raise ValueError(
                "quantified calibration must not supply hidden fixed leg_labels"
            )

    def specification(self) -> dict[str, object]:
        result: dict[str, object] = {
            "id": self.id,
            "family": "opposition_flag",
            "flag": list(self.flag),
            "data_extension": self.data_extension,
            "observation_contract": self.observation_contract,
            "label_contract": self.label_contract,
        }
        if self.leg_labels is not None:
            result["leg_labels"] = list(self.leg_labels)
        return result


def parse_opposition_flag(value: object) -> OppositionFlag:
    row = object_fields(value)
    fields = {
        "id",
        "family",
        "flag",
        "data_extension",
        "observation_contract",
        "label_contract",
    }
    if row.get("label_contract") == "fixed_calibration":
        fields.add("leg_labels")
    object_fields(row, fields)
    if row["family"] != "opposition_flag":
        raise ValueError("expected opposition_flag family")
    flag = row["flag"]
    if not isinstance(flag, list) or len(flag) != 2:
        raise ValueError("flag must be a two-entry JSON array")
    extension = row["data_extension"]
    if extension not in ("transparent_spare", "flip_spare", "passive_chart"):
        raise ValueError("unsupported data_extension")
    contract = row["observation_contract"]
    if contract not in ("resolved_packets", "port_totals"):
        raise ValueError("unsupported observation_contract")
    quantifier = row["label_contract"]
    if quantifier not in ("fixed_calibration", "exists_s4", "all_s4"):
        raise ValueError("unsupported label_contract")
    labels = None
    if quantifier == "fixed_calibration":
        raw_labels = row["leg_labels"]
        if not isinstance(raw_labels, list) or len(raw_labels) != 4:
            raise ValueError("leg_labels must be a four-entry JSON array")
        labels = tuple(bounded_int(x, 0, 3) for x in raw_labels)
    return OppositionFlag(
        candidate_id(row["id"]),
        (bounded_int(flag[0], 0, 5), bounded_int(flag[1], 0, 5)),
        "transparent_spare"
        if extension == "transparent_spare"
        else "flip_spare"
        if extension == "flip_spare"
        else "passive_chart",
        "resolved_packets" if contract == "resolved_packets" else "port_totals",
        "fixed_calibration"
        if quantifier == "fixed_calibration"
        else "exists_s4"
        if quantifier == "exists_s4"
        else "all_s4",
        labels,
    )


ASSUMPTIONS = (
    "three_binary_opposition_pairs_and_compatibility_with_one_fixed_cube_sheet",
    "supplied_ordered_flag_on_distinct_pairs_and_no_retrace_controller_successor",
    "active_recordwise_coupling_only_for_transparent_or_flip_spare_extensions",
    "passive_chart_change_is_not_an_active_route_under_fixed_chart_detection",
    "all_six_packets_individually_preparable_and_labels_persistent_across_ticks",
    "second_tick_generated_after_controller_update_v_opposite_u",
    "supplied_two_tick_exchange_02_13_and_equal_input_transparency_requirements",
    "finite_extension_and_contract_screen_not_all_three_pair_models_or_experimental_data",
)


def calibration_test(model: OppositionFlag, labels: TupleI) -> dict[str, object]:
    """Always generate the table; all eight observations share this calibration."""
    table = generate_table(model.flag, model.data_extension, labels)
    next_flag = (model.flag[1], model.flag[0] ^ 1)
    second_table = generate_table(next_flag, model.data_extension, labels)
    twice = packet.after(second_table, table)
    failures: list[dict[str, object]] = []
    for ticks, indices, actual_table, required in (
        (2, packet.ID, twice, packet.SWAP),
        (1, packet.FIX, table, packet.ID),
    ):
        for index in indices:
            actual, target = actual_table[index], required[index]
            observed = (
                (actual,)
                if model.observation_contract == "resolved_packets"
                else (packet.BY_PORT[actual], 2 - packet.BY_PORT[actual])
            )
            desired = (
                (target,)
                if model.observation_contract == "resolved_packets"
                else (packet.BY_PORT[target], 2 - packet.BY_PORT[target])
            )
            if observed != desired:
                failures.append(
                    {
                        "ticks": ticks,
                        "input_packet": index,
                        "input_legs": list(packet.EDGES[index]),
                        "observed_actual": list(observed),
                        "observed_required": list(desired),
                    }
                )
    return {
        "leg_labels": list(labels),
        "generated_packet_table": list(table),
        "second_tick_generated_packet_table": list(second_table),
        "observations_checked": 8,
        "satisfies_both_requirements": not failures,
        "first_failure": failures[0] if failures else None,
    }


def evaluate_opposition_flag(
    model: OppositionFlag, limits: Limits
) -> tuple[tuple[Check, ...], dict[str, object]]:
    labels_domain = (model.leg_labels,) if model.leg_labels is not None else S4
    records: list[dict[str, object]] = []
    status: Status = "inconclusive"
    stop_reason = "max_cases_requires_complete_calibration"
    witness: dict[str, object] | None = None
    viable: list[int] | None = None
    for labels in labels_domain:
        if 8 * (len(records) + 1) > limits.max_cases:
            break
        record = calibration_test(model, labels)
        records.append(record)
        accepted = record["satisfies_both_requirements"] is True
        if model.label_contract == "exists_s4" and accepted:
            viable = list(labels)
            status, stop_reason = (
                "no_counterexample_within_bounds",
                "existential_witness",
            )
            break
        if model.label_contract != "exists_s4" and not accepted:
            status, stop_reason = (
                "counterexample",
                "selected_calibration_counterexample",
            )
            witness = {
                "inputs": record,
                "actual": "1",
                "required": "zero_packet_observation_mismatches",
            }
            break
    else:
        if model.label_contract == "exists_s4":
            status, stop_reason = "counterexample", "all_s4_calibrations_eliminated"
            witness = {
                "inputs": {
                    "label_contract": "exists_s4",
                    "failed_calibrations": records,
                },
                "actual": "0",
                "required": "at_least_one_calibration_satisfying_both_requirements",
            }
        else:
            status, stop_reason = (
                "no_counterexample_within_bounds",
                "all_selected_calibrations_checked",
            )
    assumptions = ASSUMPTIONS + (
        f"label_contract_{model.label_contract}",
        f"observation_contract_{model.observation_contract}",
    )
    check = Check(
        "generated_opposition_packet_contract",
        status,
        8 * len(records),
        8 * len(labels_domain),
        "one_common_calibration_for_both_packet_requirements_under_declared_quantifier",
        assumptions,
        witness,
    )
    active = model.data_extension != "passive_chart"
    clock_route = extend(*model.flag, model.data_extension == "flip_spare")
    swapped, ports = chart(clock_route)
    return (check,), {
        "adapter_status": "finite_generated_opposition_flag_screen",
        "scientific_status": "unassessed",
        "micro_flag": list(model.flag),
        "next_controller_flag": [model.flag[1], model.flag[0] ^ 1],
        "data_extension": model.data_extension,
        "active_record_coupling": active,
        "physical_record_route": list(clock_route if active else X),
        "controller_extension_chart_diagnostic": {
            "exchanges_sheets": swapped,
            "port_permutation": list(ports),
            "not_a_physical_route_when_passive": not active,
        },
        "label_contract": model.label_contract,
        "observation_contract": model.observation_contract,
        "packet_order": [list(edge) for edge in packet.EDGES],
        "literal_compatibility_edges": [list(edge) for edge in LITERAL_EDGES],
        "two_tick_leg_exchange": [2, 3, 0, 1],
        "transparent_input_packets": list(packet.FIX),
        "calibrations": records,
        "viable_calibration": viable,
        "calibration_domain_size": len(labels_domain),
        "domain_exhausted": len(records) == len(labels_domain),
        "not_exercised_calibrations": [
            list(labels) for labels in labels_domain[len(records) :]
        ],
        "quantified_requirement_resolved": status != "inconclusive",
        "stop_reason": stop_reason,
        "budget_semantics": "max_cases_packet_observations_in_atomic_eight_observation_calibration_blocks",
        "observations_per_calibration": {
            "two_tick_all_input_packets": list(packet.ID),
            "one_tick_transparency_inputs": list(packet.FIX),
        },
        "quantifier_boundary": "exists_s4_is_not_all_s4_or_a_claim_about_unknown_physical_calibration",
        "rejection_boundary": "only_this_flag_extension_and_observation_contract_not_all_three_pair_models",
        "missing_bridges": [
            "physical_controller_preparation",
            "active_record_coupling_and_spare_behavior",
            "fixed_chart_detector_and_label_calibration",
            "physical_packet_requirements",
        ],
        "untested": [
            "natural_backtrack_variant",
            "arbitrary_three_pair_dynamics",
            "event_probabilities",
            "experimental_data",
            "QM_closure",
        ],
        "unused_limits": ["coefficient_radius", "reference_radius", "max_copies"],
    }
