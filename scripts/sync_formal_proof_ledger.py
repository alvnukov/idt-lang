from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TextIO


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from theory_verifier.core import (  # noqa: E402
    FINITE_GATE_CHECKS,
    FDC_CLOSURE_RULE,
    FDC_FORBIDDEN_UPGRADES,
    FDC_REQUIRED_NEGATIVE_CONTROLS,
    FDC_REQUIRED_OPEN_OBLIGATIONS,
    FDC_TARGET_PRINCIPLE,
    IDT_CORE_CLAIM_ROLE_REGISTRY,
    IDT_CORE_ROUTE_FAMILY_REGISTRY,
    IDT_PRIMITIVE_CORE_ALLOWED_DEPENDENCIES,
    IDT_PRIMITIVE_CORE_FORBIDDEN_REFS,
    IDT_PRIMITIVE_CORE_IMPORT_OBLIGATION_TARGETS,
    IDT_PRIMITIVE_CORE_REQUIRED_LAWS,
    QM_EXPERIMENT_REQUIRED_PRIMITIVES,
    FiniteGate,
    Manifest,
    idt_core_gate_type_registry_digest,
    idt_core_registry_digest,
    iter_formal_claims,
    load_manifest,
)

DEFAULT_MANIFEST = ROOT / "theory_verifier_manifest_v6_0.json"
DEFAULT_LEAN_PATH = ROOT / "Proofs" / "IDTCore.lean"


@dataclass(frozen=True)
class RegistryWitness:
    identifier: str
    source: str
    items: tuple[str, ...]
    expected_count: int
    expected_digest: str


@dataclass(frozen=True)
class ArityWitness:
    identifier: str
    route_family: str
    arity_bound: int
    uniform_bound: int
    status: str


@dataclass(frozen=True)
class GeneratorWitness:
    identifier: str
    route_family: str
    generator_refs: tuple[str, ...]
    status: str


@dataclass(frozen=True)
class NoNewEffectWitness:
    identifier: str
    closed_over_sources: tuple[str, ...]
    new_primitive_effects: tuple[str, ...]
    status: str


@dataclass(frozen=True)
class JointOnlyRejectionWitness:
    identifier: str
    status: str
    scope: str
    assumptions: tuple[str, ...]
    separator_refs: tuple[str, ...]
    rejected_witness_refs: tuple[str, ...]
    open_gap: str


@dataclass(frozen=True)
class FormalAssumptionWitness:
    identifier: str
    status: str
    evidence_refs: tuple[str, ...]
    open_gap: str


@dataclass(frozen=True)
class PrimitiveCoreWitness:
    identifier: str
    primitive_status: str
    carrier_status: str
    laws: tuple[str, ...]
    allowed_dependencies: tuple[str, ...]
    forbidden_ref_hits: tuple[str, ...]


@dataclass(frozen=True)
class ImportObligationWitness:
    import_id: str
    obligation_kind: str
    target: str
    required_status: str
    target_refactor: str
    proof_boundary: str


@dataclass(frozen=True)
class FDCConditionWitness:
    identifier: str
    status: str
    evidence_refs: tuple[str, ...]
    open_gap: str
    forbidden_ref_hits: tuple[str, ...]


@dataclass(frozen=True)
class FDCNegativeControlWitness:
    identifier: str
    expected_result: str
    evidence_refs: tuple[str, ...]
    retained_boundary: str


@dataclass(frozen=True)
class FDCOpenObligationWitness:
    identifier: str
    required_status: str


def lean_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def formal_claim_refs(manifest: Manifest) -> tuple[str, ...]:
    return tuple(sorted({claim.reference for claim in iter_formal_claims(manifest)}))


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def gate_by_id(manifest: Manifest, identifier: str) -> FiniteGate:
    matches = [gate for gate in manifest.finite_gates if gate.identifier == identifier]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one finite gate {identifier!r}")
    return matches[0]


def require_mapping(value: object, field: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{field} must be an object")
    return value


def require_list(value: object, field: str) -> list[object]:
    if not isinstance(value, list):
        raise ValueError(f"{field} must be a list")
    return value


def require_string(value: object, field: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field} must be a string")
    return value


def require_int(value: object, field: str) -> int:
    if not isinstance(value, int):
        raise ValueError(f"{field} must be an integer")
    return value


def require_string_tuple(value: object, field: str) -> tuple[str, ...]:
    return tuple(require_string(item, f"{field}[]") for item in require_list(value, field))


def component_status(gate: FiniteGate, component_id: str, status_field: str) -> str:
    for index, raw_component in enumerate(require_list(gate.payload.get("components"), f"{gate.identifier}.components")):
        component = require_mapping(raw_component, f"{gate.identifier}.components[{index}]")
        if component.get("id") == component_id:
            return require_string(component.get(status_field), f"{gate.identifier}.{component_id}.{status_field}")
    raise ValueError(f"{gate.identifier}: missing component {component_id!r}")


def assumption_witnesses(manifest: Manifest) -> tuple[FormalAssumptionWitness, ...]:
    gate = gate_by_id(manifest, "uniform_witness_bound_assumption_frontier_demo")
    witnesses: list[FormalAssumptionWitness] = []
    for index, raw_assumption in enumerate(require_list(gate.payload.get("assumptions"), f"{gate.identifier}.assumptions")):
        assumption = require_mapping(raw_assumption, f"{gate.identifier}.assumptions[{index}]")
        status = require_string(assumption.get("status"), f"{gate.identifier}.assumptions[{index}].status")
        if status != "formal_proof":
            continue
        witnesses.append(
            FormalAssumptionWitness(
                identifier=require_string(assumption.get("id"), f"{gate.identifier}.assumptions[{index}].id"),
                status=status,
                evidence_refs=require_string_tuple(
                    assumption.get("evidence_refs", []),
                    f"{gate.identifier}.assumptions[{index}].evidence_refs",
                ),
                open_gap=require_string(assumption.get("open_gap"), f"{gate.identifier}.assumptions[{index}].open_gap"),
            )
        )
    return tuple(witnesses)


def registry_witnesses(manifest: Manifest) -> tuple[RegistryWitness, ...]:
    signature_gate = gate_by_id(manifest, "idt_core_signature_registry_audit_demo")
    gate_type_gate = gate_by_id(manifest, "idt_core_gate_type_registry_audit_demo")
    registry_items = {
        "finite_primitive_sort_vocabulary": tuple(QM_EXPERIMENT_REQUIRED_PRIMITIVES),
        "finite_claim_role_vocabulary": tuple(IDT_CORE_CLAIM_ROLE_REGISTRY),
        "finite_route_family_registry": tuple(IDT_CORE_ROUTE_FAMILY_REGISTRY),
    }
    witnesses: list[RegistryWitness] = []
    for index, raw_component in enumerate(
        require_list(signature_gate.payload.get("component_registries"), f"{signature_gate.identifier}.component_registries")
    ):
        component = require_mapping(raw_component, f"{signature_gate.identifier}.component_registries[{index}]")
        component_id = require_string(component.get("component_id"), f"{signature_gate.identifier}.component_id")
        items = registry_items[component_id]
        witnesses.append(
            RegistryWitness(
                identifier=component_id,
                source=require_string(component.get("registry_source"), f"{signature_gate.identifier}.{component_id}.source"),
                items=items,
                expected_count=require_int(
                    component.get("expected_item_count"),
                    f"{signature_gate.identifier}.{component_id}.expected_item_count",
                ),
                expected_digest=require_string(
                    component.get("expected_item_digest"),
                    f"{signature_gate.identifier}.{component_id}.expected_item_digest",
                ),
            )
        )
    gate_types = tuple(sorted(FINITE_GATE_CHECKS))
    witnesses.append(
        RegistryWitness(
            identifier="finite_gate_type_registry",
            source=require_string(gate_type_gate.payload.get("registry_source"), f"{gate_type_gate.identifier}.registry_source"),
            items=gate_types,
            expected_count=require_int(gate_type_gate.payload.get("expected_gate_type_count"), "expected_gate_type_count"),
            expected_digest=require_string(
                gate_type_gate.payload.get("expected_gate_type_digest"),
                f"{gate_type_gate.identifier}.expected_gate_type_digest",
            ),
        )
    )
    return tuple(sorted(witnesses, key=lambda witness: witness.identifier))


def arity_witnesses(manifest: Manifest) -> tuple[ArityWitness, ...]:
    audit_gate = gate_by_id(manifest, "idt_core_route_grammar_audit_demo")
    frontier_gate = gate_by_id(manifest, "idt_core_bounded_arity_frontier_demo")
    uniform_bound = require_int(audit_gate.payload.get("uniform_bound"), f"{audit_gate.identifier}.uniform_bound")
    witnesses: list[ArityWitness] = []
    for index, raw_component in enumerate(
        require_list(audit_gate.payload.get("arity_components"), f"{audit_gate.identifier}.arity_components")
    ):
        component = require_mapping(raw_component, f"{audit_gate.identifier}.arity_components[{index}]")
        component_id = require_string(component.get("id"), f"{audit_gate.identifier}.arity_components[{index}].id")
        witnesses.append(
            ArityWitness(
                identifier=component_id,
                route_family=require_string(component.get("route_family"), f"{audit_gate.identifier}.{component_id}.route_family"),
                arity_bound=require_int(component.get("arity_bound"), f"{audit_gate.identifier}.{component_id}.arity_bound"),
                uniform_bound=uniform_bound,
                status=component_status(frontier_gate, component_id, "status"),
            )
        )
    return tuple(witnesses)


def generator_witnesses(manifest: Manifest) -> tuple[GeneratorWitness, ...]:
    audit_gate = gate_by_id(manifest, "idt_core_route_grammar_audit_demo")
    frontier_gate = gate_by_id(manifest, "idt_core_route_generator_basis_frontier_demo")
    witnesses: list[GeneratorWitness] = []
    for index, raw_component in enumerate(
        require_list(audit_gate.payload.get("generator_components"), f"{audit_gate.identifier}.generator_components")
    ):
        component = require_mapping(raw_component, f"{audit_gate.identifier}.generator_components[{index}]")
        component_id = require_string(component.get("id"), f"{audit_gate.identifier}.generator_components[{index}].id")
        witnesses.append(
            GeneratorWitness(
                identifier=component_id,
                route_family=require_string(component.get("route_family"), f"{audit_gate.identifier}.{component_id}.route_family"),
                generator_refs=require_string_tuple(
                    component.get("generator_refs", []),
                    f"{audit_gate.identifier}.{component_id}.generator_refs",
                ),
                status=component_status(frontier_gate, component_id, "status"),
            )
        )
    return tuple(witnesses)


def no_new_effect_witnesses(manifest: Manifest) -> tuple[NoNewEffectWitness, ...]:
    audit_gate = gate_by_id(manifest, "idt_core_route_grammar_audit_demo")
    frontier_gate = gate_by_id(manifest, "idt_core_no_new_primitive_effects_frontier_demo")
    witnesses: list[NoNewEffectWitness] = []
    for index, raw_component in enumerate(
        require_list(audit_gate.payload.get("no_new_effect_components"), f"{audit_gate.identifier}.no_new_effect_components")
    ):
        component = require_mapping(raw_component, f"{audit_gate.identifier}.no_new_effect_components[{index}]")
        component_id = require_string(component.get("id"), f"{audit_gate.identifier}.no_new_effect_components[{index}].id")
        witnesses.append(
            NoNewEffectWitness(
                identifier=component_id,
                closed_over_sources=require_string_tuple(
                    component.get("closed_over_sources", []),
                    f"{audit_gate.identifier}.{component_id}.closed_over_sources",
                ),
                new_primitive_effects=require_string_tuple(
                    component.get("new_primitive_effects", []),
                    f"{audit_gate.identifier}.{component_id}.new_primitive_effects",
                ),
                status=component_status(frontier_gate, component_id, "status"),
            )
        )
    return tuple(witnesses)


def joint_only_rejection_witness(manifest: Manifest) -> JointOnlyRejectionWitness:
    semantic_gate = gate_by_id(manifest, "idt_core_semantic_no_new_effects_audit_demo")
    for index, raw_component in enumerate(require_list(semantic_gate.payload.get("components"), f"{semantic_gate.identifier}.components")):
        component = require_mapping(raw_component, f"{semantic_gate.identifier}.components[{index}]")
        if component.get("id") != "joint_only_invariant_rejection":
            continue
        return JointOnlyRejectionWitness(
            identifier="joint_only_invariant_rejection",
            status=require_string(component.get("status"), f"{semantic_gate.identifier}.joint_only_invariant_rejection.status"),
            scope=require_string(component.get("scope"), f"{semantic_gate.identifier}.joint_only_invariant_rejection.scope"),
            assumptions=require_string_tuple(
                component.get("assumptions", []),
                f"{semantic_gate.identifier}.joint_only_invariant_rejection.assumptions",
            ),
            separator_refs=require_string_tuple(
                component.get("separator_refs", []),
                f"{semantic_gate.identifier}.joint_only_invariant_rejection.separator_refs",
            ),
            rejected_witness_refs=require_string_tuple(
                component.get("rejected_witness_refs", []),
                f"{semantic_gate.identifier}.joint_only_invariant_rejection.rejected_witness_refs",
            ),
            open_gap=require_string(component.get("open_gap"), f"{semantic_gate.identifier}.joint_only_invariant_rejection.open_gap"),
        )
    raise ValueError(f"{semantic_gate.identifier}: missing joint_only_invariant_rejection")


def primitive_core_witnesses(manifest: Manifest) -> tuple[PrimitiveCoreWitness, ...]:
    gate = gate_by_id(manifest, "idt_primitive_core_contract_demo")
    witnesses: list[PrimitiveCoreWitness] = []
    forbidden_refs = set(IDT_PRIMITIVE_CORE_FORBIDDEN_REFS)
    for index, raw_primitive in enumerate(require_list(gate.payload.get("primitive_core"), f"{gate.identifier}.primitive_core")):
        primitive = require_mapping(raw_primitive, f"{gate.identifier}.primitive_core[{index}]")
        primitive_id = require_string(primitive.get("id"), f"{gate.identifier}.primitive_core[{index}].id")
        laws = require_string_tuple(primitive.get("laws", []), f"{gate.identifier}.{primitive_id}.laws")
        allowed_dependencies = require_string_tuple(
            primitive.get("allowed_dependencies", []),
            f"{gate.identifier}.{primitive_id}.allowed_dependencies",
        )
        scanned = (primitive_id, *laws, *allowed_dependencies)
        witnesses.append(
            PrimitiveCoreWitness(
                identifier=primitive_id,
                primitive_status=require_string(
                    primitive.get("primitive_status"),
                    f"{gate.identifier}.{primitive_id}.primitive_status",
                ),
                carrier_status=require_string(
                    primitive.get("carrier_status"),
                    f"{gate.identifier}.{primitive_id}.carrier_status",
                ),
                laws=laws,
                allowed_dependencies=allowed_dependencies,
                forbidden_ref_hits=tuple(sorted(forbidden_ref for forbidden_ref in forbidden_refs if forbidden_ref in scanned)),
            )
        )
    return tuple(witnesses)


def import_obligation_witnesses(manifest: Manifest) -> tuple[ImportObligationWitness, ...]:
    gate = gate_by_id(manifest, "idt_primitive_core_contract_demo")
    witnesses: list[ImportObligationWitness] = []
    for index, raw_obligation in enumerate(
        require_list(gate.payload.get("import_obligations"), f"{gate.identifier}.import_obligations")
    ):
        obligation = require_mapping(raw_obligation, f"{gate.identifier}.import_obligations[{index}]")
        import_id = require_string(obligation.get("import_id"), f"{gate.identifier}.import_obligations[{index}].import_id")
        expected_kind, expected_target = IDT_PRIMITIVE_CORE_IMPORT_OBLIGATION_TARGETS[import_id]
        obligation_kind = require_string(
            obligation.get("obligation_kind"),
            f"{gate.identifier}.{import_id}.obligation_kind",
        )
        target = require_string(obligation.get("target"), f"{gate.identifier}.{import_id}.target")
        if obligation_kind != expected_kind or target != expected_target:
            raise ValueError(f"{gate.identifier}: import obligation target drift for {import_id}")
        witnesses.append(
            ImportObligationWitness(
                import_id=import_id,
                obligation_kind=obligation_kind,
                target=target,
                required_status=require_string(
                    obligation.get("required_status"),
                    f"{gate.identifier}.{import_id}.required_status",
                ),
                target_refactor=require_string(
                    obligation.get("target_refactor"),
                    f"{gate.identifier}.{import_id}.target_refactor",
                ),
                proof_boundary=require_string(
                    obligation.get("proof_boundary"),
                    f"{gate.identifier}.{import_id}.proof_boundary",
                ),
            )
        )
    return tuple(witnesses)


def fdc_condition_witnesses(manifest: Manifest) -> tuple[FDCConditionWitness, ...]:
    gate = gate_by_id(manifest, "facticizable_distinguishability_closure_frontier_demo")
    forbidden_refs = set(require_string_tuple(gate.payload.get("forbidden_import_refs", []), f"{gate.identifier}.forbidden_import_refs"))
    witnesses: list[FDCConditionWitness] = []
    for index, raw_condition in enumerate(require_list(gate.payload.get("conditions"), f"{gate.identifier}.conditions")):
        condition = require_mapping(raw_condition, f"{gate.identifier}.conditions[{index}]")
        condition_id = require_string(condition.get("id"), f"{gate.identifier}.conditions[{index}].id")
        status = require_string(condition.get("status"), f"{gate.identifier}.{condition_id}.status")
        evidence_refs = require_string_tuple(condition.get("evidence_refs", []), f"{gate.identifier}.{condition_id}.evidence_refs")
        open_gap = require_string(condition.get("open_gap"), f"{gate.identifier}.{condition_id}.open_gap")
        scanned = (condition_id, status, open_gap, *evidence_refs)
        witnesses.append(
            FDCConditionWitness(
                identifier=condition_id,
                status=status,
                evidence_refs=evidence_refs,
                open_gap=open_gap,
                forbidden_ref_hits=tuple(sorted(forbidden_ref for forbidden_ref in forbidden_refs if forbidden_ref in scanned)),
            )
        )
    return tuple(witnesses)


def fdc_negative_control_witnesses(manifest: Manifest) -> tuple[FDCNegativeControlWitness, ...]:
    gate = gate_by_id(manifest, "facticizable_distinguishability_closure_frontier_demo")
    witnesses: list[FDCNegativeControlWitness] = []
    for index, raw_control in enumerate(require_list(gate.payload.get("negative_controls"), f"{gate.identifier}.negative_controls")):
        control = require_mapping(raw_control, f"{gate.identifier}.negative_controls[{index}]")
        control_id = require_string(control.get("id"), f"{gate.identifier}.negative_controls[{index}].id")
        witnesses.append(
            FDCNegativeControlWitness(
                identifier=control_id,
                expected_result=require_string(control.get("expected_result"), f"{gate.identifier}.{control_id}.expected_result"),
                evidence_refs=require_string_tuple(control.get("evidence_refs", []), f"{gate.identifier}.{control_id}.evidence_refs"),
                retained_boundary=require_string(
                    control.get("retained_boundary"),
                    f"{gate.identifier}.{control_id}.retained_boundary",
                ),
            )
        )
    return tuple(witnesses)


def fdc_open_obligation_witnesses(manifest: Manifest) -> tuple[FDCOpenObligationWitness, ...]:
    gate = gate_by_id(manifest, "facticizable_distinguishability_closure_frontier_demo")
    witnesses: list[FDCOpenObligationWitness] = []
    for index, raw_obligation in enumerate(require_list(gate.payload.get("open_obligations"), f"{gate.identifier}.open_obligations")):
        obligation = require_mapping(raw_obligation, f"{gate.identifier}.open_obligations[{index}]")
        witnesses.append(
            FDCOpenObligationWitness(
                identifier=require_string(obligation.get("id"), f"{gate.identifier}.open_obligations[{index}].id"),
                required_status=require_string(
                    obligation.get("required_status"),
                    f"{gate.identifier}.open_obligations[{index}].required_status",
                ),
            )
        )
    return tuple(witnesses)


def lean_list(items: Sequence[str], indent: str = "    ") -> str:
    if not items:
        return "[]"
    lines = ["["]
    for index, item in enumerate(items):
        suffix = "," if index < len(items) - 1 else ""
        lines.append(f"{indent}{lean_string(item)}{suffix}")
    lines.append("  ]")
    return "\n".join(lines)


def render_registry_witness(witness: RegistryWitness) -> str:
    if witness.identifier == "finite_gate_type_registry":
        computed_digest = idt_core_gate_type_registry_digest(witness.items)
    else:
        computed_digest = idt_core_registry_digest(witness.items)
    return f"""  {{
    id := {lean_string(witness.identifier)},
    source := {lean_string(witness.source)},
    items := {lean_list(witness.items, "      ")},
    expectedCount := {witness.expected_count},
    expectedDigest := {lean_string(witness.expected_digest)},
    computedDigest := {lean_string(computed_digest)}
  }}"""


def render_arity_witness(witness: ArityWitness) -> str:
    return f"""  {{
    id := {lean_string(witness.identifier)},
    routeFamily := {lean_string(witness.route_family)},
    arityBound := {witness.arity_bound},
    uniformBound := {witness.uniform_bound},
    status := {lean_string(witness.status)}
  }}"""


def render_generator_witness(witness: GeneratorWitness) -> str:
    return f"""  {{
    id := {lean_string(witness.identifier)},
    routeFamily := {lean_string(witness.route_family)},
    generatorRefs := {lean_list(witness.generator_refs, "      ")},
    status := {lean_string(witness.status)}
  }}"""


def render_no_new_effect_witness(witness: NoNewEffectWitness) -> str:
    return f"""  {{
    id := {lean_string(witness.identifier)},
    closedOverSources := {lean_list(witness.closed_over_sources, "      ")},
    newPrimitiveEffects := {lean_list(witness.new_primitive_effects, "      ")},
    status := {lean_string(witness.status)}
  }}"""


def render_formal_assumption_witness(witness: FormalAssumptionWitness) -> str:
    return f"""  {{
    id := {lean_string(witness.identifier)},
    status := {lean_string(witness.status)},
    evidenceRefs := {lean_list(witness.evidence_refs, "      ")},
    openGap := {lean_string(witness.open_gap)}
  }}"""


def render_primitive_core_witness(witness: PrimitiveCoreWitness) -> str:
    expected_laws = IDT_PRIMITIVE_CORE_REQUIRED_LAWS[witness.identifier]
    return f"""  {{
    id := {lean_string(witness.identifier)},
    primitiveStatus := {lean_string(witness.primitive_status)},
    carrierStatus := {lean_string(witness.carrier_status)},
    laws := {lean_list(witness.laws, "      ")},
    expectedLaws := {lean_list(expected_laws, "      ")},
    allowedDependencies := {lean_list(witness.allowed_dependencies, "      ")},
    expectedAllowedDependencies := {lean_list(IDT_PRIMITIVE_CORE_ALLOWED_DEPENDENCIES, "      ")},
    forbiddenRefHits := {lean_list(witness.forbidden_ref_hits, "      ")}
  }}"""


def render_import_obligation_witness(witness: ImportObligationWitness) -> str:
    return f"""  {{
    importId := {lean_string(witness.import_id)},
    obligationKind := {lean_string(witness.obligation_kind)},
    target := {lean_string(witness.target)},
    requiredStatus := {lean_string(witness.required_status)},
    targetRefactor := {lean_string(witness.target_refactor)},
    proofBoundary := {lean_string(witness.proof_boundary)}
  }}"""


def render_fdc_condition_witness(witness: FDCConditionWitness) -> str:
    return f"""  {{
    id := {lean_string(witness.identifier)},
    status := {lean_string(witness.status)},
    expectedStatus := "candidate_principle",
    evidenceRefs := {lean_list(witness.evidence_refs, "      ")},
    openGap := {lean_string(witness.open_gap)},
    forbiddenRefHits := {lean_list(witness.forbidden_ref_hits, "      ")}
  }}"""


def render_fdc_negative_control_witness(witness: FDCNegativeControlWitness) -> str:
    expected_result = FDC_REQUIRED_NEGATIVE_CONTROLS[witness.identifier]
    return f"""  {{
    id := {lean_string(witness.identifier)},
    expectedResult := {lean_string(witness.expected_result)},
    requiredResult := {lean_string(expected_result)},
    evidenceRefs := {lean_list(witness.evidence_refs, "      ")},
    retainedBoundary := {lean_string(witness.retained_boundary)}
  }}"""


def render_fdc_open_obligation_witness(witness: FDCOpenObligationWitness) -> str:
    required_status = FDC_REQUIRED_OPEN_OBLIGATIONS[witness.identifier]
    return f"""  {{
    id := {lean_string(witness.identifier)},
    requiredStatus := {lean_string(witness.required_status)},
    expectedRequiredStatus := {lean_string(required_status)}
  }}"""


def render_comma_list(items: Sequence[str]) -> str:
    return ",\n".join(items)


def render_lean(manifest: Manifest) -> str:
    claim_refs = formal_claim_refs(manifest)
    registry_data = registry_witnesses(manifest)
    arity_data = arity_witnesses(manifest)
    generator_data = generator_witnesses(manifest)
    no_new_effect_data = no_new_effect_witnesses(manifest)
    assumption_data = assumption_witnesses(manifest)
    primitive_core_data = primitive_core_witnesses(manifest)
    import_obligation_data = import_obligation_witnesses(manifest)
    fdc_condition_data = fdc_condition_witnesses(manifest)
    fdc_negative_control_data = fdc_negative_control_witnesses(manifest)
    fdc_open_obligation_data = fdc_open_obligation_witnesses(manifest)
    joint_witness = joint_only_rejection_witness(manifest)
    rendered_claim_refs = lean_list(claim_refs)
    rendered_registry_witnesses = render_comma_list([render_registry_witness(witness) for witness in registry_data])
    rendered_arity_witnesses = render_comma_list([render_arity_witness(witness) for witness in arity_data])
    rendered_generator_witnesses = render_comma_list([render_generator_witness(witness) for witness in generator_data])
    rendered_no_new_effect_witnesses = render_comma_list(
        [render_no_new_effect_witness(witness) for witness in no_new_effect_data]
    )
    rendered_assumption_witnesses = render_comma_list(
        [render_formal_assumption_witness(witness) for witness in assumption_data]
    )
    rendered_primitive_core_witnesses = render_comma_list(
        [render_primitive_core_witness(witness) for witness in primitive_core_data]
    )
    rendered_import_obligation_witnesses = render_comma_list(
        [render_import_obligation_witness(witness) for witness in import_obligation_data]
    )
    rendered_fdc_condition_witnesses = render_comma_list(
        [render_fdc_condition_witness(witness) for witness in fdc_condition_data]
    )
    rendered_fdc_negative_control_witnesses = render_comma_list(
        [render_fdc_negative_control_witness(witness) for witness in fdc_negative_control_data]
    )
    rendered_fdc_open_obligation_witnesses = render_comma_list(
        [render_fdc_open_obligation_witness(witness) for witness in fdc_open_obligation_data]
    )
    if claim_refs:
        cardinality_theorem = """theorem current_formal_claim_ledger_nonempty :
    currentFormalClaimRefs.length > 0 := by
  native_decide"""
    else:
        cardinality_theorem = """theorem current_formal_claim_ledger_empty :
    currentFormalClaimRefs = [] := by
  native_decide"""
    return f"""-- Generated by scripts/sync_formal_proof_ledger.py. Do not edit by hand.

namespace IDT

def currentFormalClaimRefs : List String :=
  {rendered_claim_refs}

def currentFormalClaimCount : Nat := {len(claim_refs)}

structure RegistryWitness where
  id : String
  source : String
  items : List String
  expectedCount : Nat
  expectedDigest : String
  computedDigest : String
deriving Repr

def RegistryWitness.valid (w : RegistryWitness) : Bool :=
  w.items.length == w.expectedCount
    && w.expectedDigest == w.computedDigest
    && decide (w.items.Nodup)
    && decide (w.items.length > 0)

structure ArityWitness where
  id : String
  routeFamily : String
  arityBound : Nat
  uniformBound : Nat
  status : String
deriving Repr

def ArityWitness.valid (w : ArityWitness) : Bool :=
  w.status == "formal_proof"
    && decide (w.arityBound <= w.uniformBound)
    && decide (w.arityBound > 0)

structure GeneratorWitness where
  id : String
  routeFamily : String
  generatorRefs : List String
  status : String
deriving Repr

def GeneratorWitness.valid (w : GeneratorWitness) : Bool :=
  w.status == "formal_proof"
    && decide (w.generatorRefs.length > 0)
    && decide (w.generatorRefs.Nodup)

structure NoNewEffectWitness where
  id : String
  closedOverSources : List String
  newPrimitiveEffects : List String
  status : String
deriving Repr

def NoNewEffectWitness.valid (w : NoNewEffectWitness) : Bool :=
  w.status == "formal_proof"
    && w.newPrimitiveEffects == []
    && decide (w.closedOverSources.length > 0)

structure FormalAssumptionWitness where
  id : String
  status : String
  evidenceRefs : List String
  openGap : String
deriving Repr

def FormalAssumptionWitness.valid (w : FormalAssumptionWitness) : Bool :=
  w.status == "formal_proof"
    && w.openGap == ""
    && decide (w.evidenceRefs.length > 0)

structure PrimitiveCoreWitness where
  id : String
  primitiveStatus : String
  carrierStatus : String
  laws : List String
  expectedLaws : List String
  allowedDependencies : List String
  expectedAllowedDependencies : List String
  forbiddenRefHits : List String
deriving Repr

def PrimitiveCoreWitness.valid (w : PrimitiveCoreWitness) : Bool :=
  w.primitiveStatus == "idt_primitive"
    && w.carrierStatus == "carrier_neutral"
    && w.laws == w.expectedLaws
    && w.allowedDependencies == w.expectedAllowedDependencies
    && w.forbiddenRefHits == []
    && decide (w.laws.Nodup)
    && decide (w.laws.length > 0)

structure ImportObligationWitness where
  importId : String
  obligationKind : String
  target : String
  requiredStatus : String
  targetRefactor : String
  proofBoundary : String
deriving Repr

def ImportObligationWitness.valid (w : ImportObligationWitness) : Bool :=
  w.proofBoundary == "not_derived_from_idt_primitives"
    && w.requiredStatus != "formal_proof"
    && w.requiredStatus != "derived"
    && decide (w.target.length > 0)
    && decide (w.targetRefactor.length > 0)

structure FDCConditionWitness where
  id : String
  status : String
  expectedStatus : String
  evidenceRefs : List String
  openGap : String
  forbiddenRefHits : List String
deriving Repr

def FDCConditionWitness.valid (w : FDCConditionWitness) : Bool :=
  w.status == w.expectedStatus
    && w.expectedStatus == "candidate_principle"
    && w.forbiddenRefHits == []
    && decide (w.evidenceRefs.length > 0)
    && decide (w.openGap.length > 0)

structure FDCNegativeControlWitness where
  id : String
  expectedResult : String
  requiredResult : String
  evidenceRefs : List String
  retainedBoundary : String
deriving Repr

def FDCNegativeControlWitness.valid (w : FDCNegativeControlWitness) : Bool :=
  w.expectedResult == w.requiredResult
    && decide (w.evidenceRefs.length > 0)
    && decide (w.retainedBoundary.length > 0)

structure FDCOpenObligationWitness where
  id : String
  requiredStatus : String
  expectedRequiredStatus : String
deriving Repr

def FDCOpenObligationWitness.valid (w : FDCOpenObligationWitness) : Bool :=
  w.requiredStatus == w.expectedRequiredStatus
    && w.requiredStatus != "formal_proof"
    && w.requiredStatus != "derived"

structure JointOnlyRejectionWitness where
  id : String
  status : String
  scope : String
  assumptions : List String
  separatorRefs : List String
  rejectedWitnessRefs : List String
  openGap : String
deriving Repr

def JointOnlyRejectionWitness.valid (w : JointOnlyRejectionWitness) : Bool :=
  w.status == "formal_proof"
    && w.scope == "finite_route_covered_context_product_composites"
    && w.openGap == ""
    && decide (w.assumptions.length > 0)
    && decide (w.separatorRefs.length > 0)
    && decide (w.rejectedWitnessRefs.length > 0)

def registryWitnesses : List RegistryWitness :=
[
{rendered_registry_witnesses}
]

def arityWitnesses : List ArityWitness :=
[
{rendered_arity_witnesses}
]

def generatorWitnesses : List GeneratorWitness :=
[
{rendered_generator_witnesses}
]

def noNewEffectWitnesses : List NoNewEffectWitness :=
[
{rendered_no_new_effect_witnesses}
]

def formalAssumptionWitnesses : List FormalAssumptionWitness :=
[
{rendered_assumption_witnesses}
]

def primitiveCoreWitnesses : List PrimitiveCoreWitness :=
[
{rendered_primitive_core_witnesses}
]

def importObligationWitnesses : List ImportObligationWitness :=
[
{rendered_import_obligation_witnesses}
]

def fdcTargetPrinciple : String := {lean_string(FDC_TARGET_PRINCIPLE)}

def fdcClosureRule : String := {lean_string(FDC_CLOSURE_RULE)}

def fdcForbiddenUpgrades : List String :=
  {lean_list(FDC_FORBIDDEN_UPGRADES)}

def fdcConditionWitnesses : List FDCConditionWitness :=
[
{rendered_fdc_condition_witnesses}
]

def fdcNegativeControlWitnesses : List FDCNegativeControlWitness :=
[
{rendered_fdc_negative_control_witnesses}
]

def fdcOpenObligationWitnesses : List FDCOpenObligationWitness :=
[
{rendered_fdc_open_obligation_witnesses}
]

def jointOnlyRejectionWitness : JointOnlyRejectionWitness :=
{{
  id := {lean_string(joint_witness.identifier)},
  status := {lean_string(joint_witness.status)},
  scope := {lean_string(joint_witness.scope)},
  assumptions := {lean_list(joint_witness.assumptions, "    ")},
  separatorRefs := {lean_list(joint_witness.separator_refs, "    ")},
  rejectedWitnessRefs := {lean_list(joint_witness.rejected_witness_refs, "    ")},
  openGap := {lean_string(joint_witness.open_gap)}
}}

def currentSemanticProofChecks : List Bool :=
  [
    registryWitnesses.all RegistryWitness.valid,
    arityWitnesses.all ArityWitness.valid,
    generatorWitnesses.all GeneratorWitness.valid,
    noNewEffectWitnesses.all NoNewEffectWitness.valid,
    formalAssumptionWitnesses.all FormalAssumptionWitness.valid,
    primitiveCoreWitnesses.all PrimitiveCoreWitness.valid,
    importObligationWitnesses.all ImportObligationWitness.valid,
    fdcTargetPrinciple == "facticizable_distinguishability_closure",
    fdcClosureRule == "stable_inherited_distinguishability_requires_finite_readout_witness",
    fdcForbiddenUpgrades.length == 5,
    fdcConditionWitnesses.all FDCConditionWitness.valid,
    fdcNegativeControlWitnesses.all FDCNegativeControlWitness.valid,
    fdcOpenObligationWitnesses.all FDCOpenObligationWitness.valid,
    jointOnlyRejectionWitness.valid
  ]

theorem current_formal_claim_ledger_count :
    currentFormalClaimRefs.length = currentFormalClaimCount := by
  native_decide

{cardinality_theorem}

theorem current_formal_claim_ledger_nodup :
    currentFormalClaimRefs.Nodup := by
  native_decide

theorem current_signature_registry_witnesses_valid :
    registryWitnesses.all RegistryWitness.valid = true := by
  native_decide

theorem current_bounded_arity_witnesses_valid :
    arityWitnesses.all ArityWitness.valid = true := by
  native_decide

theorem current_route_generator_witnesses_valid :
    generatorWitnesses.all GeneratorWitness.valid = true := by
  native_decide

theorem current_no_new_effect_witnesses_valid :
    noNewEffectWitnesses.all NoNewEffectWitness.valid = true := by
  native_decide

theorem current_formal_assumption_witnesses_valid :
    formalAssumptionWitnesses.all FormalAssumptionWitness.valid = true := by
  native_decide

theorem current_primitive_core_witnesses_valid :
    primitiveCoreWitnesses.all PrimitiveCoreWitness.valid = true := by
  native_decide

theorem current_import_obligation_witnesses_valid :
    importObligationWitnesses.all ImportObligationWitness.valid = true := by
  native_decide

theorem current_fdc_condition_witnesses_valid :
    fdcConditionWitnesses.all FDCConditionWitness.valid = true := by
  native_decide

theorem current_fdc_negative_control_witnesses_valid :
    fdcNegativeControlWitnesses.all FDCNegativeControlWitness.valid = true := by
  native_decide

theorem current_fdc_open_obligation_witnesses_valid :
    fdcOpenObligationWitnesses.all FDCOpenObligationWitness.valid = true := by
  native_decide

theorem current_joint_only_rejection_witness_valid :
    jointOnlyRejectionWitness.valid = true := by
  native_decide

theorem current_semantic_proof_checks_pass :
    currentSemanticProofChecks.all (fun check => check) = true := by
  native_decide

end IDT
"""


def write_atomic(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as temp_file:
        temp_path = Path(temp_file.name)
        temp_file.write(content)
        temp_file.flush()
        os.fsync(temp_file.fileno())
    os.replace(temp_path, path)


def check_ledger(manifest_path: Path, lean_path: Path, output: TextIO) -> int:
    manifest = load_manifest(manifest_path)
    claim_refs = formal_claim_refs(manifest)
    expected = render_lean(manifest)
    try:
        actual = lean_path.read_text(encoding="utf-8")
    except FileNotFoundError:
        output.write(
            json.dumps(
                {
                    "ok": False,
                    "reason": "lean_ledger_missing",
                    "path": display_path(lean_path),
                    "claim_count": len(claim_refs),
                },
                indent=2,
            )
        )
        output.write("\n")
        return 1
    if actual != expected:
        output.write(
            json.dumps(
                {
                    "ok": False,
                    "reason": "lean_ledger_out_of_sync",
                    "path": display_path(lean_path),
                    "claim_count": len(claim_refs),
                },
                indent=2,
            )
        )
        output.write("\n")
        return 1
    output.write(
        json.dumps(
            {
                "ok": True,
                "path": display_path(lean_path),
                "claim_count": len(claim_refs),
            },
            indent=2,
        )
    )
    output.write("\n")
    return 0


def write_ledger(manifest_path: Path, lean_path: Path, output: TextIO) -> int:
    manifest = load_manifest(manifest_path)
    claim_refs = formal_claim_refs(manifest)
    content = render_lean(manifest)
    if lean_path.exists() and lean_path.read_text(encoding="utf-8") == content:
        changed = False
    else:
        write_atomic(lean_path, content)
        changed = True
    output.write(
        json.dumps(
            {
                "ok": True,
                "path": display_path(lean_path),
                "claim_count": len(claim_refs),
                "changed": changed,
            },
            indent=2,
        )
    )
    output.write("\n")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Synchronize the generated Lean ledger of formal proof claims.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lean-path", type=Path, default=DEFAULT_LEAN_PATH)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="Fail if the Lean ledger is out of sync.")
    mode.add_argument("--write", action="store_true", help="Rewrite the generated Lean ledger.")
    return parser


def main(argv: Sequence[str] | None = None, output: TextIO | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    stream = output if output is not None else sys.stdout
    manifest_path = args.manifest if args.manifest.is_absolute() else ROOT / args.manifest
    lean_path = args.lean_path if args.lean_path.is_absolute() else ROOT / args.lean_path
    if args.write:
        return write_ledger(manifest_path, lean_path, stream)
    return check_ledger(manifest_path, lean_path, stream)


if __name__ == "__main__":
    raise SystemExit(main())
