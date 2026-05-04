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
    IDT_CORE_CLAIM_ROLE_REGISTRY,
    IDT_CORE_ROUTE_FAMILY_REGISTRY,
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


def render_comma_list(items: Sequence[str]) -> str:
    return ",\n".join(items)


def render_lean(manifest: Manifest) -> str:
    claim_refs = formal_claim_refs(manifest)
    registry_data = registry_witnesses(manifest)
    arity_data = arity_witnesses(manifest)
    generator_data = generator_witnesses(manifest)
    no_new_effect_data = no_new_effect_witnesses(manifest)
    assumption_data = assumption_witnesses(manifest)
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
