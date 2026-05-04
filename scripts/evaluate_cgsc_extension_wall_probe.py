from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import scripts.evaluate_cgsc_primitive_derivation as primitive_derivation  # noqa: E402

DEFAULT_DRAFT = REPO_ROOT / "Proofs/QMClosure/CGSCExtensionWallProbeDraft.json"

Verdict = Literal[
    "EXTENSION_WALL_LOCALIZED",
    "EXTENSION_ROUTE_READY",
    "EXTENSION_DRAFT_INVALID",
    "FATAL_IMPORT_WALL",
    "PRIMITIVE_DERIVATION_UNEXPECTED",
]
PackageStatus = Literal["OPEN_EXTENSION", "DERIVED", "IMPORT_REJECTED"]
ControlStatus = Literal["REJECTED_CONTROL", "CONTROL_FAILED"]

FORBIDDEN_IMPORTS: tuple[str, ...] = (
    "born_rule",
    "complex_hilbert_space",
    "generator_assumed",
    "hilbert_tensor_product",
    "spectral_theorem",
    "stone_theorem",
    "unitary_group",
)
EXPECTED_PACKAGE_IDS: tuple[str, ...] = (
    "finite_exposed_context_completion",
    "route_automorphism_and_refinement_coherence",
    "generated_composite_no_hidden_joint_closure",
)
EXPECTED_CONTROL_IDS: tuple[str, ...] = (
    "spectral_theorem_import_control",
    "unitary_group_import_control",
    "stone_generator_import_control",
    "hilbert_tensor_product_import_control",
    "born_rule_import_control",
    "complex_hilbert_carrier_import_control",
)


@dataclass(frozen=True)
class ExtensionPackage:
    id: str
    expected_status: PackageStatus
    covers: tuple[str, ...]
    required_clauses: tuple[str, ...]
    open_obligation: str
    candidate_imports: tuple[str, ...]
    forbidden_imports: tuple[str, ...]


@dataclass(frozen=True)
class NegativeControl:
    id: str
    attempted_import: str
    target_package: str
    expected_status: ControlStatus


@dataclass(frozen=True)
class PackageCheck:
    id: str
    status: PackageStatus
    covers: tuple[str, ...]
    required_clauses: tuple[str, ...]
    forbidden_import_hits: tuple[str, ...]
    open_obligation: str


@dataclass(frozen=True)
class ControlCheck:
    id: str
    status: ControlStatus
    attempted_import: str
    target_package: str


@dataclass(frozen=True)
class DraftCheck:
    name: str
    passed: bool
    reason: str


@dataclass(frozen=True)
class ExtensionWallProbe:
    verdict: Verdict
    primitive_derivation: primitive_derivation.Verdict
    draft_path: str
    missing_extensions: tuple[str, ...]
    extension_packages: int
    covered_extensions: tuple[str, ...]
    uncovered_extensions: tuple[str, ...]
    fatal_imports: tuple[str, ...]
    rejected_controls: int
    failed_controls: int
    draft_checks_passed: int
    draft_checks_failed: int
    package_checks: list[PackageCheck]
    control_checks: list[ControlCheck]
    draft_checks: list[DraftCheck]
    next_blocker: str


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


def string_tuple(value: object, field: str) -> tuple[str, ...]:
    return tuple(require_string(item, f"{field}[]") for item in require_list(value, field))


def sorted_tuple(values: set[str]) -> tuple[str, ...]:
    return tuple(sorted(values))


def load_draft(path: Path) -> dict[str, object]:
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    return require_mapping(raw, "draft")


def check_equals(name: str, actual: object, expected: object) -> DraftCheck:
    if actual == expected:
        return DraftCheck(name=name, passed=True, reason=f"{actual!r}")
    return DraftCheck(name=name, passed=False, reason=f"expected {expected!r}, got {actual!r}")


def check_set_equals(name: str, actual: tuple[str, ...], expected: tuple[str, ...]) -> DraftCheck:
    actual_set = set(actual)
    expected_set = set(expected)
    if actual_set == expected_set:
        return DraftCheck(name=name, passed=True, reason=f"count={len(actual_set)}")
    return DraftCheck(
        name=name,
        passed=False,
        reason=f"missing={sorted(expected_set - actual_set)}; extra={sorted(actual_set - expected_set)}",
    )


def existing_dependency_refs(dependencies: tuple[str, ...]) -> DraftCheck:
    missing = tuple(ref for ref in dependencies if not (REPO_ROOT / ref).exists())
    if not missing:
        return DraftCheck(name="dependency_refs_grounded", passed=True, reason=f"count={len(dependencies)}")
    return DraftCheck(name="dependency_refs_grounded", passed=False, reason=f"missing={','.join(missing)}")


def parse_package(value: object, field: str) -> ExtensionPackage:
    package = require_mapping(value, field)
    expected_status_raw = require_string(package.get("expected_status"), f"{field}.expected_status")
    if expected_status_raw == "OPEN_EXTENSION":
        expected_status: PackageStatus = "OPEN_EXTENSION"
    elif expected_status_raw == "DERIVED":
        expected_status = "DERIVED"
    elif expected_status_raw == "IMPORT_REJECTED":
        expected_status = "IMPORT_REJECTED"
    else:
        raise ValueError(f"{field}.expected_status is invalid: {expected_status_raw!r}")
    return ExtensionPackage(
        id=require_string(package.get("id"), f"{field}.id"),
        expected_status=expected_status,
        covers=string_tuple(package.get("covers"), f"{field}.covers"),
        required_clauses=string_tuple(package.get("required_clauses"), f"{field}.required_clauses"),
        open_obligation=require_string(package.get("open_obligation"), f"{field}.open_obligation"),
        candidate_imports=string_tuple(package.get("candidate_imports"), f"{field}.candidate_imports"),
        forbidden_imports=string_tuple(package.get("forbidden_imports"), f"{field}.forbidden_imports"),
    )


def parse_control(value: object, field: str) -> NegativeControl:
    control = require_mapping(value, field)
    expected_status_raw = require_string(control.get("expected_status"), f"{field}.expected_status")
    if expected_status_raw == "REJECTED_CONTROL":
        expected_status: ControlStatus = "REJECTED_CONTROL"
    elif expected_status_raw == "CONTROL_FAILED":
        expected_status = "CONTROL_FAILED"
    else:
        raise ValueError(f"{field}.expected_status is invalid: {expected_status_raw!r}")
    return NegativeControl(
        id=require_string(control.get("id"), f"{field}.id"),
        attempted_import=require_string(control.get("attempted_import"), f"{field}.attempted_import"),
        target_package=require_string(control.get("target_package"), f"{field}.target_package"),
        expected_status=expected_status,
    )


def packages_from_draft(probe: dict[str, object]) -> list[ExtensionPackage]:
    return [
        parse_package(raw_package, f"probe.packages[{index}]")
        for index, raw_package in enumerate(require_list(probe.get("packages"), "probe.packages"))
    ]


def controls_from_draft(probe: dict[str, object]) -> list[NegativeControl]:
    return [
        parse_control(raw_control, f"probe.negative_controls[{index}]")
        for index, raw_control in enumerate(require_list(probe.get("negative_controls"), "probe.negative_controls"))
    ]


def check_package(package: ExtensionPackage) -> PackageCheck:
    forbidden_hits = tuple(item for item in package.candidate_imports if item in FORBIDDEN_IMPORTS)
    if forbidden_hits:
        status: PackageStatus = "IMPORT_REJECTED"
    elif package.expected_status == "DERIVED":
        status = "DERIVED"
    else:
        status = "OPEN_EXTENSION"
    return PackageCheck(
        id=package.id,
        status=status,
        covers=package.covers,
        required_clauses=package.required_clauses,
        forbidden_import_hits=forbidden_hits,
        open_obligation=package.open_obligation,
    )


def check_control(control: NegativeControl, package_ids: set[str]) -> ControlCheck:
    if control.attempted_import in FORBIDDEN_IMPORTS and control.target_package in package_ids:
        status: ControlStatus = "REJECTED_CONTROL"
    else:
        status = "CONTROL_FAILED"
    return ControlCheck(
        id=control.id,
        status=status,
        attempted_import=control.attempted_import,
        target_package=control.target_package,
    )


def package_forbidden_imports(packages: list[ExtensionPackage]) -> tuple[str, ...]:
    imports: set[str] = set()
    for package in packages:
        imports.update(package.forbidden_imports)
    return sorted_tuple(imports)


def validate_draft(
    draft: dict[str, object],
    probe: dict[str, object],
    primitive_probe: primitive_derivation.PrimitiveDerivationProbe,
    packages: list[ExtensionPackage],
    controls: list[NegativeControl],
    package_checks: list[PackageCheck],
    control_checks: list[ControlCheck],
    verdict: Verdict,
) -> list[DraftCheck]:
    dependencies = string_tuple(probe.get("dependencies"), "probe.dependencies")
    covered: set[str] = set()
    for package in packages:
        covered.update(package.covers)
    package_statuses = tuple(f"{check.id}:{check.status}" for check in package_checks)
    expected_package_statuses = tuple(f"{package.id}:{package.expected_status}" for package in packages)
    control_statuses = tuple(f"{check.id}:{check.status}" for check in control_checks)
    expected_control_statuses = tuple(f"{control.id}:{control.expected_status}" for control in controls)
    return [
        check_equals("artifact_status", draft.get("artifact_status"), "extension_wall_probe_not_formal_proof"),
        check_equals("probe_id", probe.get("id"), "cgsc_extension_wall_probe"),
        check_equals("expected_verdict", probe.get("expected_verdict"), verdict),
        existing_dependency_refs(dependencies),
        check_equals("primitive_derivation_verdict", primitive_probe.verdict, "PRIMITIVE_DERIVATION_NOT_CLOSED"),
        check_set_equals("package_ids", tuple(package.id for package in packages), EXPECTED_PACKAGE_IDS),
        check_set_equals("control_ids", tuple(control.id for control in controls), EXPECTED_CONTROL_IDS),
        check_set_equals("package_statuses", package_statuses, expected_package_statuses),
        check_set_equals("control_statuses", control_statuses, expected_control_statuses),
        check_set_equals("covered_extensions", tuple(covered), primitive_probe.missing_base_extensions),
        check_set_equals("declared_forbidden_imports", package_forbidden_imports(packages), FORBIDDEN_IMPORTS),
    ]


def build_probe(draft_path: Path = DEFAULT_DRAFT) -> ExtensionWallProbe:
    draft = load_draft(draft_path)
    probe = require_mapping(draft.get("probe"), "probe")
    primitive_probe = primitive_derivation.build_probe()
    packages = packages_from_draft(probe)
    controls = controls_from_draft(probe)
    package_checks = [check_package(package) for package in packages]
    package_ids = {package.id for package in packages}
    control_checks = [check_control(control, package_ids) for control in controls]
    covered_extensions: set[str] = set()
    fatal_imports: set[str] = set()
    for check in package_checks:
        covered_extensions.update(check.covers)
        fatal_imports.update(check.forbidden_import_hits)
    missing_set = set(primitive_probe.missing_base_extensions)
    uncovered_extensions = sorted_tuple(missing_set - covered_extensions)
    covered_tuple = sorted_tuple(covered_extensions & missing_set)
    failed_controls = sum(1 for check in control_checks if check.status == "CONTROL_FAILED")
    rejected_controls = sum(1 for check in control_checks if check.status == "REJECTED_CONTROL")
    if primitive_probe.verdict != "PRIMITIVE_DERIVATION_NOT_CLOSED":
        verdict: Verdict = "PRIMITIVE_DERIVATION_UNEXPECTED"
    elif fatal_imports:
        verdict = "FATAL_IMPORT_WALL"
    elif not uncovered_extensions and rejected_controls == len(control_checks):
        verdict = "EXTENSION_WALL_LOCALIZED"
    else:
        verdict = "EXTENSION_DRAFT_INVALID"
    draft_checks = validate_draft(
        draft=draft,
        probe=probe,
        primitive_probe=primitive_probe,
        packages=packages,
        controls=controls,
        package_checks=package_checks,
        control_checks=control_checks,
        verdict=verdict,
    )
    draft_failed = sum(1 for check in draft_checks if not check.passed)
    if draft_failed > 0:
        verdict = "EXTENSION_DRAFT_INVALID"
    return ExtensionWallProbe(
        verdict=verdict,
        primitive_derivation=primitive_probe.verdict,
        draft_path=str(draft_path.relative_to(REPO_ROOT)),
        missing_extensions=primitive_probe.missing_base_extensions,
        extension_packages=len(packages),
        covered_extensions=covered_tuple,
        uncovered_extensions=uncovered_extensions,
        fatal_imports=sorted_tuple(fatal_imports),
        rejected_controls=rejected_controls,
        failed_controls=failed_controls,
        draft_checks_passed=sum(1 for check in draft_checks if check.passed),
        draft_checks_failed=draft_failed,
        package_checks=package_checks,
        control_checks=control_checks,
        draft_checks=draft_checks,
        next_blocker=(
            "prove or reject the three localized extension packages from B0; "
            "without them CGSC remains a conditional route and QM inevitability remains open"
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Localize the next CGSC primitive-extension wall.")
    parser.add_argument("--draft", default=str(DEFAULT_DRAFT))
    parser.add_argument("--output-json", default="")
    parser.add_argument("--show-packages", action="store_true")
    parser.add_argument("--show-controls", action="store_true")
    parser.add_argument("--show-draft-checks", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    probe = build_probe(Path(str(args.draft)))
    print(
        f"cgsc_extension_wall_probe={probe.verdict} primitive_derivation={probe.primitive_derivation} "
        f"missing_extensions={len(probe.missing_extensions)} extension_packages={probe.extension_packages} "
        f"covered_extensions={len(probe.covered_extensions)} uncovered_extensions={len(probe.uncovered_extensions)} "
        f"fatal_imports={len(probe.fatal_imports)} rejected_controls={probe.rejected_controls} "
        f"failed_controls={probe.failed_controls} draft_checks_failed={probe.draft_checks_failed}"
    )
    if probe.uncovered_extensions:
        print(f"UNCOVERED_EXTENSIONS {','.join(probe.uncovered_extensions)}")
    if probe.fatal_imports:
        print(f"FATAL_IMPORTS {','.join(probe.fatal_imports)}")
    print(f"NEXT {probe.next_blocker}")
    if args.show_packages:
        for check in probe.package_checks:
            print(f"{check.status} {check.id}: covers={','.join(check.covers)}")
            print(f"  obligation: {check.open_obligation}")
    if args.show_controls:
        for control_check in probe.control_checks:
            print(
                f"{control_check.status} {control_check.id}: "
                f"import={control_check.attempted_import} target={control_check.target_package}"
            )
    if args.show_draft_checks:
        for draft_check in probe.draft_checks:
            status = "PASS" if draft_check.passed else "FAIL"
            print(f"{status} {draft_check.name}: {draft_check.reason}")
    if args.output_json:
        with open(str(args.output_json), "w", encoding="utf-8") as handle:
            json.dump(asdict(probe), handle, indent=2, sort_keys=True)
            handle.write("\n")
    if probe.verdict in ("EXTENSION_DRAFT_INVALID", "FATAL_IMPORT_WALL", "PRIMITIVE_DERIVATION_UNEXPECTED"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
