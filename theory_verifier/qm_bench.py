from __future__ import annotations

from dataclasses import dataclass

from theory_verifier.core import Manifest, QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS


@dataclass(frozen=True)
class QMBenchKernel:
    identifier: str
    title: str
    compiler_target: str
    experiment_ids: tuple[str, ...]
    finite_gate_ids: tuple[str, ...]
    operations: tuple[str, ...]
    claim_boundary: str

    def to_jsonable(self) -> dict[str, object]:
        return {
            "id": self.identifier,
            "title": self.title,
            "compiler_target": self.compiler_target,
            "experiment_count": len(self.experiment_ids),
            "finite_gate_count": len(self.finite_gate_ids),
            "experiments": list(self.experiment_ids),
            "finite_gates": list(self.finite_gate_ids),
            "operations": list(self.operations),
            "claim_boundary": self.claim_boundary,
        }


@dataclass(frozen=True)
class QMBenchCompilation:
    kernels: tuple[QMBenchKernel, ...]
    experiment_count: int
    finite_gate_reference_count: int
    shared_operations: tuple[str, ...]

    def to_jsonable(self) -> dict[str, object]:
        return {
            "ok": True,
            "kernel_count": len(self.kernels),
            "experiment_count": self.experiment_count,
            "finite_gate_reference_count": self.finite_gate_reference_count,
            "shared_operations": list(self.shared_operations),
            "kernels": [kernel.to_jsonable() for kernel in self.kernels],
        }


def compile_qm_bench(manifest: Manifest) -> QMBenchCompilation:
    kernels = tuple(
        QMBenchKernel(
            identifier=pattern.identifier,
            title=pattern.title,
            compiler_target=pattern.compiler_target,
            experiment_ids=pattern.experiments,
            finite_gate_ids=pattern.finite_gates,
            operations=QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS,
            claim_boundary=pattern.claim_boundary,
        )
        for pattern in manifest.qm_universal_patterns
    )
    experiment_ids = {experiment_id for kernel in kernels for experiment_id in kernel.experiment_ids}
    finite_gate_ids = {gate_id for kernel in kernels for gate_id in kernel.finite_gate_ids}
    return QMBenchCompilation(
        kernels=kernels,
        experiment_count=len(experiment_ids),
        finite_gate_reference_count=len(finite_gate_ids),
        shared_operations=QM_UNIVERSAL_PATTERN_REQUIRED_OPERATIONS,
    )
