import Proofs.MetaLang.V8LeanExperimentProtocolBoundary
import Proofs.MetaLang.V8MigrationCompletionCriterion

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 experiment program readiness.

This module records the readiness gate for moving executable experiments into
the Lean + IDT v8 architecture. It does not run experiments and does not claim
that any experiment is a physical/QM formal proof.
-/

structure ExperimentProgramReadiness where
  residualExperimentsClassified : Prop

def currentExperimentProgramReadiness : ExperimentProgramReadiness :=
  {
    residualExperimentsClassified :=
      qmExperimentClassificationCount
        ExperimentV8ClassificationStatus.needsClassification
        currentQmExperimentResidualLedger = 0
  }

def ExperimentProgramReadiness.readyForResearchHandoff
    (readiness : ExperimentProgramReadiness) : Prop :=
  v8LeanExperimentProtocolTarget.isCertifiedExecutableExperiment
    ∧ readiness.residualExperimentsClassified
    ∧ ¬ v8LeanExperimentProtocolTarget.canAssignPhysicalFormalProof

theorem current_experiment_program_protocol_is_certified_executable :
    v8LeanExperimentProtocolTarget.isCertifiedExecutableExperiment :=
  v8_lean_experiment_protocol_is_certified_executable_check

theorem current_experiment_program_residuals_are_classified :
    currentExperimentProgramReadiness.residualExperimentsClassified := by
  exact current_qm_experiment_residuals_need_v8_classification

theorem current_experiment_program_keeps_formal_proof_boundary :
    ¬ v8LeanExperimentProtocolTarget.canAssignPhysicalFormalProof :=
  certified_executable_experiment_cannot_assign_physical_formal_proof

theorem current_experiment_program_readiness_is_locally_ready :
    currentExperimentProgramReadiness.readyForResearchHandoff := by
  exact And.intro
    current_experiment_program_protocol_is_certified_executable
    (And.intro
      current_experiment_program_residuals_are_classified
      current_experiment_program_keeps_formal_proof_boundary)

end V8
end MetaLang
end IDT
