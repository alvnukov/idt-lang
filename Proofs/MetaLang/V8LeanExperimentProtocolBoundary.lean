import Proofs.MetaLang.V8QmExperimentResidualLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 Lean experiment protocol boundary.

This module records the intended architecture for executable experiments after
the Lean-first migration:

* Lean is the source of truth for admissible protocol logic and computable
  readout semantics;
* external fixtures, laboratory data, calibration anchors, and numeric
  tolerances remain explicit input boundaries;
* a successful executable experiment may become a certified executable check,
  but it is not a physical/QM `formalProof`.
-/

inductive ExperimentLogicAuthority where
  | leanCheckedProtocol
  | idtV8DeclarativeResidual
  | legacyPythonGate
deriving DecidableEq, Repr

inductive ExperimentInputBoundary where
  | noExternalInput
  | fixtureData
  | laboratoryData
  | calibrationAnchor
  | numericTolerance
deriving DecidableEq, Repr

inductive ExperimentResultStatus where
  | leanComputedResult
  | certifiedExecutableCheck
  | boundedNumericalEvidence
  | residualInputOnly
deriving DecidableEq, Repr

structure LeanExperimentProtocol where
  logicAuthority : ExperimentLogicAuthority
  inputBoundaries : List ExperimentInputBoundary
  resultStatus : ExperimentResultStatus
  proofAuthority : VerificationAuthority
deriving Repr

def LeanExperimentProtocol.logicComesFromLean
    (protocol : LeanExperimentProtocol) : Prop :=
  protocol.logicAuthority = ExperimentLogicAuthority.leanCheckedProtocol

def LeanExperimentProtocol.hasExternalInputBoundary
    (protocol : LeanExperimentProtocol) : Prop :=
  ∃ boundary, boundary ∈ protocol.inputBoundaries
    ∧ boundary ≠ ExperimentInputBoundary.noExternalInput

def LeanExperimentProtocol.canAssignPhysicalFormalProof
    (protocol : LeanExperimentProtocol) : Prop :=
  protocol.proofAuthority = VerificationAuthority.proofTruth
    ∧ ¬ protocol.hasExternalInputBoundary
    ∧ protocol.resultStatus = ExperimentResultStatus.leanComputedResult

def LeanExperimentProtocol.isCertifiedExecutableExperiment
    (protocol : LeanExperimentProtocol) : Prop :=
  protocol.logicComesFromLean
    ∧ protocol.hasExternalInputBoundary
    ∧ protocol.resultStatus = ExperimentResultStatus.certifiedExecutableCheck
    ∧ protocol.proofAuthority = VerificationAuthority.declarativeInputCheck

def v8LeanExperimentProtocolTarget : LeanExperimentProtocol :=
  {
    logicAuthority := ExperimentLogicAuthority.leanCheckedProtocol,
    inputBoundaries := [
      ExperimentInputBoundary.fixtureData,
      ExperimentInputBoundary.calibrationAnchor,
      ExperimentInputBoundary.numericTolerance
    ],
    resultStatus := ExperimentResultStatus.certifiedExecutableCheck,
    proofAuthority := VerificationAuthority.declarativeInputCheck
  }

theorem v8_lean_experiment_protocol_logic_is_lean_checked :
    v8LeanExperimentProtocolTarget.logicComesFromLean := by
  rfl

theorem v8_lean_experiment_protocol_has_external_input_boundary :
    v8LeanExperimentProtocolTarget.hasExternalInputBoundary := by
  exact ⟨ExperimentInputBoundary.fixtureData, by simp [v8LeanExperimentProtocolTarget], by decide⟩

theorem v8_lean_experiment_protocol_is_certified_executable_check :
    v8LeanExperimentProtocolTarget.isCertifiedExecutableExperiment := by
  exact And.intro
    v8_lean_experiment_protocol_logic_is_lean_checked
    (And.intro
      v8_lean_experiment_protocol_has_external_input_boundary
      (And.intro rfl rfl))

theorem certified_executable_experiment_cannot_assign_physical_formal_proof :
    ¬ v8LeanExperimentProtocolTarget.canAssignPhysicalFormalProof := by
  intro canAssign
  exact nomatch canAssign.left

structure ExperimentProgramArchitecture where
  protocol : LeanExperimentProtocol
  residualLedger : List QmExperimentResidualEntry
  residualsNeedClassification :
    qmExperimentClassificationCount
      ExperimentV8ClassificationStatus.needsClassification
      residualLedger = residualLedger.length

def currentExperimentProgramArchitecture : ExperimentProgramArchitecture :=
  {
    protocol := v8LeanExperimentProtocolTarget,
    residualLedger := currentQmExperimentResidualLedger,
    residualsNeedClassification := by
      rw [current_qm_experiment_residuals_need_v8_classification]
      rw [current_qm_experiment_residual_ledger_count]
  }

theorem current_experiment_program_has_35_residual_experiments :
    currentExperimentProgramArchitecture.residualLedger.length = 35 := by
  exact current_qm_experiment_residual_ledger_count

theorem current_experiment_program_is_not_physical_formal_proof :
    ¬ currentExperimentProgramArchitecture.protocol.canAssignPhysicalFormalProof := by
  exact certified_executable_experiment_cannot_assign_physical_formal_proof

end V8
end MetaLang
end IDT
