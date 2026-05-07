import Proofs.MetaLang.V8ResidualEncodingRequirements

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 QM experiment residual ledger.

The current 35 QM experiment records are executable gates, not Lean proofs.
This module preserves their IDs as typed residual inputs that must be classified
in IDT v8 before research resumes.
-/

inductive CurrentQmExperimentId where
  | bornContextProbabilityTests
  | twoPathInterference
  | finiteI3Actualization
  | tripleSlitSorkinParameter
  | whichWayMarker
  | quantumEraser
  | unitaryMeasurementContext
  | finiteInterferometerNetwork
  | projectiveRepeatability
  | bellChshTable
  | bellChshFromAmplitudes
  | singletAngleModel
  | calibratedActionPhaseHoldout
  | decoherenceAndRecoverability
  | sternGerlachSingleAxis
  | sequentialSternGerlach
  | delayedChoice
  | aharonovBohmPhase
  | abFluxPeriod
  | ramseyInterferometry
  | rabiOscillation
  | photoelectricThreshold
  | spectroscopyLines
  | tunnelingBarrier
  | quantumZeno
  | hongOuMandel
  | antibunchingSinglePhoton
  | entanglementSwapping
  | quantumTeleportation
  | noCloning
  | ghzMerminContextuality
  | kochenSpeckerContextuality
  | leggettGargTemporalContext
  | weakMeasurement
  | quantumRandomWalk
deriving DecidableEq, Repr

def CurrentQmExperimentId.toManifestId : CurrentQmExperimentId → String
  | .bornContextProbabilityTests => "born_context_probability_tests"
  | .twoPathInterference => "two_path_interference"
  | .finiteI3Actualization => "finite_i3_actualization"
  | .tripleSlitSorkinParameter => "triple_slit_sorkin_parameter"
  | .whichWayMarker => "which_way_marker"
  | .quantumEraser => "quantum_eraser"
  | .unitaryMeasurementContext => "unitary_measurement_context"
  | .finiteInterferometerNetwork => "finite_interferometer_network"
  | .projectiveRepeatability => "projective_repeatability"
  | .bellChshTable => "bell_chsh_table"
  | .bellChshFromAmplitudes => "bell_chsh_from_amplitudes"
  | .singletAngleModel => "singlet_angle_model"
  | .calibratedActionPhaseHoldout => "calibrated_action_phase_holdout"
  | .decoherenceAndRecoverability => "decoherence_and_recoverability"
  | .sternGerlachSingleAxis => "stern_gerlach_single_axis"
  | .sequentialSternGerlach => "sequential_stern_gerlach"
  | .delayedChoice => "delayed_choice"
  | .aharonovBohmPhase => "aharonov_bohm_phase"
  | .abFluxPeriod => "ab_flux_period"
  | .ramseyInterferometry => "ramsey_interferometry"
  | .rabiOscillation => "rabi_oscillation"
  | .photoelectricThreshold => "photoelectric_threshold"
  | .spectroscopyLines => "spectroscopy_lines"
  | .tunnelingBarrier => "tunneling_barrier"
  | .quantumZeno => "quantum_zeno"
  | .hongOuMandel => "hong_ou_mandel"
  | .antibunchingSinglePhoton => "antibunching_single_photon"
  | .entanglementSwapping => "entanglement_swapping"
  | .quantumTeleportation => "quantum_teleportation"
  | .noCloning => "no_cloning"
  | .ghzMerminContextuality => "ghz_mermin_contextuality"
  | .kochenSpeckerContextuality => "kochen_specker_contextuality"
  | .leggettGargTemporalContext => "leggett_garg_temporal_context"
  | .weakMeasurement => "weak_measurement"
  | .quantumRandomWalk => "quantum_random_walk"

inductive ExperimentGateStatus where
  | executableGate
deriving DecidableEq, Repr

inductive ExperimentV8ClassificationStatus where
  | needsClassification
  | classified
deriving DecidableEq, Repr

structure QmExperimentResidualEntry where
  id : CurrentQmExperimentId
  gateStatus : ExperimentGateStatus
  v8Classification : ExperimentV8ClassificationStatus
deriving Repr

def QmExperimentResidualEntry.manifestId
    (entry : QmExperimentResidualEntry) : String :=
  entry.id.toManifestId

def currentQmExperimentResidualLedger : List QmExperimentResidualEntry :=
  [
    { id := .bornContextProbabilityTests, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .twoPathInterference, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .finiteI3Actualization, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .tripleSlitSorkinParameter, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .whichWayMarker, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .quantumEraser, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .unitaryMeasurementContext, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .finiteInterferometerNetwork, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .projectiveRepeatability, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .bellChshTable, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .bellChshFromAmplitudes, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .singletAngleModel, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .calibratedActionPhaseHoldout, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .decoherenceAndRecoverability, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .sternGerlachSingleAxis, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .sequentialSternGerlach, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .delayedChoice, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .aharonovBohmPhase, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .abFluxPeriod, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .ramseyInterferometry, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .rabiOscillation, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .photoelectricThreshold, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .spectroscopyLines, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .tunnelingBarrier, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .quantumZeno, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .hongOuMandel, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .antibunchingSinglePhoton, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .entanglementSwapping, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .quantumTeleportation, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .noCloning, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .ghzMerminContextuality, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .kochenSpeckerContextuality, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .leggettGargTemporalContext, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .weakMeasurement, gateStatus := .executableGate, v8Classification := .needsClassification },
    { id := .quantumRandomWalk, gateStatus := .executableGate, v8Classification := .needsClassification }
  ]

def qmExperimentClassificationCount
    (status : ExperimentV8ClassificationStatus)
    (entries : List QmExperimentResidualEntry) : Nat :=
  (entries.filter (fun entry => entry.v8Classification == status)).length

def qmExperimentGateStatusCount
    (status : ExperimentGateStatus)
    (entries : List QmExperimentResidualEntry) : Nat :=
  (entries.filter (fun entry => entry.gateStatus == status)).length

def qmExperimentResidualFormalProofCount : Nat := 0

theorem current_qm_experiment_residual_ledger_count :
    currentQmExperimentResidualLedger.length = 35 := by
  rfl

theorem current_qm_experiment_residuals_are_executable_gates :
    qmExperimentGateStatusCount
      .executableGate
      currentQmExperimentResidualLedger = 35 := by
  rfl

theorem current_qm_experiment_residuals_need_v8_classification :
    qmExperimentClassificationCount
      .needsClassification
      currentQmExperimentResidualLedger = 35 := by
  rfl

theorem current_qm_experiment_residuals_have_no_formal_proof_closure :
    qmExperimentResidualFormalProofCount = 0 := by
  rfl

end V8
end MetaLang
end IDT
