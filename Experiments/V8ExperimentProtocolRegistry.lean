import Proofs.MetaLang.V8LeanExperimentProtocolBoundary

open IDT.MetaLang.V8

namespace IDT
namespace Experiments
namespace V8

/-!
Lean-sourced v8 experiment protocol registry.

This executable registry is intentionally small. It declares which logical
nodes a Python runner may exercise and which claim boundaries must be preserved.
The runner may produce certified executable telemetry, but never a physical or
QM `formal_proof`.
-/

inductive LogicalNodeRole where
  | used
  | stressed
  | blocked
deriving DecidableEq, Repr

structure LogicalNodeSpec where
  id : String
  label : String
  claimBoundary : String
deriving Repr

structure ExperimentProtocolSpec where
  id : String
  experimentId : String
  fixtureClass : String
  claimBoundary : String
  logicalNodes : List String
  allowedResultStatuses : List String
  forbiddenUpgrades : List String
deriving Repr

def allowedTelemetryResultStatuses : List String :=
  ["pass", "fail", "inconclusive", "blocked"]

def requiredForbiddenUpgrades : List String :=
  ["formal_proof", "physical_formal_proof", "qm_formal_proof"]

def logicalNodeSpecs : List LogicalNodeSpec :=
  [
    {
      id := "phase_action_conversion_I",
      label := "calibrated universal action-to-phase anchor",
      claimBoundary := "calibrated anchor only; does not derive hbar_I"
    },
    {
      id := "no_refit_shared_parameter",
      label := "one shared frozen parameter across fixture classes",
      claimBoundary := "reject per-experiment refit"
    },
    {
      id := "hbar_first_principles_boundary",
      label := "hbar_I remains blocked as first-principles derivation",
      claimBoundary := "experiment telemetry cannot upgrade hbar_I"
    },
    {
      id := "context_normalization",
      label := "finite readout weights normalize inside one context",
      claimBoundary := "finite executable readout check only"
    },
    {
      id := "positive_measure_readout",
      label := "finite readout weights remain nonnegative",
      claimBoundary := "positive finite fixture check only"
    },
    {
      id := "bell_chsh_no_signalling",
      label := "Bell/CHSH table has no-signalling marginals",
      claimBoundary := "finite table compatibility check only"
    },
    {
      id := "bounded_correlation_window",
      label := "CHSH value stays inside declared finite bound",
      claimBoundary := "does not derive Bell correlations from primitives"
    },
    {
      id := "interference_visibility",
      label := "finite interference visibility matches declared fixture",
      claimBoundary := "finite interference fixture only; not Born proof"
    },
    {
      id := "path_marker_distinguishability",
      label := "path marker and eraser visibility boundary is explicit",
      claimBoundary := "finite marker/eraser fixture only"
    },
    {
      id := "sorkin_i3_zero",
      label := "third-order interference term is zero in finite fixture",
      claimBoundary := "finite Sorkin I3 compatibility check only"
    },
    {
      id := "phase_accumulation",
      label := "phase accumulation follows declared calibrated relation",
      claimBoundary := "calibrated phase fixture only; does not derive hbar_I"
    },
    {
      id := "spin_axis_transition",
      label := "finite spin-axis transition table matches declared fixture",
      claimBoundary := "finite spin readout fixture only"
    },
    {
      id := "unitary_context_map",
      label := "finite context map preserves declared readout probabilities",
      claimBoundary := "finite unitary-context fixture only; not unitary derivation"
    },
    {
      id := "projective_repeatability",
      label := "ideal finite projective readout repeats in the selected context",
      claimBoundary := "finite repeatability fixture only; not collapse derivation"
    },
    {
      id := "amplitude_probability_readout",
      label := "declared amplitude packet yields a finite probability table",
      claimBoundary := "finite amplitude fixture only; not Born proof"
    },
    {
      id := "singlet_angle_correlation",
      label := "finite singlet angle grid matches declared correlation table",
      claimBoundary := "finite angle-grid fixture only; not spin representation derivation"
    },
    {
      id := "decoherence_suppression",
      label := "finite environment kernel suppresses residual coherence",
      claimBoundary := "finite decoherence fixture only"
    },
    {
      id := "recoverability_loss",
      label := "finite visibility loss crosses declared facticity threshold",
      claimBoundary := "finite recoverability fixture only"
    },
    {
      id := "repeated_context_survival",
      label := "finite repeated-context survival follows declared Zeno samples",
      claimBoundary := "finite Zeno fixture only; not continuous measurement derivation"
    },
    {
      id := "context_transfer_branch",
      label := "finite Bell-branch correction reconstructs the target state",
      claimBoundary := "finite branch-correction fixture only; not physical teleportation proof"
    },
    {
      id := "no_cloning_obstruction",
      label := "finite overlap-preservation obstruction rejects universal cloning",
      claimBoundary := "finite obstruction fixture only; not cloning-machine model"
    },
    {
      id := "barrier_transmission_suppression",
      label := "finite forbidden-barrier transmission is exponentially suppressed",
      claimBoundary := "finite barrier fixture only; not material barrier derivation"
    },
    {
      id := "bosonic_coincidence_suppression",
      label := "finite indistinguishability fixture suppresses coincidence events",
      claimBoundary := "finite HOM fixture only; not photonic apparatus derivation"
    },
    {
      id := "single_quantum_coincidence_exclusion",
      label := "finite single-source fixture excludes double coincidence facticity",
      claimBoundary := "finite antibunching fixture only; not source physics derivation"
    },
    {
      id := "conditional_inheritance_swap",
      label := "finite Bell outcome transfers declared remote correlations",
      claimBoundary := "finite swapping fixture only; not source/network derivation"
    },
    {
      id := "contextuality_obstruction",
      label := "finite parity/context hypergraph has no global assignment",
      claimBoundary := "finite contextuality obstruction fixture only"
    },
    {
      id := "temporal_facticity_bound",
      label := "finite temporal-correlation fixture crosses declared macrorealist bound",
      claimBoundary := "finite Leggett-Garg fixture only"
    },
    {
      id := "partial_facticity_readout",
      label := "finite weak readout has declared pointer shift without full facticity",
      claimBoundary := "finite weak-measurement fixture only"
    },
    {
      id := "unitary_graph_walk_distribution",
      label := "finite unitary graph walk matches declared distribution",
      claimBoundary := "finite graph-walk fixture only; not general graph-walk theory"
    },
    {
      id := "residual_fixture_not_implemented",
      label := "residual QM experiment awaits a v8 telemetry fixture",
      claimBoundary := "coverage only; blocked until a safe fixture exists"
    }
  ]

def protocol
    (experimentId : String)
    (fixtureClass : String)
    (nodes : List String)
    (boundary : String) : ExperimentProtocolSpec :=
  {
    id := experimentId ++ "_protocol",
    experimentId := experimentId,
    fixtureClass := fixtureClass,
    claimBoundary := boundary,
    logicalNodes := nodes,
    allowedResultStatuses := allowedTelemetryResultStatuses,
    forbiddenUpgrades := requiredForbiddenUpgrades
  }

def residualProtocol (experimentId : String) : ExperimentProtocolSpec :=
  {
    id := experimentId ++ "_protocol",
    experimentId := experimentId,
    fixtureClass := "residual_not_implemented",
    claimBoundary := "residual experiment is registered for telemetry coverage; fixture not implemented",
    logicalNodes := ["residual_fixture_not_implemented"],
    allowedResultStatuses := allowedTelemetryResultStatuses,
    forbiddenUpgrades := requiredForbiddenUpgrades
  }

def experimentProtocolSpecs : List ExperimentProtocolSpec :=
  [
    {
      id := "calibrated_action_scale_reconstruction_protocol",
      experimentId := "calibrated_action_phase_holdout",
      fixtureClass := "calibrated_action_scale_reconstruction",
      claimBoundary := "shared calibrated action scale only; hbar_I remains blocked",
      logicalNodes := [
        "phase_action_conversion_I",
        "no_refit_shared_parameter",
        "hbar_first_principles_boundary"
      ],
      allowedResultStatuses := allowedTelemetryResultStatuses,
      forbiddenUpgrades := requiredForbiddenUpgrades
    },
    {
      id := "finite_readout_normalization_protocol",
      experimentId := "born_context_probability_tests",
      fixtureClass := "finite_readout_normalization",
      claimBoundary := "finite readout normalization check only; not Born proof",
      logicalNodes := [
        "context_normalization",
        "positive_measure_readout"
      ],
      allowedResultStatuses := allowedTelemetryResultStatuses,
      forbiddenUpgrades := requiredForbiddenUpgrades
    },
    {
      id := "bell_chsh_table_protocol",
      experimentId := "bell_chsh_table",
      fixtureClass := "bell_chsh_table",
      claimBoundary := "finite Bell table compatibility only; not Bell derivation",
      logicalNodes := [
        "bell_chsh_no_signalling",
        "bounded_correlation_window"
      ],
      allowedResultStatuses := allowedTelemetryResultStatuses,
      forbiddenUpgrades := requiredForbiddenUpgrades
    }
  ] ++ [
    protocol "two_path_interference" "interference_visibility"
      ["interference_visibility", "context_normalization"]
      "finite two-path interference fixture only; not Born proof",
    protocol "finite_i3_actualization" "sorkin_i3"
      ["sorkin_i3_zero", "context_normalization"]
      "finite third-order interference compatibility only",
    protocol "triple_slit_sorkin_parameter" "sorkin_i3"
      ["sorkin_i3_zero", "context_normalization"]
      "finite triple-slit Sorkin parameter compatibility only",
    protocol "which_way_marker" "marker_eraser_visibility"
      ["path_marker_distinguishability", "interference_visibility"]
      "finite which-way marker visibility fixture only",
    protocol "quantum_eraser" "marker_eraser_visibility"
      ["path_marker_distinguishability", "interference_visibility"]
      "finite eraser visibility fixture only",
    protocol "unitary_measurement_context" "unitary_context_readout"
      ["unitary_context_map", "context_normalization"]
      "finite unitary measurement-context fixture only; apparatus derivation remains open",
    protocol "finite_interferometer_network" "phase_accumulation"
      ["phase_accumulation", "context_normalization"]
      "finite interferometer phase fixture only",
    protocol "projective_repeatability" "projective_repeatability"
      ["projective_repeatability", "positive_measure_readout"]
      "finite projective repeatability fixture only; irreversible collapse dynamics is not derived",
    protocol "bell_chsh_from_amplitudes" "bell_amplitude_table"
      ["amplitude_probability_readout", "bell_chsh_no_signalling", "bounded_correlation_window"]
      "finite amplitude-to-table fixture only; not Born proof",
    protocol "singlet_angle_model" "singlet_angle_grid"
      ["singlet_angle_correlation", "bounded_correlation_window"]
      "finite singlet angle-grid fixture only; spin representation theory is not derived",
    protocol "decoherence_and_recoverability" "decoherence_recoverability"
      ["decoherence_suppression", "recoverability_loss", "positive_measure_readout"]
      "finite decoherence and recoverability fixtures only",
    protocol "stern_gerlach_single_axis" "spin_axis_transition"
      ["spin_axis_transition", "positive_measure_readout"]
      "finite Stern-Gerlach readout fixture only",
    protocol "sequential_stern_gerlach" "spin_axis_transition"
      ["spin_axis_transition", "positive_measure_readout"]
      "finite sequential Stern-Gerlach transition fixture only",
    protocol "delayed_choice" "interference_visibility"
      ["interference_visibility", "phase_accumulation"]
      "finite delayed-choice interference fixture only",
    protocol "aharonov_bohm_phase" "phase_accumulation"
      ["phase_accumulation", "phase_action_conversion_I"]
      "calibrated phase accumulation fixture only",
    protocol "ab_flux_period" "phase_accumulation"
      ["phase_accumulation", "phase_action_conversion_I"]
      "calibrated AB flux-period fixture only",
    protocol "ramsey_interferometry" "phase_accumulation"
      ["phase_accumulation", "phase_action_conversion_I"]
      "calibrated Ramsey phase fixture only",
    protocol "rabi_oscillation" "phase_accumulation"
      ["phase_accumulation", "context_normalization"]
      "finite Rabi oscillation fixture only; not Schrodinger proof",
    protocol "photoelectric_threshold" "calibrated_action_scale_reconstruction"
      ["phase_action_conversion_I", "no_refit_shared_parameter", "hbar_first_principles_boundary"]
      "calibrated energy-frequency fixture only; hbar_I remains blocked",
    protocol "spectroscopy_lines" "calibrated_action_scale_reconstruction"
      ["phase_action_conversion_I", "no_refit_shared_parameter", "hbar_first_principles_boundary"]
      "calibrated spectral transition fixture only; hbar_I remains blocked",
    protocol "tunneling_barrier" "barrier_transmission"
      ["barrier_transmission_suppression", "positive_measure_readout"]
      "finite suppressed-transmission fixture only; exact material barrier dynamics are not claimed",
    protocol "quantum_zeno" "repeated_context_zeno"
      ["repeated_context_survival", "context_normalization"]
      "finite repeated-context Zeno fixture only; continuous measurement model is open",
    protocol "hong_ou_mandel" "bosonic_indistinguishability"
      ["bosonic_coincidence_suppression", "positive_measure_readout"]
      "finite overlap-to-coincidence fixture only; full photonic source/apparatus derivation is not claimed",
    protocol "antibunching_single_photon" "single_quantum_facticity"
      ["single_quantum_coincidence_exclusion", "positive_measure_readout"]
      "finite coincidence-count fixture only; source physics is not derived",
    protocol "entanglement_swapping" "conditional_inheritance_swap"
      ["conditional_inheritance_swap"]
      "finite Bell-outcome correlation transfer fixture only; full source/network derivation is not claimed",
    protocol "quantum_teleportation" "context_transfer_no_cloning"
      ["context_transfer_branch", "no_cloning_obstruction"]
      "finite Bell-branch correction fixture only; full physical teleportation is not claimed",
    protocol "no_cloning" "no_cloning_context_invariance"
      ["no_cloning_obstruction"]
      "finite inner-product obstruction fixture only; no physical cloning machine model is claimed",
    protocol "ghz_mermin_contextuality" "multipartite_contextuality"
      ["contextuality_obstruction"]
      "finite Mermin parity obstruction fixture only; full multipartite apparatus derivation is not claimed",
    protocol "kochen_specker_contextuality" "ks_contextuality_obstruction"
      ["contextuality_obstruction"]
      "finite parity-hypergraph obstruction fixture only; physical projector-set derivation is not claimed",
    protocol "leggett_garg_temporal_context" "temporal_facticity"
      ["temporal_facticity_bound"]
      "finite temporal-correlation fixture only; no macrorealist residual model is claimed",
    protocol "weak_measurement" "partial_facticity_readout"
      ["partial_facticity_readout"]
      "finite weak pointer-shift and partial-facticity fixture only; full apparatus derivation is open",
    protocol "quantum_random_walk" "unitary_graph_walk"
      ["unitary_graph_walk_distribution", "context_normalization"]
      "finite Hadamard graph-walk fixture only; general graph-walk theory is not claimed"
  ]

def jsonEscape (value : String) : String :=
  let escaped := value.replace "\\" "\\\\" |>.replace "\"" "\\\""
  "\"" ++ escaped ++ "\""

def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," (items.map jsonEscape) ++ "]"

def logicalNodeSpecJson (node : LogicalNodeSpec) : String :=
  "{"
    ++ "\"id\":" ++ jsonEscape node.id ++ ","
    ++ "\"label\":" ++ jsonEscape node.label ++ ","
    ++ "\"claim_boundary\":" ++ jsonEscape node.claimBoundary
    ++ "}"

def protocolSpecJson (protocol : ExperimentProtocolSpec) : String :=
  "{"
    ++ "\"id\":" ++ jsonEscape protocol.id ++ ","
    ++ "\"experiment_id\":" ++ jsonEscape protocol.experimentId ++ ","
    ++ "\"fixture_class\":" ++ jsonEscape protocol.fixtureClass ++ ","
    ++ "\"claim_boundary\":" ++ jsonEscape protocol.claimBoundary ++ ","
    ++ "\"logical_nodes\":" ++ jsonArray protocol.logicalNodes ++ ","
    ++ "\"allowed_result_statuses\":" ++ jsonArray protocol.allowedResultStatuses ++ ","
    ++ "\"forbidden_upgrades\":" ++ jsonArray protocol.forbiddenUpgrades
    ++ "}"

def registryJson : String :=
  "{"
    ++ "\"schema\":\"idt-v8-experiment-protocol-registry/1\","
    ++ "\"protocol_authority\":\"lean_checked_protocol\","
    ++ "\"result_boundary\":\"certified_executable_check\","
    ++ "\"proof_boundary\":\"experiment_results_are_not_formal_proofs\","
    ++ "\"logical_nodes\":["
    ++ String.intercalate "," (logicalNodeSpecs.map logicalNodeSpecJson)
    ++ "],"
    ++ "\"protocols\":["
    ++ String.intercalate "," (experimentProtocolSpecs.map protocolSpecJson)
    ++ "]}"

theorem registry_keeps_experiment_formal_proof_boundary :
    ¬ v8LeanExperimentProtocolTarget.canAssignPhysicalFormalProof :=
  certified_executable_experiment_cannot_assign_physical_formal_proof

def main (args : List String) : IO Unit := do
  if args.contains "--json" then
    IO.println registryJson
  else
    IO.println "IDT v8 experiment protocol registry: use --json"

end V8
end Experiments
end IDT

def main (args : List String) : IO Unit :=
  IDT.Experiments.V8.main args
