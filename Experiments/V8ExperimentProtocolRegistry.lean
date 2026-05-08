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
    }
  ]

def experimentProtocolSpecs : List ExperimentProtocolSpec :=
  [
    {
      id := "calibrated_action_scale_reconstruction_protocol",
      experimentId := "calibrated_action_scale_reconstruction_demo",
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
