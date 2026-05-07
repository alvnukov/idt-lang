import Proofs.MetaLang.V8CurrentStopReadiness

open IDT.MetaLang.V8

def protocolStatusText : String :=
  String.intercalate "\n" [
    "IDT v8 Lean experiment protocol status",
    "protocol_logic_authority=lean_checked",
    "result_status=certified_executable_check",
    "proof_authority=declarative_input_check",
    s!"residual_qm_experiments={currentExperimentProgramArchitecture.residualLedger.length}",
    "residuals_need_idt_v8_classification=true",
    "can_assign_physical_formal_proof=false",
    "ready_for_research_handoff=false",
    "ready_for_migration_stop=false"
  ]

def boundaryCheckPassed : Bool :=
  currentExperimentProgramArchitecture.residualLedger.length == 35

def main (args : List String) : IO Unit := do
  if args.contains "--check-boundary" then
    if boundaryCheckPassed then
      IO.println "boundary_check=ok"
    else
      throw <| IO.userError "boundary_check=failed"
  else if args.contains "--json" then
    let residualCount :=
      toString currentExperimentProgramArchitecture.residualLedger.length
    IO.println (
      "{\"protocol_logic_authority\":\"lean_checked\","
      ++ "\"result_status\":\"certified_executable_check\","
      ++ "\"proof_authority\":\"declarative_input_check\","
      ++ "\"residual_qm_experiments\":" ++ residualCount ++ ","
      ++ "\"residuals_need_idt_v8_classification\":true,"
      ++ "\"can_assign_physical_formal_proof\":false,"
      ++ "\"ready_for_research_handoff\":false,"
      ++ "\"ready_for_migration_stop\":false}"
    )
  else
    IO.println protocolStatusText
